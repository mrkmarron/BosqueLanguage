//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRTypeOption, MIRInvokeDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { NOT_IMPLEMENTED, isInlinableType, getInlinableType, sanitizeForSMT } from "./smtutils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort } from "../../compiler/mir_ops";
import * as assert from "assert";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smtexp";
import { SourceInfo } from "../../ast/parser";

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;

    private errorCodes = new Map<string, number>();
    private bmcCodes = new Map<string, number>();
    private bmcDepths = new Map<string, number>();

    private tmpvarctr = 0;
    private currentRType: MIRType;
    private currentFile: string = "[No File]";

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.currentRType = typegen.noneType;
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo): SMTValue {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo) as number;

        return new SMTValue(`(result_error_${this.typegen.getSMTType(this.currentRType)}, (result_error ${errid}))`);
    }

    getArgType(arg: MIRArgument): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return this.vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }

    varNameToSMTName(name: string): string {
        return sanitizeForSMT(name);
    }

    varToSMTName(varg: MIRRegisterArgument): string {
        return sanitizeForSMT(varg.nameID);
    }

    constNameToSMTName(cname: string): string {
        return sanitizeForSMT(cname);
    }

    invokenameToSMTName(invk: string): string {
        return sanitizeForSMT(invk);
    }

    boxIfNeeded(exp: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        if (!isInlinableType(from) || isInlinableType(into)) {
            return exp;
        }

        const itype = getInlinableType(from);
        if (itype.trkey === "NSCore::Bool") {
            return new SMTValue(`(bsq_term_bool ${exp.emit()})`);
        }
        else {
            return new SMTValue(`(bsq_term_int ${exp.emit()})`);
        }
    }

    unboxIfNeeded(exp: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        if (isInlinableType(from) || !isInlinableType(into)) {
            return exp;
        }

        const itype = getInlinableType(into);
        if (itype.trkey === "NSCore::Bool") {
            return new SMTValue(`(bsq_term_bool_value ${exp.emit()})`);
        }
        else {
            return new SMTValue(`(bsq_term_int_value ${exp.emit()})`);
        }
    }

    coerce(exp: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        if (isInlinableType(from) === isInlinableType(into)) {
            return exp;
        }

        return isInlinableType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType | MIRTypeOption): SMTExp {
        const isinlineable = isInlinableType(into);

        if (cval instanceof MIRConstantNone) {
            return new SMTValue("bsq_term_none");
        }
        else if (cval instanceof MIRConstantTrue) {
            return new SMTValue(isinlineable ? "true" : "(bsq_term_bool_value true)");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new SMTValue(isinlineable ? "false" : "(bsq_term_bool_value false)");
        }
        else if (cval instanceof MIRConstantInt) {
            return new SMTValue(isinlineable ? cval.value : `(bsq_term_int_value ${cval.value})`);
        }
        else {
            assert(cval instanceof MIRConstantString);

            return new SMTValue((cval as MIRConstantString).value);
        }
    }

    argToSMT(arg: MIRArgument, into: MIRType | MIRTypeOption): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.coerce(new SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument, into);
        }
    }

    generateTruthyConvert(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT(arg, this.typegen.boolType);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsq_term_true_const)`);
        }
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        let coreop = "";
        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.boolType)} ${op} ${this.argToSMT(rhs, this.typegen.boolType)}`;
        }
        else {
            coreop = `${this.argToSMT(lhs, this.typegen.intType)} ${op} ${this.argToSMT(rhs, this.typegen.intType)}`;
        }

        return op === "!=" ? `(not ${coreop})` : coreop;
    }

    generateStmt(op: MIROp, vtypes: Map<string, MIRType>): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<SMTExp>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                return NOT_IMPLEMENTED<SMTExp>("MIRAccessConstantValue");
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                return NOT_IMPLEMENTED<SMTExp>("MIRLoadFieldDefaultValue");
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                return new SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                return new SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case MIROpTag.MIRConstructorPrimary: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimary");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionEmpty");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionSingletons");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorTuple");
            }
            case MIROpTag.MIRConstructorRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorRecord");
            }
            case MIROpTag.MIRAccessFromIndex: {
                return NOT_IMPLEMENTED<SMTExp>("MIRAccessFromIndex");
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                return NOT_IMPLEMENTED<SMTExp>("MIRAccessFromProperty");
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                return NOT_IMPLEMENTED<SMTExp>("MIRAccessFromField");
            }
            case MIROpTag.MIRProjectFromFields: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromFields");
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromTypeConcept");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRModifyWithIndecies");
            }
            case MIROpTag.MIRModifyWithProperties: {
                return NOT_IMPLEMENTED<SMTExp>("MIRModifyWithProperties");
            }
            case MIROpTag.MIRModifyWithFields: {
                return NOT_IMPLEMENTED<SMTExp>("MIRModifyWithFields");
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendTuple");
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendRecord");
            }
            case MIROpTag.MIRStructuredExtendObject: {
                return NOT_IMPLEMENTED<SMTExp>("MIRStructuredExtendObject");
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return new SMTLet(this.varToSMTName(invk.trgt), this.generateMIRInvokeFixedFunction(invk));
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(not ${tval.emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                    }
                    else {
                        return new SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.typegen.intType));
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;

                const restmp = this.generateTempName();
                let smtconds = [`(< ${restmp} BINT_MIN)`, `(< BINT_MAX ${restmp})`];
                if (bop.op === "/" || bop.op === "%") {
                    smtconds.push(`(= ${restmp} 0)`);
                }
                const ite = new SMTCond(new SMTValue(`(or ${smtconds.join(" ")})`), this.generateErrorCreate(op.sinfo), SMTFreeVar.generate());

                return new SMTLet(restmp, new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType)} ${this.argToSMT(bop.rhs, this.typegen.intType)})`), ite);
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateFastEquals(beq.op, beq.lhs, beq.rhs)));
                }
                else {
                    const larg = this.argToSMT(beq.lhs, this.typegen.anyType);
                    const rarg = this.argToSMT(beq.rhs, this.typegen.anyType);

                    const sloweq = `(@equality_op ${larg.emit()} ${rarg.emit()})`;
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${sloweq})` : sloweq));
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return `${this.varToCppName(bcmp.trgt)} = ${this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(bcmp.lhs, this.typegen.anyType);
                    const rarg = this.argToCpp(bcmp.rhs, this.typegen.anyType);

                    if (bcmp.op === "<") {
                        return `${this.varToCppName(bcmp.trgt)} = Value::compare_op(${larg}, ${rarg});`;
                    }
                    else if (bcmp.op === ">") {
                        return `${this.varToCppName(bcmp.trgt)} = Value::compare_op(${rarg}, ${larg});`;
                    }
                    else if (bcmp.op === "<=") {
                        return `${this.varToCppName(bcmp.trgt)} = Value::compare_op(${larg}, ${rarg}) || Value::equality_op(${larg}, ${rarg});`;
                    }
                    else {
                        return `${this.varToCppName(bcmp.trgt)} = Value::compare_op(${rarg}, ${larg}) || Value::equality_op(${larg}, ${rarg});`;
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;

                const argtype = this.getArgType(ton.arg);
                if (isInlinableType(argtype)) {
                    return `${this.varToCppName(ton.trgt)} = ${this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "true" : "false"};`;
                }
                else {
                    return `${this.varToCppName(ton.trgt)} = ${this.varToCppName(ton.arg)}.isNone();`;
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;

                const argtype = this.getArgType(tos.arg);
                if (isInlinableType(argtype)) {
                    return `${this.varToCppName(tos.trgt)} = ${this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "false" : "true"};`;
                }
                else {
                    return `${this.varToCppName(tos.trgt)} = !(${this.varToCppName(tos.arg)}.isNone());`;
                }
           }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<SMTExp>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return `${this.varToCppName(regop.trgt)} = ${this.argToCpp(regop.src, this.getArgType(regop.trgt))};`;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return `${this.varToCppName(tcop.trgt)} = ${this.generateTruthyConvert(tcop.src)};`;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                return `${this.varToCppName(llop.trgt)} = (${this.argToCpp(llop.lhs, this.typegen.boolType)} ${llop.op} ${this.argToCpp(llop.rhs, this.typegen.boolType)});`;
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return `${this.varToCppName(vsop.name)} = ${this.argToCpp(vsop.src, this.getArgType(vsop.name))};`;
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return `${this.varToCppName(raop.name)} = ${this.argToCpp(raop.src, this.getArgType(raop.name))};`;
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return `BSQ_ABORT("${aop.info}", "[TODO: filename]", ${aop.sinfo.line});`;
            }
            case MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op as MIRDebug;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    return `cout << Value::diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}) << \n;`;
                }
            }
            case MIROpTag.MIRJump: {
                const jop = op as MIRJump;
                return `goto ${this.labelToCpp(jop.trgtblock)};`;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                return `if(${this.generateTruthyConvert(cjop.arg)}) {goto ${this.labelToCpp(cjop.trueblock)};} else {goto ${cjop.falseblock};}`;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const argtype = this.getArgType(njop.arg);
                if (isInlinableType(argtype)) {
                    return this.assembly.subtypeOf(argtype, this.typegen.noneType) ? `goto ${this.labelToCpp(njop.noneblock)};` : `goto ${this.labelToCpp(njop.someblock)};`;
                }
                else {
                    return `if(${this.argToCpp(njop.arg, this.typegen.anyType)}.isNone()) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
                }
            }
            case MIROpTag.MIRPhi: {
                return undefined; //handle this as a special case in the block processing code
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED<SMTExp>(`Missing case ${op.tag}`);
            }
        }
    }
}

export {
    SMTBodyEmitter
};
