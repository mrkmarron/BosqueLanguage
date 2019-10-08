//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRTypeOption, MIRInvokeDecl } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { sanitizeForCpp, NOT_IMPLEMENTED, isInlinableType, getInlinableType } from "./cpputils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort } from "../../compiler/mir_ops";
import * as assert from "assert";

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;

    readonly allConstStrings: Map<string, string> = new Map<string, string>();

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
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

    labelToCpp(label: string): string {
        return sanitizeForCpp(label);
    }

    varNameToCppName(name: string): string {
        return sanitizeForCpp(name);
    }

    varToCppName(varg: MIRRegisterArgument): string {
        return sanitizeForCpp(varg.nameID);
    }

    constNameToCppName(cname: string): string {
        return sanitizeForCpp(cname);
    }

    invokenameToCppName(invk: string): string {
        return sanitizeForCpp(invk);
    }

    boxIfNeeded(exp: string, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        if (!isInlinableType(from) || isInlinableType(into)) {
            return exp;
        }

        const itype = getInlinableType(from);
        if (itype.trkey === "NSCore::None") {
            return "Value::noneValue()";
        }
        else if (itype.trkey === "NSCore::Bool") {
            return `Value(${exp})`;
        }
        else {
            return `Value(${exp})`;
        }
    }

    unboxIfNeeded(exp: string, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        if (isInlinableType(from) || !isInlinableType(into)) {
            return exp;
        }

        const itype = getInlinableType(into);
        if (itype.trkey === "NSCore::None") {
            return "nullptr";
        }
        else if (itype.trkey === "NSCore::Bool") {
            return `(${exp}).getBool()`;
        }
        else {
            return `(${exp}).getInt()`;
        }
    }

    coerce(exp: string, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        if (isInlinableType(from) === isInlinableType(into)) {
            return exp;
        }

        return isInlinableType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType | MIRTypeOption): string {
        const isinlineable = isInlinableType(into);

        if (cval instanceof MIRConstantNone) {
            return isinlineable ? "nullptr" : "Value::noneValue()";
        }
        else if (cval instanceof MIRConstantTrue) {
            return isinlineable ? "true" : "Value::trueValue()";
        }
        else if (cval instanceof MIRConstantFalse) {
            return isinlineable ? "false" : "Value::falseValue()";
        }
        else if (cval instanceof MIRConstantInt) {
            return isinlineable ? cval.value : (cval.value === "0" ? "Value::zeroValue()" : `Value(${cval.value})`);
        }
        else {
            assert(cval instanceof MIRConstantString);

            const sval = (cval as MIRConstantString).value;
            const sname = "str$" + sanitizeForCpp(sval);
            if (!this.allConstStrings.has(sname)) {
                this.allConstStrings.set(sname, sval);
            }

            return `Runtime::BSQ_STRING_${sname}`;
        }
    }

    argToCpp(arg: MIRArgument, into: MIRType | MIRTypeOption): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.coerce(this.varToCppName(arg), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument, into);
        }
    }

    generateTruthyConvert(arg: MIRArgument): string {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "false";
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToCpp(arg, this.typegen.boolType);
        }
        else {
            return `(${this.varToCppName(arg)}).getTruthy()`;
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): string {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCpp(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType));
        }

        return `${this.invokenameToCppName(ivop.mkey)}(${vals.join(", ")})`;
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)}`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
            return `${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)}`;
        }
        else {
            assert(lhvtype.trkey === "NSCore::None" || rhvtype.trkey === "NSCore::None");
            return op === "!=" ? "false" : "true";
        }
    }

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        return `${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)}`;
    }

    generateStmt(op: MIROp, vtypes: Map<string, MIRType>): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                return `${this.varToCppName(lcv.trgt)} = ${this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt))};`;
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<string>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                return NOT_IMPLEMENTED<string>("MIRAccessConstantValue");
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                return NOT_IMPLEMENTED<string>("MIRLoadFieldDefaultValue");
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                return `${this.varToCppName(lav.trgt)} = ${this.argToCpp(lav.name, this.getArgType(lav.trgt))};`;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                return `${this.varToCppName(llv.trgt)} = ${this.argToCpp(llv.name, this.getArgType(llv.trgt))};`;
            }
            case MIROpTag.MIRConstructorPrimary: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimary");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionEmpty");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionSingletons");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<string>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                return NOT_IMPLEMENTED<string>("MIRConstructorTuple");
            }
            case MIROpTag.MIRConstructorRecord: {
                return NOT_IMPLEMENTED<string>("MIRConstructorRecord");
            }
            case MIROpTag.MIRAccessFromIndex: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromIndex");
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromProperty");
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                return NOT_IMPLEMENTED<string>("MIRAccessFromField");
            }
            case MIROpTag.MIRProjectFromFields: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromFields");
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeTuple");
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeRecord");
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromTypeConcept");
            }
            case MIROpTag.MIRModifyWithIndecies: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithIndecies");
            }
            case MIROpTag.MIRModifyWithProperties: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithProperties");
            }
            case MIROpTag.MIRModifyWithFields: {
                return NOT_IMPLEMENTED<string>("MIRModifyWithFields");
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendTuple");
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendRecord");
            }
            case MIROpTag.MIRStructuredExtendObject: {
                return NOT_IMPLEMENTED<string>("MIRStructuredExtendObject");
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                return `${this.varToCppName(invk.trgt)} = ${this.generateMIRInvokeFixedFunction(invk)};`;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return `${this.varToCppName(pfx.trgt)} = !${tval};`;
                }
                else {
                    if (pfx.op === "-") {
                        return `${this.varToCppName(pfx.trgt)} = -${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCpp(pfx.arg, this.typegen.intType)};`;
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                return `${this.varToCppName(bop.trgt)} = ${this.argToCpp(bop.lhs, this.typegen.intType)} ${bop.op} ${this.argToCpp(bop.rhs, this.typegen.intType)};`;
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return `${this.varToCppName(beq.trgt)} = ${this.generateFastEquals(beq.op, beq.lhs, beq.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(beq.lhs, this.typegen.anyType);
                    const rarg = this.argToCpp(beq.rhs, this.typegen.anyType);

                    return `${this.varToCppName(beq.trgt)} = ${beq.op === "!=" ? "!" : ""}Value::equality_op(${larg}, ${rarg});`;
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
                return NOT_IMPLEMENTED<string>("MIRIsTypeOf");
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
                return NOT_IMPLEMENTED<string>(`Missing case ${op.tag}`);
            }
        }
    }
}

export {
    CPPBodyEmitter
};
