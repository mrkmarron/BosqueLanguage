//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { sanitizeForCpp, NOT_IMPLEMENTED } from "./cpputils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable } from "../../compiler/mir_ops";
import * as assert from "assert";

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;

    readonly allConstStrings: Map<string, string> = new Map<string, string>();

    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
    }

    getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return vtypes.get(arg.nameID) as MIRType;
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

    generateConstantExp(cval: MIRConstantArgument): string {
        if (cval instanceof MIRConstantNone) {
            return "nullptr";
        }
        else if (cval instanceof MIRConstantTrue) {
            return "true";
        }
        else if (cval instanceof MIRConstantFalse) {
            return "false";
        }
        else if (cval instanceof MIRConstantInt) {
            return cval.value;
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

    generateTruthyConvert(arg: MIRArgument, vtypes: Map<string, MIRType>): string {
        const argtype = this.getArgType(arg, vtypes);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return "false";
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToCppCoerce(arg, argtype, this.typegen.boolType);
        }
        else {
            const argv = this.varToCppName(arg);
            return `(${argv} !== RuntimeValueEnvironment::none && dynamic_cast<BSQ::BoxedBool>(${argv})->unbox())`;
        }
    }

    generateStmt(op: MIROp, vtypes: Map<string, MIRType>): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                return `${this.varToCppName(lcv.trgt)} = ${this.generateConstantExp(lcv.src)};`;
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
                return `${this.varToCppName(lav.trgt)} = ${this.argToCppDirect(lav.name)};`;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                return `${this.varToCppName(llv.trgt)} = ${this.argToCppDirect(llv.name)};`;
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
                return `${this.varToCppName(invk.trgt)} = ${this.generateMIRInvokeFixedFunction(invk, vtypes)};`;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const argtype = this.getArgType(pfx.arg, vtypes);
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg, vtypes);
                    return `${this.varToCppName(pfx.trgt)} = !${tval};`;
                }
                else {
                    if (pfx.op === "-") {
                        return `${this.varToCppName(pfx.trgt)} = -${this.argToCppCoerce(pfx.arg, argtype, this.typegen.intType)};`;
                    }
                    else {
                        return `${this.varToCppName(pfx.trgt)} = ${this.argToCppCoerce(pfx.arg, argtype, this.typegen.intType)};`;
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;

                const trgt = this.varToCppName(bop.trgt);
                const lhv = this.argToCppCoerce(bop.lhs, this.getArgType(bop.lhs, vtypes), this.typegen.intType);
                const rhv = this.argToCppCoerce(bop.rhs, this.getArgType(bop.rhs, vtypes), this.typegen.intType);

                return `${trgt} = ${lhv} ${bop.op} ${rhv};`;
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs, vtypes);
                const rhvtype = this.getArgType(beq.rhs, vtypes);
                if (this.typegen.isTypeExact(lhvtype) && this.typegen.isTypeExact(rhvtype)) {
                    if ((lhvtype.trkey === "NSCore::None" && rhvtype.trkey === "NSCore::None")
                        || (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool")
                        || (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int")
                        || (lhvtype.trkey === "NSCore::String" && rhvtype.trkey === "NSCore::String")) {
                            return `${this.argToCppDirect(beq.lhs)} = ${this.argToCppDirect(beq.lhs)} ${beq.op} ${this.argToCppDirect(beq.rhs)};`;
                    }
                    else {
                        return NOT_IMPLEMENTED<string>("BINEQ -- nonprimitive values");
                    }
                }
                else {
                    const larg = this.argToCppCoerce(beq.lhs, lhvtype, this.typegen.anyType);
                    const rarg = this.argToCppCoerce(beq.rhs, rhvtype, this.typegen.anyType);

                    let tops: string[] = [];
                    if (this.assembly.subtypeOf(this.typegen.noneType, lhvtype) && this.assembly.subtypeOf(this.typegen.noneType, lhvtype)) {
                        tops.push(`((${larg} == RuntimeValueEnvironment.none) && (${rarg} == RuntimeValueEnvironment.none))`);
                    }

                    if (this.assembly.subtypeOf(this.typegen.boolType, lhvtype) && this.assembly.subtypeOf(this.typegen.boolType, lhvtype)) {
                        tops.push(`((dynamic_cast<BoxedBool>${larg} != nullptr) && (dynamic_cast<BoxedBool>${rarg} != nullptr) && (BSQ::BoxedBool::unbox(${larg} == BSQ::BoxedBool::unbox(${rarg}))`);
                    }

                    if (this.assembly.subtypeOf(this.typegen.intType, lhvtype) && this.assembly.subtypeOf(this.typegen.intType, lhvtype)) {
                        tops.push(`((dynamic_cast<BoxedInt>${larg} != nullptr) && (dynamic_cast<BoxedInt>${rarg} != nullptr) && (BSQ::BoxedInt::unbox(${larg} == BSQ::BoxedInt::unbox(${rarg}))`);
                    }

                    if (this.assembly.subtypeOf(this.typegen.stringType, lhvtype) && this.assembly.subtypeOf(this.typegen.stringType, lhvtype)) {
                        tops.push(`((dynamic_cast<BoxedString>${larg} != nullptr) && (dynamic_cast<BoxedString>${rarg} != nullptr) && (*BSQ::BoxedString::unbox(${larg} == *BSQ::BoxedString::unbox(${rarg}))`);
                    }

                    //
                    //TODO: handle the other types here
                    //

                    const test = tops.length === 1 ? tops[0] : `(${tops.join(" || ")})`;

                    return `${this.argToCppDirect(beq.lhs)} = ${beq.op === "!=" ? `!${test}` : test};`;
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs, vtypes);
                const rhvtype = this.getArgType(bcmp.rhs, vtypes);

                if (this.typegen.isTypeExact(lhvtype) && this.typegen.isTypeExact(rhvtype)) {
                    return `${this.varToCppName(bcmp.trgt)} = ${this.argToCppDirect(bcmp.lhs)} ` + bcmp.op + ` ${this.argToCppDirect(bcmp.rhs)};`;
                }
                else {
                    const trgttype = (this.assembly.subtypeOf(this.typegen.intType, lhvtype) && this.assembly.subtypeOf(this.typegen.intType, rhvtype)) ? this.typegen.intType : this.typegen.stringType;

                    return `${this.varToCppName(bcmp.trgt)} = ${this.argToCppCoerce(bcmp.lhs, lhvtype, trgttype)} ` + bcmp.op + ` ${this.argToCppCoerce(bcmp.rhs, rhvtype, trgttype)};`;
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;

                const argtype = this.getArgType(ton.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return `${this.varToCppName(ton.trgt)} = ${this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "true" : "false"};`;
                }
                else {
                    return `${this.varToCppName(ton.trgt)} = ${this.argToCppDirect(ton.arg)} == RuntimeValueEnvironment.none;`;
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;

                const argtype = this.getArgType(tos.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return `${this.varToCppName(tos.trgt)} = ${this.assembly.subtypeOf(argtype, this.typegen.noneType) ? "false" : "true"};`;
                }
                else {
                    return `${this.varToCppName(tos.trgt)} = ${this.argToCppDirect(tos.arg)} != RuntimeValueEnvironment.none;`;
                }
           }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<string>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;

                return `${this.varToCppName(regop.trgt)} = ${this.argToCppDirect(regop.src)};`;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;

                const smttest = this.generateTruthyConvert(tcop.src, vtypes);
                return `${this.varToCppName(tcop.trgt)} = ${smttest};`;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToCppCoerce(llop.lhs, lhvtype, this.typegen.boolType);

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToCppCoerce(llop.rhs, rhvtype, this.typegen.boolType);

                return `${this.varToCppName(llop.trgt)} = (${lhv} ${llop.op} ${rhv});`;
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;

                return `${this.varToCppName(vsop.name)} = ${this.argToCppDirect(vsop.src)};`;
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;

                const totype = vtypes.get(raop.name.nameID) as MIRType;
                const fromtype = this.getArgType(raop.src, vtypes);
                return `${this.varToCppName(raop.name)} = ${this.argToCppCoerce(raop.src, fromtype, totype)};`;
            }
            case MIROpTag.MIRAbort: {
                return "throw MIRAbort{};";
            }
            case MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op as MIRDebug;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    const argv = this.getArgType(dbgop.value, vtypes);
                    return `cout << BSQ::ValueOps::diagnostic_format(${this.argToCppCoerce(dbgop.value, argv, this.typegen.anyType)}) << \n;`;
                }
            }
            case MIROpTag.MIRJump: {
                const jop = op as MIRJump;
                return `goto ${this.labelToCpp(jop.trgtblock)};`;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const smttest = this.generateTruthyConvert(cjop.arg, vtypes);
                return `if(${smttest}) {goto ${this.labelToCpp(cjop.trueblock)};} else {goto ${cjop.falseblock};}`;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const argtype = this.getArgType(njop.arg, vtypes);
                if (this.typegen.isTypeExact(argtype)) {
                    return this.assembly.subtypeOf(argtype, this.typegen.noneType) ? `goto ${this.labelToCpp(njop.noneblock)};` : `goto ${this.labelToCpp(njop.someblock)};`;
                }
                else {
                    return `if(${this.argToCppDirect(njop.arg)} == RuntimeValueEnvironment.none) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
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
