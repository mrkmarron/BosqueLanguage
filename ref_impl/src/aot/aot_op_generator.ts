//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantTrue, MIRConstantFalse, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIRAccessArgVariable, MIRAccessLocalVariable, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRJump, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRAbort, MIRJumpCond, MIRJumpNone, MIRPhi, MIRDebug, MIRInvokeFixedFunction, MIRBasicBlock } from "../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTypeOption, MIREntityType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIRInvokeDecl } from "../compiler/mir_assembly";
import { AOTTypeGenerator } from "./aot_type_generator";
import { sanitizeForCpp, NOT_IMPLEMENTED } from "./utils";

class AOTCodeGenerator {
    readonly assembly: MIRAssembly;
    readonly typegen: AOTTypeGenerator;

    readonly allConstStrings: string[] = [];

    private cinvokeResult: MIRType;

    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();
    private allVTypes: Map<string, Map<string, MIRType>> = new Map<string, Map<string, MIRType>>();

    constructor(assembly: MIRAssembly, typegen: AOTTypeGenerator) {
        this.assembly = assembly;
        this.typegen = typegen;

        this.cinvokeResult = this.typegen.noneType;
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

    literalStringToCppName(str: string): string {
        return sanitizeForCpp(str);
    }

    labelToCpp(label: string): string {
        return sanitizeForCpp(label);
    }

    varToCppName(varg: MIRRegisterArgument): string {
        return sanitizeForCpp(varg.nameID);
    }

    invokenameToCppName(invk: string): string {
        return sanitizeForCpp(invk);
    }

    generateConstantExp(cval: MIRConstantArgument): string {
        if (cval instanceof MIRConstantNone) {
            return "RuntimeValueEnvironment.none";
        }
        else if (cval instanceof MIRConstantTrue) {
            return "true";
        }
        else if (cval instanceof MIRConstantFalse) {
            return "false";
        }
        else if (cval instanceof MIRConstantInt) {
            return cval.value.slice(1, cval.value.length - 2);
        }
        else {
            assert(cval instanceof MIRConstantString);

            return (cval as MIRConstantString).value;
        }
    }

    argToCppDirect(arg: MIRArgument): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.varToCppName(arg);
        }
        else {
            return this.generateConstantExp(arg as MIRConstantArgument);
        }
    }

    coerceBoxIfNeeded(arg: string, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        assert(!this.typegen.isTypeExact(into));

        if (!this.typegen.isTypeExact(from)) {
            return arg;
        }
        else {
            const fromtype = AOTTypeGenerator.getExactTypeFrom(from);
            if (fromtype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(fromtype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return `(${arg} ? RuntimeValueEnvironment.boxedTrue : RuntimeValueEnvironment.boxedFalse)`;
                    }
                    if (typedecl.name === "Int") {
                        return `BSQ::BoxedInt::box(${arg})`;
                    }
                    if (typedecl.name === "String") {
                        return `BSQ::BoxedString::box(${arg})`;
                    }
                    if (typedecl.name === "Float") {
                        return `BSQ::BoxedFloat::box(${arg})`;
                    }
                }

                return NOT_IMPLEMENTED<string>("coerceBoxIfNeeded -- entity");
            }
            else if (fromtype instanceof MIRTupleType) {
                return NOT_IMPLEMENTED<string>("coerceBoxIfNeeded -- tuple");
            }
            else {
                assert(fromtype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<string>("coerceBoxIfNeeded -- record");
            }
        }
    }

    coerceUnBoxIfNeeded(arg: string, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        assert(this.typegen.isTypeExact(into));

        if (this.typegen.isTypeExact(from)) {
            return arg;
        }
        else {
            const intotype = AOTTypeGenerator.getExactTypeFrom(into);
            if (intotype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(intotype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return `dynamic_cast<BSQ::BoxedBool>(${arg})->unbox()`;
                    }
                    if (typedecl.name === "Int") {
                        return`dynamic_cast<BSQ::BoxedInt>(${arg})->unbox()`;
                    }
                    if (typedecl.name === "String") {
                        return `dynamic_cast<BSQ::BoxedString>(${arg})->unbox()`;
                    }
                    if (typedecl.name === "Float") {
                        return `dynamic_cast<BSQ::BoxedFloat>(${arg})->unbox()`;
                    }
                }

                return NOT_IMPLEMENTED<string>("coerceUnBoxIfNeeded -- entity");
            }
            else if (intotype instanceof MIRTupleType) {
                return NOT_IMPLEMENTED<string>("coerceUnBoxIfNeeded -- tuple");
            }
            else {
                assert(intotype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<string>("coerceUnBoxIfNeeded -- record");
            }
        }
    }

    argToCppCoerce(arg: MIRArgument, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): string {
        if (arg instanceof MIRRegisterArgument) {
            const rval = this.varToCppName(arg);
            if (this.typegen.isTypeExact(into)) {
                return this.coerceUnBoxIfNeeded(rval, from, into);
            }
            else {
                return this.coerceBoxIfNeeded(rval, from, into);
            }
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return "RuntimeValueEnvironment.none";
            }
            else if (arg instanceof MIRConstantTrue) {
                return this.typegen.isTypeExact(into) ? "true" : "RuntimeValueEnvironment.boxedTrue";
            }
            else if (arg instanceof MIRConstantFalse) {
                return this.typegen.isTypeExact(into) ? "false" : "RuntimeValueEnvironment.boxedFalse";
            }
            else if (arg instanceof MIRConstantInt) {
                return this.typegen.isTypeExact(into) ? arg.value : `BSQ::BoxedInt::box(${arg.value})`;
            }
            else {
                const strv = (arg as MIRConstantString).value;

                return this.typegen.isTypeExact(into) ? `RuntimeValueEnvironment.${this.allConstStrings.indexOf(strv)}` : `BSQ::BoxedInt::box(RuntimeValueEnvironment.${this.allConstStrings.indexOf(strv)})`;
            }
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

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, vtypes: Map<string, MIRType>): string {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCppCoerce(ivop.args[i], this.getArgType(ivop.args[i], vtypes), this.assembly.typeMap.get(idecl.params[i].type) as MIRType));
        }

        return `${this.invokenameToCppName(ivop.mkey)}(${vals.join(", ")})`;
    }

    generateStmt(op: MIROp, vtypes: Map<string, MIRType>): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                vtypes.set(lcv.trgt.nameID, this.getArgType(lcv.src, vtypes));
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
                vtypes.set(lav.trgt.nameID, this.getArgType(lav.name, vtypes));
                return `${this.varToCppName(lav.trgt)} = ${this.argToCppDirect(lav.name)};`;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                vtypes.set(llv.trgt.nameID, this.getArgType(llv.name, vtypes));
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
                vtypes.set(invk.trgt.nameID, this.assembly.typeMap.get(((this.assembly.invokeDecls.get(invk.mkey) || this.assembly.primitiveInvokeDecls.get(invk.mkey)) as MIRInvokeDecl).resultType) as MIRType);
                return this.generateMIRInvokeFixedFunction(invk, vtypes);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<string>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const argtype = this.getArgType(pfx.arg, vtypes);
                if (pfx.op === "!") {
                    vtypes.set(pfx.trgt.nameID, this.typegen.boolType);

                    const tval = this.generateTruthyConvert(pfx.arg, vtypes);
                    return `${this.varToCppName(pfx.trgt)} = !${tval};`;
                }
                else {
                    vtypes.set(pfx.trgt.nameID, this.typegen.intType);

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
                vtypes.set(bop.trgt.nameID, this.typegen.intType);

                const trgt = this.varToCppName(bop.trgt);
                const lhv = this.argToCppCoerce(bop.lhs, this.getArgType(bop.lhs, vtypes), this.typegen.intType);
                const rhv = this.argToCppCoerce(bop.rhs, this.getArgType(bop.rhs, vtypes), this.typegen.intType);

                return `${trgt} = ${lhv} ${bop.op} ${rhv};`;
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;
                vtypes.set(beq.trgt.nameID, this.typegen.boolType);

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
                vtypes.set(bcmp.trgt.nameID, this.typegen.boolType);

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
                vtypes.set(ton.trgt.nameID, this.typegen.boolType);

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
                vtypes.set(tos.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);

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
                vtypes.set(regop.trgt.nameID, this.getArgType(regop.src, vtypes));

                return `${this.varToCppName(regop.trgt)} = ${this.argToCppDirect(regop.src)};`;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                vtypes.set(tcop.trgt.nameID, this.typegen.boolType);

                const smttest = this.generateTruthyConvert(tcop.src, vtypes);
                return `${this.varToCppName(tcop.trgt)} = ${smttest};`;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                vtypes.set(llop.trgt.nameID, this.typegen.boolType);

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToCppCoerce(llop.lhs, lhvtype, this.typegen.boolType);

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToCppCoerce(llop.rhs, rhvtype, this.typegen.boolType);

                return `${this.varToCppName(llop.trgt)} = (${lhv} ${llop.op} ${rhv});`;
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                vtypes.set(vsop.name.nameID, this.getArgType(vsop.src, vtypes));

                return `${this.varToCppName(vsop.name)} = ${this.argToCppDirect(vsop.src)};`;
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                vtypes.set(raop.name.nameID, this.cinvokeResult as MIRType);

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

    generateSingleBlocks(block: MIRBasicBlock) {
        let gblock: string[] = [];

        let blocki = 0;
        /*
        while (blocki < block.ops.length - 1 && block.ops[blocki] instanceof MIRPhi) {
            const phiop = block.ops[blocki] as MIRPhi;
            const vtypes = ;
        }
        */

        while (blocki < block.ops.length) {
            const gop = this.generateStmt(block.ops[blocki]);
            if (gop !== undefined) {
                gblock.push(gop);
            }
        }

        this.generatedBlocks.set(block.label, gblock);
    }
}

export {
    AOTCodeGenerator
};
