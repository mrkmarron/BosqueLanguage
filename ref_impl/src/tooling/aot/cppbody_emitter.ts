//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIRFunctionParameter } from "../../compiler/mir_assembly";
import { CPPTypeEmitter } from "./cpptype_emitter";
import { NOT_IMPLEMENTED, filenameClean, sanitizeStringForCpp } from "./cpputils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRDebug, MIRJump, MIRJumpCond, MIRJumpNone, MIRAbort, MIRBasicBlock, MIRPhi, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRBodyKey, MIRAccessFromField } from "../../compiler/mir_ops";
import * as assert from "assert";
import { topologicalOrder } from "../../compiler/mir_info";
import { constructCallGraphInfo, CallGInfo } from "../../compiler/mir_callg";

class CPPBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: CPPTypeEmitter;
    readonly callg: CallGInfo;

    readonly allPropertyNames: Set<string> = new Set<string>();
    readonly allConstStrings: Map<string, string> = new Map<string, string>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();
    private generatedBlocks: Map<string, string[]> = new Map<string, string[]>();

    private compoundEqualityOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTEQOps: { fkey: string, t1: MIRType, t2: MIRType }[] = [];

    constructor(assembly: MIRAssembly, typegen: CPPTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callg = constructCallGraphInfo(assembly.entryPoints, assembly);

        this.currentRType = typegen.noneType;
    }

    labelToCpp(label: string): string {
        return sanitizeStringForCpp(label);
    }

    varNameToCppName(name: string): string {
        if (name === "this") {
            return "$this";
        }
        else {
            return sanitizeStringForCpp(name);
        }
    }

    varToCppName(varg: MIRRegisterArgument): string {
        return this.varNameToCppName(varg.nameID);
    }

    invokenameToCPP(ivk: MIRInvokeKey): string {
        return sanitizeStringForCpp(ivk);
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

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): string {
        const isinlineable = this.typegen.isPrimitiveType(into);

        if (cval instanceof MIRConstantNone) {
            return "BSQ_VALUE_NONE";
        }
        else if (cval instanceof MIRConstantTrue) {
            return isinlineable ? "true" : "BSQ_VALUE_TRUE";
        }
        else if (cval instanceof MIRConstantFalse) {
            return isinlineable ? "false" : "BSQ_VALUE_FALSE";
        }
        else if (cval instanceof MIRConstantInt) {
            if (isinlineable) {
                return cval.value;
            }
            else {
                if (cval.value === "0") {
                    return "BSQ_VALUE_0";
                }
                else if (cval.value === "1") {
                    return "BSQ_VALUE_POS_1";
                }
                else if (cval.value === "-1") {
                    return "BSQ_VALUE_NEG_1";
                }
                else {
                    return `BSQ_BOX_VALUE_INT(${cval.value})`;
                }
            }
        }
        else {
            assert(cval instanceof MIRConstantString);

            const sval = (cval as MIRConstantString).value;
            const sname = "str$" + this.allConstStrings.size;
            if (!this.allConstStrings.has(sval)) {
                this.allConstStrings.set(sval, sname);
            }

            return `(&Runtime::${this.allConstStrings.get(sval) as string})`;
        }
    }

    argToCpp(arg: MIRArgument, into: MIRType): string {
        if (arg instanceof MIRRegisterArgument) {
            return this.typegen.coerce(this.varToCppName(arg), this.getArgType(arg), into);
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
            return `BSQ_GET_VALUE_TRUTHY(${this.varToCppName(arg)})`;
        }
    }

    static expBodyTrivialCheck(bd: MIRBody): MIROp | undefined {
        if (bd.body.size !== 2 || (bd.body.get("entry") as MIRBasicBlock).ops.length !== 1) {
            return undefined;
        }

        const op = (bd.body.get("entry") as MIRBasicBlock).ops[0];
        if (op.tag === MIROpTag.MIRLoadConst) {
            return op;
        }
        else {
            return undefined;
        }
    }

    generateAccessConstantValue(cp: MIRAccessConstantValue): string {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const top = CPPBodyEmitter.expBodyTrivialCheck(cdecl.value);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return `${this.varToCppName(cp.trgt)} = ${this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt))};`;
        }
        else {
            return `${this.varToCppName(cp.trgt)} = ${this.invokenameToCPP(cdecl.value.bkey)}();`;
        }
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): string {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const top = CPPBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return `${this.varToCppName(ld.trgt)} = ${this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt))};`;
        }
        else {
            return `${this.varToCppName(ld.trgt)} = ${this.invokenameToCPP((fdecl.value as MIRBody).bkey)}();`;
        }
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): string {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToCpp(arg, ftype);
        });

        const smtctype = this.typegen.typeToCPPType(this.typegen.getMIRType(cp.tkey), "base");
        const cexp = `${this.varToCppName(cp.trgt)} = new ${smtctype}(${fvals.join(", ")});`;
        if (ctype.invariants.length === 0) {
            return cexp;
        }
        else {
            const testexp = `${sanitizeStringForCpp("invariant::" + cp.tkey)}(${this.varToCppName(cp.trgt)});`;
            return cexp + " " + testexp;
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType): string {
        const tuptype = this.getArgType(op.arg);
        if (this.typegen.isFixedTupleType(tuptype)) {
            const ftuptype = CPPTypeEmitter.getFixedTupleType(tuptype);
            if (op.idx < ftuptype.entries.length) {
                const value = `(${this.argToCpp(op.arg, tuptype)})${this.typegen.generateFixedTupleAccessor(op.idx)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else {
            const value = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, this.typegen.anyType)}, BSQTuple)->atFixed<${op.idx}>()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
        }
    }

    generateMIRAccessFromProperty(op: MIRAccessFromProperty, resultAccessType: MIRType): string {
        const rectype = this.getArgType(op.arg);
        if (this.typegen.isFixedRecordType(rectype)) {
            const frectype = CPPTypeEmitter.getFixedRecordType(rectype);
            const hasproperty = frectype.entries.findIndex((entry) => entry.name === op.property) !== -1;
            if (hasproperty) {
                const value = `(${this.argToCpp(op.arg, rectype)})${this.typegen.generateFixedRecordAccessor(rectype, op.property)}`;
                return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
            }
            else {
                return `${this.varToCppName(op.trgt)} = BSQ_VALUE_NONE;`;
            }
        }
        else {
            const value = `BSQ_GET_VALUE_PTR(${this.argToCpp(op.arg, this.typegen.anyType)}, BSQRecord)->atFixed<MIRPropertyEnum::${sanitizeStringForCpp(op.property)}>()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(value, this.typegen.anyType, resultAccessType)};`;
        }
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): string {
        const argtype = this.getArgType(op.arg);

        if (this.typegen.isUEntityType(argtype)) {
            const etype = CPPTypeEmitter.getUEntityType(argtype);
            const entity = this.assembly.entityDecls.get(etype.ekey) as MIREntityTypeDecl;
            const field = entity.fields.find((f) => f.name === op.field) as MIRFieldDecl;

            const access = `${this.argToCpp(op.arg, argtype)}->${op.field}`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, this.typegen.getMIRType(field.declaredType), resultAccessType)};`;
        }
        else {
            const access = `${this.argToCpp(op.arg, this.typegen.anyType)}get$${op.field}()`;
            return `${this.varToCppName(op.trgt)} = ${this.typegen.coerce(access, this.typegen.anyType, resultAccessType)};`;
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): string {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToCpp(ivop.args[i], this.typegen.getMIRType(idecl.params[i].type)));
        }

        const rtype = this.typegen.getMIRType(ivop.resultType);
        if (this.typegen.maybeRefableCountableType(rtype)) {
            vals.push(`$scope$.getCallerSlot<${this.typegen.scopectr++}>()`);
        }

        return `${this.varToCppName(ivop.trgt)} = ${this.invokenameToCPP(ivop.mkey)}(${vals.join(", ")});`;
    }

    registerCompoundEquals(t1: MIRType, t2: MIRType): string {
        const lt = (t1.trkey < t2.trkey) ? t1 : t2;
        const rt = (t1.trkey < t2.trkey) ? t2 : t1;

        const fkey = `equals@${sanitizeStringForCpp(lt.trkey)}$${sanitizeStringForCpp(rt.trkey)}`;

        if (this.compoundEqualityOps.findIndex((eop) => eop.t1.trkey === lt.trkey && eop.t2.trkey === rt.trkey) === -1) {
            this.compoundEqualityOps.push({ fkey: fkey, t1: lt, t2: rt });
        }

        return fkey;
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int"){
            return `(${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)})`;
        }
        else {
            return `(${this.argToCpp(lhs, this.typegen.stringType)}->sdata ${op} ${this.argToCpp(rhs, this.typegen.stringType)}->sdata)`;
        }
    }

    registerCompoundLT(t1: MIRType, t2: MIRType): string {
        const fkey = `lt$${sanitizeStringForCpp(t1.trkey)}$${sanitizeStringForCpp(t2.trkey)}`;

        if (this.compoundLTOps.findIndex((eop) => eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTOps.push({ fkey: fkey, t1: t1, t2: t2 });
        }

        return fkey;
    }

    registerCompoundLTEQ(t1: MIRType, t2: MIRType): string {
        const fkey = `lteq$${sanitizeStringForCpp(t1.trkey)}$${sanitizeStringForCpp(t2.trkey)}`;

        if (this.compoundLTEQOps.findIndex((eop) => eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTEQOps.push({ fkey: fkey, t1: t1, t2: t2 });
        }

        return fkey;
    }

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${this.argToCpp(lhs, this.typegen.boolType)} ${op} ${this.argToCpp(rhs, this.typegen.boolType)})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int"){
            return `(${this.argToCpp(lhs, this.typegen.intType)} ${op} ${this.argToCpp(rhs, this.typegen.intType)})`;
        }
        else {
            return `(${this.argToCpp(lhs, this.typegen.stringType)}->sdata ${op} ${this.argToCpp(rhs, this.typegen.stringType)}->sdata)`;
        }
    }

    generateStmt(op: MIROp): string | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return `${this.varToCppName(lcv.trgt)} = ${this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt))};`;
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<string>("MIRLoadConstTypedString");
            }
            case MIROpTag.MIRAccessConstantValue: {
                const acv = (op as MIRAccessConstantValue);
                return this.generateAccessConstantValue(acv);
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = (op as MIRLoadFieldDefaultValue);
                return this.generateLoadFieldDefaultValue(ldv);
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = op as MIRAccessArgVariable;
                return `${this.varToCppName(lav.trgt)} = ${this.argToCpp(lav.name, this.getArgType(lav.trgt))};`;
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                return `${this.varToCppName(llv.trgt)} = ${this.argToCpp(llv.name, this.getArgType(llv.trgt))};`;
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                return this.generateMIRConstructorPrimary(cp);
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
                const tc = op as MIRConstructorTuple;
                return `${this.varToCppName(tc.trgt)} = { ${tc.args.map((arg) => this.argToCpp(arg, this.typegen.anyType)).join(", ")} };`;
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;
                return `${this.varToCppName(tr.trgt)} = { ${tr.args.map((arg) => this.argToCpp(arg[1], this.typegen.anyType)).join(", ")} };`;
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return this.generateMIRAccessFromIndex(ai, this.typegen.getMIRType(ai.resultAccessType));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return this.generateMIRAccessFromProperty(ap, this.typegen.getMIRType(ap.resultAccessType));
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<string>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
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
                return this.generateMIRInvokeFixedFunction(invk);
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
                if (bop.op === "+") {
                    return `BSQ_OP_ADD(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_SUB(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_MULT(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else if (bop.op === "-") {
                    return `BSQ_OP_DIV(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
                else {
                    return `BSQ_OP_MOD(${this.varToCppName(bop.trgt)}, ${this.argToCpp(bop.lhs, this.typegen.intType)}, ${this.argToCpp(bop.rhs, this.typegen.intType)}, "${filenameClean(this.currentFile)}", ${op.sinfo.line})`;
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (this.typegen.isPrimitiveType(lhvtype) && this.typegen.isPrimitiveType(rhvtype)) {
                    return `${this.varToCppName(beq.trgt)} = ${this.generateFastEquals(beq.op, beq.lhs, beq.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(beq.lhs, lhvtype);
                    const rarg = this.argToCpp(beq.rhs, rhvtype);

                    const compoundeq = `${this.registerCompoundEquals(lhvtype, rhvtype)}(${larg} ${rarg})`;
                    return `${this.varToCppName(beq.trgt)} = ${beq.op === "!=" ? "!" : ""}${compoundeq};`;
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if (this.typegen.isPrimitiveType(lhvtype) && this.typegen.isPrimitiveType(rhvtype)) {
                    return `${this.varToCppName(bcmp.trgt)} = ${this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs)};`;
                }
                else {
                    const larg = this.argToCpp(bcmp.lhs, lhvtype);
                    const rarg = this.argToCpp(bcmp.rhs, rhvtype);

                    if (bcmp.op === "<") {
                        const compoundlt = `${this.registerCompoundLT(lhvtype, rhvtype)}(${larg} ${rarg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlt};`;
                    }
                    else if (bcmp.op === ">") {
                        const compoundlt = `(${this.registerCompoundLT(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlt};`;
                    }
                    else if (bcmp.op === "<=") {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${larg} ${rarg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlteq};`;
                    }
                    else {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return `${this.varToCppName(bcmp.trgt)} = ${compoundlteq};`;
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;

                if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, this.getArgType(ton.arg))) {
                    return "false";
                }
                else if (this.typegen.assembly.subtypeOf(this.getArgType(ton.arg), this.typegen.noneType)) {
                    return "true";
                }
                else {
                    return `${this.varToCppName(ton.trgt)} = BSQ_IS_VALUE_NONE(${this.varToCppName(ton.arg)});`;
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;

                if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, this.getArgType(tos.arg))) {
                    return "true";
                }
                else {
                    return `${this.varToCppName(tos.trgt)} = BSQ_IS_VALUE_NONNONE(${this.varToCppName(tos.arg)};`;
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
                return `BSQ_ABORT("${aop.info}", "${filenameClean(this.currentFile)}", ${aop.sinfo.line});`;
            }
            case MIROpTag.MIRDebug: {
                //debug is a nop in AOT release mode but we allow it for our debugging purposes
                const dbgop = op as MIRDebug;
                if (dbgop.value === undefined) {
                    return "assert(false);";
                }
                else {
                    return `printf(Runtime::diagnostic_format(${this.argToCpp(dbgop.value, this.typegen.anyType)}).c_str()); printf("\\n");`;
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
                if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    return `goto ${this.labelToCpp(njop.someblock)};`;
                }
                else if (this.typegen.assembly.subtypeOf(this.getArgType(njop.arg), this.typegen.noneType)) {
                    return `goto ${this.labelToCpp(njop.noneblock)};`;
                }
                else {
                    return `if(BSQ_IS_VALUE_NONE(${this.argToCpp(njop.arg, this.typegen.anyType)})) {goto ${this.labelToCpp(njop.noneblock)};} else {goto ${njop.someblock};}`;
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

    generateBlock(block: MIRBasicBlock) {
        let gblock: string[] = [];

        let blocki = 0;
        while (blocki < block.ops.length - 1 && block.ops[blocki] instanceof MIRPhi) {
            const phiop = block.ops[blocki] as MIRPhi;
            phiop.src.forEach((src, fblock) => {
                const assign = `${this.varToCppName(phiop.trgt)} = ${this.argToCpp(src, this.getArgType(phiop.trgt))};`;
                const inblock = this.generatedBlocks.get(fblock) as string[];

                //last entry is the jump so put before that but after all other statements
                const jmp = inblock[inblock.length - 1];
                inblock[inblock.length - 1] = assign;
                inblock.push(jmp);
            });

            ++blocki;
        }

        while (blocki < block.ops.length) {
            const gop = this.generateStmt(block.ops[blocki]);
            if (gop !== undefined) {
                gblock.push(gop);
            }

            ++blocki;
        }

        if (block.label === "exit") {
            if (this.typegen.maybeRefableCountableType(this.currentRType)) {
                if (!this.assembly.subtypeOf(this.typegen.boolType, this.currentRType) && !this.assembly.subtypeOf(this.typegen.intType, this.currentRType)) {
                    if (this.assembly.subtypeOf(this.typegen.noneType, this.currentRType)) {
                        gblock.push("RefCountScopeCallMgr::processCallRefNoneable($callerslot$, _return_);");
                    }
                    else {
                        gblock.push("RefCountScopeCallMgr::processCallReturnFast($callerslot$, _return_);");
                    }
                }
                else {
                    gblock.push("RefCountScopeCallMgr::processCallRefAny($callerslot$, _return_);");
                }
            }

            gblock.push("return _return_;");
        }

        this.generatedBlocks.set(block.label, gblock);
    }

    generateCPPVarDecls(body: MIRBody, params: MIRFunctionParameter[]): string {
        const refscope = this.typegen.scopectr !== 0 ? `RefCountScope<${this.typegen.scopectr}> $scope$;` : ";";

        let vdecls = new Map<string, string[]>();
        (body.vtypes as Map<string, string>).forEach((tkey, name) => {
            if (params.findIndex((p) => p.name === name) === -1) {
                const declt = this.typegen.typeToCPPType(this.typegen.getMIRType(tkey), "decl");
                if (!vdecls.has(declt)) {
                    vdecls.set(declt, [] as string[]);
                }

                (vdecls.get(declt) as string[]).push(this.varNameToCppName(name));
            }
        });
        let vdeclscpp: string[] = [];
        if (vdecls.has("bool")) {
            vdeclscpp.push(`bool ${(vdecls.get("bool") as string[]).join(", ")};`);
        }
        if (vdecls.has("int64_t")) {
            vdeclscpp.push(`int64_t ${(vdecls.get("int64_t") as string[]).join(", ")};`);
        }
        [...vdecls].sort((a, b) => a[0].localeCompare(b[0])).forEach((kv) => {
            if (kv[0] !== "bool" && kv[0] !== "int64_t") {
                vdeclscpp.push(kv[1].map((vname) => `${kv[0]} ${vname}`).join("; ") + ";");
            }
        });

        return [refscope, ...vdeclscpp].join("\n");
    }

    generateCPPInvoke(idecl: MIRInvokeDecl): { fwddecl: string, fulldecl: string } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.typegen.scopectr = 0;

        const args = idecl.params.map((arg) => `${this.typegen.typeToCPPType(this.typegen.getMIRType(arg.type), "parameter")} ${this.varNameToCppName(arg.name)}`);
        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.resultType), "return");

        if (this.typegen.maybeRefableCountableType(this.typegen.getMIRType(idecl.resultType))) {
            args.push("BSQRef** $callerslot$");
        }
        const decl = `${restype} ${this.invokenameToCPP(idecl.key)}(${args.join(", ")})`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
            });

            this.generatedBlocks = new Map<string, string[]>();

            const blocks = topologicalOrder((idecl as MIRInvokeBodyDecl).body.body);
            for (let i = 0; i < blocks.length; ++i) {
                this.generateBlock(blocks[i]);
            }

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                const blockstrs = [...this.generatedBlocks].map((blck) => {
                    const lbl = `${this.labelToCpp(blck[0])}:\n`;
                    const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
                    return lbl + stmts;
                });

                const scopestrs = this.generateCPPVarDecls(idecl.body, idecl.params);

                return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
            }
            else {
                return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string }>("generateInvoke -- Pre/Post");
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string, supportcalls: string[] }>("generateInvoke -- MIRInvokePrimitiveDecl");
        }
    }

    generateSingleCPPInv(body: MIRBody, invname: string, idecl: MIREntityTypeDecl): { fulldecl: string } {
        this.typegen.scopectr = 0;

        const decl = `bool ${invname}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} this)`;

        this.vtypes = new Map<string, MIRType>();
        (body.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
        });

        this.generatedBlocks = new Map<string, string[]>();

        const blocks = topologicalOrder(body.body);
        for (let i = 0; i < blocks.length; ++i) {
            this.generateBlock(blocks[i]);
        }

        const blockstrs = [...this.generatedBlocks].map((blck) => {
            const lbl = `${this.labelToCpp(blck[0])}:\n`;
            const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
            return lbl + stmts;
        });

        const scopestrs = this.generateCPPVarDecls(idecl.invariants[0], [new MIRFunctionParameter("this", idecl.tkey)]);

        return { fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
    }

    generateCPPInv(invkey: MIRBodyKey, idecl: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;

        const decl = `bool ${sanitizeStringForCpp(invkey)}(${this.typegen.typeToCPPType(this.typegen.getMIRType(idecl.tkey), "parameter")} this)`;

        if (idecl.invariants.length === 1) {
            const icall = this.generateSingleCPPInv(idecl.invariants[0], sanitizeStringForCpp(invkey), idecl);

            return { fwddecl: decl + ";", fulldecl: icall.fulldecl };
        }
        else {
            let supportcalls: string[] = [];
            const decls = idecl.invariants.map((pc, i) => {
                const icall = this.generateSingleCPPInv(idecl.invariants[0], `sanitizeStringForCpp(invkey)$${i}`, idecl);

                supportcalls = [...supportcalls, icall.fulldecl];
                return `${sanitizeStringForCpp(invkey)}}$${i}(this)`;
            });

            return { fwddecl: decl + ";", fulldecl: `${supportcalls.join("\n")}\n${decl}\n{\n  return ${decls.join(" & ")};\n}\n` };
        }
    }

    generateCPPConst(constkey: MIRBodyKey, cdecl: MIRConstantDecl): { fwddecl: string, fulldecl: string } | undefined {
        this.currentFile = cdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(cdecl.declaredType);
        this.typegen.scopectr = 0;

        if (CPPBodyEmitter.expBodyTrivialCheck(cdecl.value)) {
            return undefined;
        }

        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(cdecl.declaredType), "return");
        const decl = `${restype} ${this.invokenameToCPP(constkey)}()`;

        this.vtypes = new Map<string, MIRType>();
        (cdecl.value.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
        });

        this.generatedBlocks = new Map<string, string[]>();

        const blocks = topologicalOrder(cdecl.value.body);
        for (let i = 0; i < blocks.length; ++i) {
            this.generateBlock(blocks[i]);
        }

        const blockstrs = [...this.generatedBlocks].map((blck) => {
            const lbl = `${this.labelToCpp(blck[0])}:\n`;
            const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
            return lbl + stmts;
        });

        const scopestrs = this.generateCPPVarDecls(cdecl.value, []);

        return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
    }

    generateCPPFDefault(fdkey: MIRBodyKey, fdecl: MIRFieldDecl): { fwddecl: string, fulldecl: string } | undefined {
        this.currentFile = fdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(fdecl.declaredType);
        this.typegen.scopectr = 0;

        if (CPPBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody)) {
            return undefined;
        }

        const fdbody = fdecl.value as MIRBody;
        const restype = this.typegen.typeToCPPType(this.typegen.getMIRType(fdecl.declaredType), "return");
        const decl = `${restype} ${this.invokenameToCPP(fdkey)}()`;

        this.vtypes = new Map<string, MIRType>();
        (fdbody.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
        });

        this.generatedBlocks = new Map<string, string[]>();

        const blocks = topologicalOrder(fdbody.body);
        for (let i = 0; i < blocks.length; ++i) {
            this.generateBlock(blocks[i]);
        }

        const blockstrs = [...this.generatedBlocks].map((blck) => {
            const lbl = `${this.labelToCpp(blck[0])}:\n`;
            const stmts = blck[1].map((stmt) => "    " + stmt).join("\n");
            return lbl + stmts;
        });

        const scopestrs = this.generateCPPVarDecls(fdbody, []);

        return { fwddecl: decl + ";", fulldecl: `${decl}\n{\n${scopestrs}\n\n${blockstrs.join("\n\n")}\n}\n` };
    }
}

export {
    CPPBodyEmitter
};
