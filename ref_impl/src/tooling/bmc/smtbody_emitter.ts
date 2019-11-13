//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl, MIRConstantDecl, MIRFieldDecl, MIREntityTypeDecl, MIREntityType } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRJumpNone, MIRAbort, MIRPhi, MIRBasicBlock, MIRJump, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey, MIRAccessConstantValue, MIRLoadFieldDefaultValue, MIRBody, MIRConstructorPrimary, MIRBodyKey, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";
import { CallGInfo, constructCallGraphInfo } from "../../compiler/mir_callg";
import { CoreImplBodyText } from "./cppcore_impls";

import * as assert from "assert";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

const DEFAULT_GAS = 3;

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;
    readonly callg: CallGInfo;

    private errorCodes = new Map<string, number>();
    private bmcCodes = new Map<string, number>();
    private bmcGas = new Map<string, number>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private tmpvarctr = 0;
    private currentSCC = new Set<string>();

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    private compoundEqualityOps: { fkey: string, gas: number, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTOps: { fkey: string, gas: number, t1: MIRType, t2: MIRType }[] = [];
    private compoundLTEQOps: { fkey: string, gas: number, t1: MIRType, t2: MIRType }[] = [];

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callg = constructCallGraphInfo(assembly.entryPoints, assembly);

        this.currentRType = typegen.noneType;
    }

    generateTempName(): string {
        return `@tmpvar@${this.tmpvarctr++}`;
    }

    generateErrorCreate(sinfo: SourceInfo, rtype: string): SMTValue {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo) as number;

        return new SMTValue(`(result_error@${rtype} (result_error ${errid}))`);
    }

    getGasForOperation(key: string): number {
        if (!this.bmcGas.has(key)) {
           this.bmcGas.set(key, DEFAULT_GAS);
        }
        return this.bmcGas.get(key) as number;
    }

    generateBMCLimitCreate(key: string, rtype: string): SMTValue {
        if (!this.bmcCodes.has(key)) {
            this.bmcCodes.set(key, this.bmcCodes.size);
         }
        const errid = this.bmcCodes.get(key) as number;

        return new SMTValue(`(result_error@${rtype} (result_bmc ${errid}))`);
    }

    varNameToSMTName(name: string): string {
        if (name === "_return_") {
            return "_return_";
        }
        else {
            return this.typegen.mangleStringForSMT(name);
        }
    }

    varToSMTName(varg: MIRRegisterArgument): string {
        return this.varNameToSMTName(varg.nameID);
    }

    invokenameToSMT(ivk: MIRInvokeKey): string {
        return this.typegen.mangleStringForSMT(ivk);
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

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): SMTExp {
        const isinlineable = this.typegen.isPrimitiveType(into);

        if (cval instanceof MIRConstantNone) {
            return this.typegen.coerce(new SMTValue("bsqterm_none_const"), this.typegen.noneType, into);
        }
        else if (cval instanceof MIRConstantTrue) {
            return new SMTValue(isinlineable ? "true" : "bsqterm_true_const");
        }
        else if (cval instanceof MIRConstantFalse) {
            return new SMTValue(isinlineable ? "false" : "bsqterm_false_const");
        }
        else if (cval instanceof MIRConstantInt) {
            return new SMTValue(isinlineable ? cval.value : `(bsqterm_int ${cval.value})`);
        }
        else {
            assert(cval instanceof MIRConstantString);

            return new SMTValue(isinlineable ? (cval as MIRConstantString).value : `(bsqterm_string ${(cval as MIRConstantString).value})`);
        }
    }

    argToSMT(arg: MIRArgument, into: MIRType): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return this.typegen.coerce(new SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
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
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_true_const)`);
        }
    }

    generateNoneCheck(arg: MIRArgument): SMTExp {
        const argtype = this.getArgType(arg);

        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new SMTValue("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return new SMTValue("false");
        }
        else if (this.typegen.isUEntityType(argtype)) {
            return new SMTValue(`(is-${this.typegen.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(argtype).ekey)} ${this.argToSMT(arg, argtype).emit()})`);
        }
        else {
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_none_const)`);
        }
    }

    static expBodyTrivialCheck(bd: MIRBody): MIROp | undefined {
        if (bd.body.size !== 2 || (bd.body.get("entry") as MIRBasicBlock).ops.length !== 2) {
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

    generateAccessConstantValue(cp: MIRAccessConstantValue): SMTExp {
        const cdecl = this.assembly.constantDecls.get(cp.ckey) as MIRConstantDecl;

        const top = SMTBodyEmitter.expBodyTrivialCheck(cdecl.value);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return new SMTLet(this.varToSMTName(cp.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(cdecl.declaredType));
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);

            const constexp = new SMTValue(this.invokenameToSMT(cdecl.value.bkey));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.typeToSMTCategory(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
            const normalassign = new SMTLet(this.varToSMTName(cp.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

            return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
        }
    }

    generateLoadFieldDefaultValue(ld: MIRLoadFieldDefaultValue): SMTExp {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey) as MIRFieldDecl;

        const top = SMTBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody);
        if (top !== undefined) {
            const cvv = top as MIRLoadConst;
            return new SMTLet(this.varToSMTName(ld.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(fdecl.declaredType));
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);

            const constexp = new SMTValue(this.invokenameToSMT((fdecl.value as MIRBody).bkey));
            const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
            const normalassign = new SMTLet(this.varToSMTName(ld.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

            return new SMTLet(tv, constexp, new SMTCond(checkerror, extracterror, normalassign));
        }
    }

    generateMIRConstructorPrimary(cp: MIRConstructorPrimary): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });

        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new SMTValue(smtctype) : new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        const bindexp = new SMTLet(this.varToSMTName(cp.trgt), cexp);
        if (ctype.invariants.length === 0) {
            return bindexp;
        }
        else {
            const testexp = new SMTValue(`(${this.typegen.mangleStringForSMT("invariant::" + cp.tkey)} ${this.varToSMTName(cp.trgt)})`);
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            const errexp = this.generateErrorCreate(cp.sinfo, resulttype);
            return bindexp.bind(new SMTCond(testexp, SMTFreeVar.generate(), errexp));
        }
    }

    generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty): SMTExp {
        const ctype = this.assembly.entityDecls.get((this.typegen.getMIRType(cpce.tkey).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        if (ctype.name === "List") {
            return new SMTLet(this.varToSMTName(cpce.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(cpce.tkey)} bsqterm_none_const 0)`));
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Map");
        }
    }

    generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons): SMTExp {
        const ctype = this.assembly.entityDecls.get((this.typegen.getMIRType(cpcs.tkey).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        if (ctype.name === "List") {
            const clisttype = this.typegen.getMIRType((ctype.fields.find((fd) => fd.name === "list") as MIRFieldDecl).declaredType);
            const clistcons = this.typegen.generateEntityConstructor(clisttype.options[0].trkey);
            const contentstype = ctype.terms.get("T") as MIRType;

            let cons = this.typegen.coerce(new SMTValue("bsqterm_none_const"), this.typegen.noneType, clisttype).emit();
            for (let i = cpcs.args.length - 1; i >= 0; --i) {
                cons = `(${clistcons} ${this.argToSMT(cpcs.args[i], contentstype).emit()} ${cons})`;
            }

            return new SMTLet(this.varToSMTName(cpcs.trgt), new SMTValue(`(${this.typegen.generateEntityConstructor(cpcs.tkey)} ${cons} ${cpcs.args.length})`));
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Map");
        }
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): SMTExp {
        const tcons = this.typegen.generateTupleConstructor(this.typegen.getMIRType(op.resultTupleType));
        if (tcons === "bsqtuple_0@cons") {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqtuple_empty_const"));
        }
        else {
            const argl = op.args.map((arg) => `(bsqtuple_entry@value ${this.argToSMT(arg, this.typegen.anyType).emit()})`);
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${tcons} ${argl.join(" ")})`));
        }
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): SMTExp {
        const tcons = this.typegen.generateRecordConstructor(this.typegen.getMIRType(op.resultRecordType));
        if (tcons === "bsqrecord_empty@cons") {
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqrecord_empty_const"));
        }
        else {
            const argl = op.args.map((arg) => `(bsqrecord_entry@value ${this.argToSMT(arg[1], this.typegen.anyType).emit()})`);
            return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${tcons} ${argl.join(" ")})`));
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType): SMTExp {
        const tuptype = this.getArgType(op.arg);
        if (this.typegen.isTupleType(tuptype)) {
            if (this.typegen.isKnownLayoutTupleType(tuptype)) {
                return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new SMTValue(`(bsqtuple_entry@term (${this.typegen.generateTupleAccessor(tuptype, op.idx)} ${this.argToSMT(op.arg, tuptype).emit()}))`), this.typegen.anyType, resultAccessType));
            }
            else {
                const tmax = SMTTypeEmitter.getTupleTypeMaxLength(tuptype);
                if (op.idx < tmax) {
                    const recaccess = new SMTValue(`(${this.typegen.generateTupleAccessor(tuptype, op.idx)} ${this.argToSMT(op.arg, tuptype).emit()})`);
                    const iteaccess = new SMTCond(new SMTValue(`(is-bsqtuple_entry@value ${recaccess.emit()})`), new SMTValue(`(bsqtuple_entry@term ${recaccess.emit()})`), new SMTValue("bsqterm_none_const"));
                    return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(iteaccess, this.typegen.anyType, resultAccessType));
                }
                else {
                    return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqterm_none_const"));
                }
            }
        }
        else {
            const avalue = `(select (bsqterm_tuple_entries ${this.argToSMT(op.arg, tuptype).emit()}) ${op.idx})`;
            const value = new SMTCond(new SMTValue(`(is-bsqtuple_entry@clear ${avalue})`), new SMTValue("bsqterm_none"), new SMTValue(avalue));
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(value, this.typegen.anyType, resultAccessType));
        }
    }

    generateMIRAccessFromProperty(op: MIRAccessFromProperty, resultAccessType: MIRType): SMTExp {
        const rectype = this.getArgType(op.arg);
        if (this.typegen.isRecordType(rectype)) {
            if (this.typegen.isKnownLayoutRecordType(rectype)) {
                return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new SMTValue(`(bsqrecord_entry@term (${this.typegen.generateRecordAccessor(rectype, op.property)} ${this.argToSMT(op.arg, rectype).emit()}))`), this.typegen.anyType, resultAccessType));
            }
            else {
                const maxset = SMTTypeEmitter.getRecordTypeMaxPropertySet(rectype);
                if (maxset.includes(op.property)) {
                    const recaccess = new SMTValue(`(${this.typegen.generateRecordAccessor(rectype, op.property)} ${this.argToSMT(op.arg, rectype).emit()})`);
                    const iteaccess = new SMTCond(new SMTValue(`(is-bsqrecord_entry@value ${recaccess.emit()})`), new SMTValue(`(bsqrecord_entry@term ${recaccess.emit()})`), new SMTValue("bsqterm_none_const"));
                    return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(iteaccess, this.typegen.anyType, resultAccessType));
                }
                else {
                    return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqterm_none_const"));
                }
            }
        }
        else {
            const avalue = `(select (bsqterm_record_entries ${this.argToSMT(op.arg, rectype).emit()}) "${op.property}")`;
            const value = new SMTCond(new SMTValue(`(is-bsqrecord_entry@clear ${avalue})`), new SMTValue("bsqterm_none"), new SMTValue(avalue));
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(value, this.typegen.anyType, resultAccessType));
        }
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType): SMTExp {
        const argtype = this.getArgType(op.arg);

        if (this.typegen.isUEntityType(argtype)) {
            const etype = SMTTypeEmitter.getUEntityType(argtype);
            const entity = this.assembly.entityDecls.get(etype.ekey) as MIREntityTypeDecl;
            const field = entity.fields.find((f) => f.name === op.field) as MIRFieldDecl;

            const access = new SMTValue(`(${this.typegen.generateEntityAccessor(etype.ekey, op.field)} ${this.argToSMT(op.arg, argtype).emit()})`);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, this.typegen.getMIRType(field.declaredType), resultAccessType));
        }
        else {
            const access = new SMTValue(`(select (bsqterm_object_entries ${this.argToSMT(op.arg, this.typegen.anyType)}) "${op.field}")`);
            return new SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, this.typegen.anyType, resultAccessType));
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, gas: number | undefined): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        const tv = this.generateTempName();
        const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType((idecl as MIRInvokeDecl).resultType));
        const resulttype = this.typegen.typeToSMTCategory(this.currentRType);

        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(ivop.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        if (this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey)) {
            const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
            return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
        }
        else {
            if (gas === 0) {
                const invokeexp = this.generateBMCLimitCreate(ivop.mkey, ivrtype);
                return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
            }
            else {
                const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)}@gas${gas} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
            }
        }
    }

    registerCompoundEquals(t1: MIRType, t2: MIRType): string {
        const lt = (t1.trkey < t2.trkey) ? t1 : t2;
        const rt = (t1.trkey < t2.trkey) ? t2 : t1;

        const compoundname = `equals@${this.typegen.mangleStringForSMT(lt.trkey)}_${this.typegen.mangleStringForSMT(rt.trkey)}`;
        const gas = this.getGasForOperation(compoundname);
        const fkey = `${compoundname}@${gas}`;

        if (this.compoundEqualityOps.findIndex((eop) => eop.gas === gas && eop.t1.trkey === lt.trkey && eop.t2.trkey === rt.trkey) === -1) {
            this.compoundEqualityOps.push({ fkey: compoundname, gas: gas, t1: lt, t2: rt });
        }

        return fkey;
    }

    generateFastEquals(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        let coreop = "";
        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.boolType).emit()} ${this.argToSMT(rhs, this.typegen.boolType).emit()})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int"){
            coreop = `(= ${this.argToSMT(lhs, this.typegen.intType).emit()} ${this.argToSMT(rhs, this.typegen.intType).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.stringType).emit()} ${this.argToSMT(rhs, this.typegen.stringType).emit()})`;
        }

        return op === "!=" ? `(not ${coreop})` : coreop;
    }

    registerCompoundLT(t1: MIRType, t2: MIRType): string {
        const compoundname = `lt@${this.typegen.mangleStringForSMT(t1.trkey)}_${this.typegen.mangleStringForSMT(t2.trkey)}`;
        const gas = this.getGasForOperation(compoundname);
        const fkey = `${compoundname}@${gas}`;

        if (this.compoundLTOps.findIndex((eop) => eop.gas === gas && eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTOps.push({ fkey: compoundname, gas: gas, t1: t1, t2: t2 });
        }

        return fkey;
    }

    registerCompoundLTEQ(t1: MIRType, t2: MIRType): string {
        const compoundname = `lteq@${this.typegen.mangleStringForSMT(t1.trkey)}_${this.typegen.mangleStringForSMT(t2.trkey)}`;
        const gas = this.getGasForOperation(compoundname);
        const fkey = `${compoundname}@${gas}`;

        if (this.compoundLTEQOps.findIndex((eop) => eop.gas === gas && eop.t1.trkey === t1.trkey && eop.t2.trkey === t2.trkey) === -1) {
            this.compoundLTEQOps.push({ fkey: compoundname, gas: gas, t1: t1, t2: t2 });
        }

        return fkey;
    }

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${op} ${this.argToSMT(lhs, this.typegen.boolType).emit()} ${this.argToSMT(rhs, this.typegen.boolType).emit()})`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
            return `(${op} ${this.argToSMT(lhs, this.typegen.intType).emit()} ${this.argToSMT(rhs, this.typegen.intType).emit()})`;
        }
        else {
            return NOT_IMPLEMENTED<string>("generateFastCompare -- string");
        }
    }

    generateStmt(op: MIROp, fromblck: string, gas: number | undefined): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
                return new SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                return NOT_IMPLEMENTED<SMTExp>("MIRLoadConstTypedString");
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
                return new SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
                return new SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                return this.generateMIRConstructorPrimary(cp);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                return this.generateMIRConstructorTuple(tc);
            }
            case MIROpTag.MIRConstructorRecord: {
                const tr = op as MIRConstructorRecord;
                return this.generateMIRConstructorRecord(tr);
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return this.generateMIRAccessFromIndex(ai, this.typegen.getMIRType(ai.resultAccessType));
            }
            case MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromIndecies");
            }
            case MIROpTag.MIRAccessFromProperty: {
                const ap = op as MIRAccessFromProperty;
                return this.generateMIRAccessFromProperty(ap, this.typegen.getMIRType(ap.resultAccessType));
            }
            case MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED<SMTExp>("MIRProjectFromProperties");
            }
            case MIROpTag.MIRAccessFromField: {
                const af = op as MIRAccessFromField;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
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
                return this.generateMIRInvokeFixedFunction(invk, gas);
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
                        if (pfx.arg instanceof MIRConstantInt) {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`-${(pfx.arg as MIRConstantInt).value}`));
                        }
                        else {
                            return new SMTLet(this.varToSMTName(pfx.trgt), new SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                        }
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
                const ite = new SMTCond(new SMTValue(`(or ${smtconds.join(" ")})`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(restmp), SMTFreeVar.generate()));

                return new SMTLet(restmp, new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`), ite);
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (this.typegen.isPrimitiveType(lhvtype) && this.typegen.isPrimitiveType(rhvtype)) {
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateFastEquals(beq.op, beq.lhs, beq.rhs)));
                }
                else {
                    const larg = this.argToSMT(beq.lhs, lhvtype);
                    const rarg = this.argToSMT(beq.rhs, rhvtype);

                    const compoundeq = `(${this.registerCompoundEquals(lhvtype, rhvtype)} ${larg.emit()} ${rarg.emit()})`;
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${compoundeq})` : compoundeq));
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if ((lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") || (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int")) {
                    return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs)));
                }
                else {
                    const larg = this.argToSMT(bcmp.lhs, lhvtype).emit();
                    const rarg = this.argToSMT(bcmp.rhs, rhvtype).emit();

                    if (bcmp.op === "<") {
                        const compoundlt = `(${this.registerCompoundLT(lhvtype, rhvtype)} ${larg} ${rarg})`;
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(compoundlt));
                    }
                    else if (bcmp.op === ">") {
                        const compoundlt = `(${this.registerCompoundLT(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(compoundlt));
                    }
                    else if (bcmp.op === "<=") {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${larg} ${rarg})`;
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(compoundlteq));
                    }
                    else {
                        const compoundlteq = `(${this.registerCompoundLTEQ(lhvtype, rhvtype)} ${rarg} ${larg})`;
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(compoundlteq));
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                return new SMTLet(this.varToSMTName(ton.trgt), this.generateNoneCheck(ton.arg));
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                return new SMTLet(this.varToSMTName(tos.trgt), new SMTValue(`(not ${this.generateNoneCheck(tos.arg).emit()})`));
           }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<SMTExp>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                return new SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                return new SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                return new SMTLet(this.varToSMTName(llop.trgt), new SMTValue(`(${llop.op === "&" ? "and" : "or"} ${this.argToSMT(llop.lhs, this.typegen.boolType).emit()} ${this.argToSMT(llop.rhs, this.typegen.boolType).emit()})`));
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                return new SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                return new SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case MIROpTag.MIRAbort: {
                const aop = (op as MIRAbort);
                return this.generateErrorCreate(aop.sinfo, this.typegen.typeToSMTCategory(this.currentRType));
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const smttest = this.generateTruthyConvert(cjop.arg);
                return new SMTCond(smttest, SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                return new SMTCond(this.generateNoneCheck(njop.arg), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;

                return new SMTLet(this.varToSMTName(pop.trgt), this.argToSMT(uvar, this.getArgType(pop.trgt)));
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

    generateBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number | undefined): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            let rexp = new SMTValue(`(result_success@${resulttype} _return_)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas);

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl, cscc: Set<string>, gas: number | undefined, gasdown: number | undefined): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.resultType));
        const decl = `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gasdown);

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                return `${decl} \n${body.emit("  ")})`;
            }
            else {
                let cbody = body;

                if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                    return `${decl} \n${cbody.emit("  ")})`;
                }
                else {
                    return NOT_IMPLEMENTED<string>("generateInvoke -- Pre/Post");
                }
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));

            return `${decl} \n    ${this.generateBuiltinBody(idecl as MIRInvokePrimitiveDecl, params)}\n)`;
        }
    }

    generateSMTInv(invkey: MIRBodyKey, idecl: MIREntityTypeDecl): string {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;

        const args = `(this ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.tkey))})`;
        const decl = `(define-fun ${this.invokenameToSMT(invkey)} (${args}) Result@Bool`;

        if (idecl.invariants.length === 1) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.invariants[0].vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const blocks = idecl.invariants[0].body;
            const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, undefined);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            this.vtypes = new Map<string, MIRType>();
            (idecl.invariants[0].vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });

            const decls = idecl.invariants.map((pc, i) => {
                const blocksi = pc.body;
                const bodyi = this.generateBlockExps(blocksi.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocksi, undefined);
                const decli = `(define-fun ${this.invokenameToSMT(invkey)}$${i} (${args}) Result@Bool \n${bodyi.emit("  ")})`;
                const calli = (`(${this.invokenameToSMT(invkey)}${i} this)`);

                return [decli, calli];
            });

            const declsand = decls.map((cc) => {
                const tv = `@tmpvarda@${this.tmpvarctr++}`;
                return new SMTLet(tv, new SMTValue(cc[1]), new SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
            });

            return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl} \n(and ${declsand.join(" ")}))`;
        }
    }

    generateSMTConst(constkey: MIRBodyKey, cdecl: MIRConstantDecl): string | undefined {
        this.currentFile = cdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(cdecl.declaredType);

        if (SMTBodyEmitter.expBodyTrivialCheck(cdecl.value as MIRBody)) {
            return undefined;
        }

        this.vtypes = new Map<string, MIRType>();
        (cdecl.value.vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });

        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(cdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(constkey)} () Result@${restype}`;
        const blocks = cdecl.value.body;
        const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }

    generateSMTFDefault(fdkey: MIRBodyKey, fdecl: MIRFieldDecl): string | undefined {
        this.currentFile = fdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(fdecl.declaredType);

        if (SMTBodyEmitter.expBodyTrivialCheck(fdecl.value as MIRBody)) {
            return undefined;
        }

        this.vtypes = new Map<string, MIRType>();
        ((fdecl.value as MIRBody).vtypes as Map<string, string>).forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });

        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(fdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(fdkey)} () Result@${restype}`;
        const blocks = (fdecl.value as MIRBody).body;
        const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }

    generateBuiltinBody(idecl: MIRInvokePrimitiveDecl, params: string[]): string {
        switch (idecl.implkey) {
            case "_listcons": {
                const mres = this.typegen.getMIRType(idecl.resultType);
                return `(result_success@${this.typegen.typeToSMTCategory(mres)} (${this.typegen.generateEntityConstructor(idecl.resultType)} ${params[1]} ${params[0]}))`;
            }
            default: {
                return (CoreImplBodyText.get(idecl.implkey) as ((params: string[]) => string))(params);
            }
        }
    }
}

export {
    SMTBodyEmitter
};
