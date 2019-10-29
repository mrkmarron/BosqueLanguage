//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIRTypeOption, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl } from "../../compiler/mir_assembly";
import { SMTTypeEmitter } from "./smttype_emitter";
import { NOT_IMPLEMENTED, sanitizeStringForSMT } from "./smtutils";
import { MIRArgument, MIRRegisterArgument, MIRConstantNone, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantArgument, MIRConstantString, MIROp, MIROpTag, MIRLoadConst, MIRAccessArgVariable, MIRAccessLocalVariable, MIRInvokeFixedFunction, MIRPrefixOp, MIRBinOp, MIRBinEq, MIRBinCmp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRJumpNone, MIRAbort, MIRPhi, MIRBasicBlock, MIRJump, MIRBodyKey, MIRConstructorTuple, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRInvokeKey } from "../../compiler/mir_ops";
import * as assert from "assert";
import { SMTExp, SMTValue, SMTCond, SMTLet, SMTFreeVar } from "./smt_exp";
import { SourceInfo } from "../../ast/parser";
import { CallGInfo, constructCallGraphInfo } from "../../compiler/mir_callg";

class SMTBodyEmitter {
    readonly assembly: MIRAssembly;
    readonly typegen: SMTTypeEmitter;
    readonly callg: CallGInfo;

    private errorCodes = new Map<string, number>();
    private bmcCodes = new Map<string, number>();
    private bmcDepths = new Map<string, number>();

    private currentFile: string = "[No File]";
    private currentRType: MIRType;
    private tmpvarctr = 0;

    private vtypes: Map<string, MIRType> = new Map<string, MIRType>();

    private typeboxings: { fkey: string, from: MIRTypeOption, into: MIRType }[] = [];
    private typeunboxings: { fkey: string, from: MIRType, into: MIRTypeOption }[] = [];

    constructor(assembly: MIRAssembly, typegen: SMTTypeEmitter) {
        this.assembly = assembly;
        this.typegen = typegen;
        this.callg = constructCallGraphInfo(assembly.entryPoints, assembly);

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

        return new SMTValue(`(result_error$${this.typegen.typeToSMTCategory(this.currentRType)} (result_error ${errid}))`);
    }

    generateBMCCreate(invkey: MIRBodyKey): SMTValue {
        const rc = this.callg.recursive.findIndex((scc) => scc.has(invkey));
        const bmcid = [...(this.callg.recursive[rc] as Set<MIRBodyKey>)].sort()[0];

        if (!this.bmcCodes.has(bmcid)) {
            this.bmcCodes.set(bmcid, this.bmcCodes.size);
            this.bmcDepths.set(bmcid, 3);
        }
        const errid = this.bmcCodes.get(bmcid) as number;

        return new SMTValue(`(result_error$${this.typegen.typeToSMTCategory(this.currentRType)} (result_bmc ${errid}))`);
    }

    getBMCGas(key: string): number {
        const rc = this.callg.recursive.findIndex((scc) => scc.has(key));
        const bmcid = [...(this.callg.recursive[rc] as Set<MIRBodyKey>)].sort()[0];

        return this.bmcDepths.get(bmcid) as number;
    }

    varNameToSMTName(name: string): string {
        return sanitizeStringForSMT(name);
    }

    varToSMTName(varg: MIRRegisterArgument): string {
        return this.varNameToSMTName(varg.nameID);
    }

    invokenameToSMT(ivk: MIRInvokeKey): string {
        return sanitizeStringForSMT(ivk);
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

    registerTypeBoxing(from: MIRTypeOption, into: MIRType): string {
        const tbi = this.typeboxings.findIndex((tb) => tb.from.trkey === from.trkey && tb.into.trkey === into.trkey);
        if (tbi !== -1) {
            return this.typeboxings[tbi].fkey;
        }

        const fkey = sanitizeStringForSMT(`Box@${from.trkey}@${into.trkey}`);
        this.typeboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    boxIfNeeded(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (SMTTypeEmitter.isPrimitiveType(from)) {
            if (SMTTypeEmitter.isPrimitiveType(into)) {
                return exp;
            }

            if (into.trkey === "NSCore::Bool") {
                return new SMTValue(`(bsqterm_bool ${exp.emit()})`);
            }
            else if (into.trkey === "NSCore::Int") {
                return new SMTValue(`(bsqterm_int ${exp.emit()})`);
            }
            else {
                return new SMTValue(`(bsqterm_string ${exp.emit()})`);
            }
        }
        else if (SMTTypeEmitter.isFixedTupleType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else if (SMTTypeEmitter.isFixedRecordType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else if (SMTTypeEmitter.isUEntityType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else {
            return exp;
        }
    }

    registerTypeUnBoxing(from: MIRType, into: MIRTypeOption): string {
        const tbi = this.typeunboxings.findIndex((tb) => tb.from.trkey === from.trkey && tb.into.trkey === into.trkey);
        if (tbi !== -1) {
            return this.typeunboxings[tbi].fkey;
        }

        const fkey = sanitizeStringForSMT(`UnBox@${from.trkey}@${into.trkey}`);
        this.typeunboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    unboxIfNeeded(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (SMTTypeEmitter.isPrimitiveType(into)) {
            if (SMTTypeEmitter.isPrimitiveType(from)) {
                return exp;
            }

            if (into.trkey === "NSCore::Bool") {
                return new SMTValue(`(bsqterm_bool_value ${exp.emit()})`);
            }
            else if (into.trkey === "NSCore::Int") {
                return new SMTValue(`(bsqterm_int_value ${exp.emit()})`);
            }
            else {
                return new SMTValue(`(bsqterm_string_value ${exp.emit()})`);
            }
        }
        else if (SMTTypeEmitter.isFixedTupleType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else if (SMTTypeEmitter.isFixedRecordType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else if (SMTTypeEmitter.isUEntityType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else {
            return exp;
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (SMTTypeEmitter.isPrimitiveType(from) !== SMTTypeEmitter.isPrimitiveType(into)) {
            return SMTTypeEmitter.isPrimitiveType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (SMTTypeEmitter.isFixedTupleType(from) !== SMTTypeEmitter.isFixedTupleType(into)) {
            return SMTTypeEmitter.isFixedTupleType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (SMTTypeEmitter.isFixedRecordType(from) !== SMTTypeEmitter.isFixedRecordType(into)) {
            return SMTTypeEmitter.isFixedRecordType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (SMTTypeEmitter.isUEntityType(from) !== SMTTypeEmitter.isUEntityType(into)) {
            return SMTTypeEmitter.isUEntityType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else {
            return exp;
        }
    }

    generateConstantExp(cval: MIRConstantArgument, into: MIRType): SMTExp {
        const isinlineable = SMTTypeEmitter.isPrimitiveType(into);

        if (cval instanceof MIRConstantNone) {
            return new SMTValue("bsqterm_none_const");
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
            return new SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} bsqterm_true_const)`);
        }
    }

    generateMIRConstructorTuple(op: MIRConstructorTuple): SMTExp {
        const tcons = this.typegen.generateFixedTupleConstructor(this.typegen.getMIRType(op.resultTupleType));
        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${tcons}, ${op.args.map((arg) => this.argToSMT(arg, this.typegen.anyType)).join(" ")})`));
    }

    generateMIRConstructorRecord(op: MIRConstructorRecord): SMTExp {
        const tcons = this.typegen.generateFixedRecordConstructor(this.typegen.getMIRType(op.resultRecordType));
        return new SMTLet(this.varToSMTName(op.trgt), new SMTValue(`(${tcons}, ${op.args.map((arg) => this.argToSMT(arg[1], this.typegen.anyType)).join(" ")})`));
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType): SMTExp {
        const tuptype = this.getArgType(op.arg);
        if (SMTTypeEmitter.isFixedTupleType(tuptype)) {
            const ftuptype = SMTTypeEmitter.getFixedTupleType(tuptype);
            if (op.idx < ftuptype.entries.length) {
                return new SMTLet(this.varToSMTName(op.trgt), this.coerce(new SMTValue(`(${this.typegen.generateFixedTupleAccessor(tuptype, op.idx)} ${this.argToSMT(op.arg, tuptype).emit()})`), this.typegen.anyType, resultAccessType));
            }
            else {
                return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqterm_none_const"));
            }
        }
        else {
            const value = new SMTValue(`(select (bsqterm_tuple_entries ${this.argToSMT(op.arg, tuptype).emit()}) ${op.idx})`);
            return new SMTLet(this.varToSMTName(op.trgt), this.coerce(value, this.typegen.anyType, resultAccessType));
        }
    }

    generateMIRAccessFromProperty(op: MIRAccessFromProperty, resultAccessType: MIRType): SMTExp {
        const rectype = this.getArgType(op.arg);
        if (SMTTypeEmitter.isFixedRecordType(rectype)) {
            const frectype = SMTTypeEmitter.getFixedRecordType(rectype);
            const hasproperty = frectype.entries.findIndex((entry) => entry.name === op.property) !== -1;
            if (hasproperty) {
                return new SMTLet(this.varToSMTName(op.trgt), this.coerce(new SMTValue(`(${this.typegen.generateFixedRecordAccessor(rectype, op.property)} ${this.argToSMT(op.arg, rectype).emit()})`), this.typegen.anyType, resultAccessType));
            }
            else {
                return new SMTLet(this.varToSMTName(op.trgt), new SMTValue("bsqterm_none_const"));
            }
        }
        else {
            const value = new SMTValue(`(select (bsqterm_record_entries ${this.argToSMT(op.arg, rectype).emit()}) "${op.property}")`);
            return new SMTLet(this.varToSMTName(op.trgt), this.coerce(value, this.typegen.anyType, resultAccessType));
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        const tv = this.generateTempName();
        const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType((idecl as MIRInvokeDecl).resultType));
        const resulttype = this.typegen.typeToSMTCategory(this.currentRType);

        const invokeexp = new SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
        const checkerror = new SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new SMTValue(`(result_error@${this.typegen.typeToSMTCategory(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new SMTValue(tv);
        const normalassign = new SMTLet(this.varToSMTName(ivop.trgt), new SMTValue(`(result_success_value@${ivrtype} ${tv})`));

        return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
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

    generateFastCompare(op: string, lhs: MIRArgument, rhs: MIRArgument): string {
        const lhvtype = this.getArgType(lhs);
        const rhvtype = this.getArgType(rhs);

        if (lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool") {
            return `(${op} ${this.argToSMT(lhs, this.typegen.boolType).emit()} ${this.argToSMT(rhs, this.typegen.boolType).emit()}`;
        }
        else if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
            return `(${op} ${this.argToSMT(lhs, this.typegen.intType).emit()} ${this.argToSMT(rhs, this.typegen.intType).emit()}`;
        }
        else {
            return NOT_IMPLEMENTED<string>("generateFastCompare -- string");
        }
    }

    generateStmt(op: MIROp, fromblck: string, gass: number): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = op as MIRLoadConst;
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
                const lav = op as MIRAccessArgVariable;
                return new SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = op as MIRAccessLocalVariable;
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
                return this.generateMIRInvokeFixedFunction(invk);
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
                const ite = new SMTCond(new SMTValue(`(or ${smtconds.join(" ")})`), this.generateErrorCreate(op.sinfo), new SMTLet(this.varToSMTName(bop.trgt), new SMTValue(restmp), SMTFreeVar.generate()));

                return new SMTLet(restmp, new SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`), ite);
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;

                const lhvtype = this.getArgType(beq.lhs);
                const rhvtype = this.getArgType(beq.rhs);
                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(this.generateFastEquals(beq.op, beq.lhs, beq.rhs)));
                }
                else {
                    const larg = this.argToSMT(beq.lhs, lhvtype);
                    const rarg = this.argToSMT(beq.rhs, rhvtype);

                    const sloweq = `(@equality_op ${larg.emit()} ${rarg.emit()})`;
                    return new SMTLet(this.varToSMTName(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${sloweq})` : sloweq));
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;

                const lhvtype = this.getArgType(bcmp.lhs);
                const rhvtype = this.getArgType(bcmp.rhs);

                if (isInlinableType(lhvtype) && isInlinableType(rhvtype)) {
                    return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(this.generateFastCompare(bcmp.op, bcmp.lhs, bcmp.rhs)));
                }
                else {
                    const larg = this.argToSMT(bcmp.lhs, lhvtype).emit();
                    const rarg = this.argToSMT(bcmp.rhs, rhvtype).emit();

                    if (bcmp.op === "<") {
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(`(@compare_op ${larg} ${rarg})`));
                    }
                    else if (bcmp.op === ">") {
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(`(@compare_op ${rarg} ${larg})`));
                    }
                    else if (bcmp.op === "<=") {
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(`(or (@compare_op ${larg} ${rarg}) (@equality_op ${larg} ${rarg}))`));
                    }
                    else {
                        return new SMTLet(this.varToSMTName(bcmp.trgt), new SMTValue(`(or (@compare_op ${rarg} ${larg}) (@equality_op ${larg} ${rarg}))`));
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;

                if (isInlinableType(this.getArgType(ton.arg))) {
                    return new SMTLet(this.varToSMTName(ton.trgt), new SMTValue("false"));
                }
                else {
                    return new SMTLet(this.varToSMTName(ton.trgt), new SMTValue(`(= ${this.argToSMT(ton.arg, this.typegen.anyType).emit()} bsq_term_none)`));
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;

                if (isInlinableType(this.getArgType(tos.arg))) {
                    return new SMTLet(this.varToSMTName(tos.trgt), new SMTValue("true"));
                }
                else {
                    return new SMTLet(this.varToSMTName(tos.trgt), new SMTValue(`(not (= ${this.argToSMT(tos.arg, this.typegen.anyType).emit()} bsq_term_none))`));
                }
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
                return this.generateErrorCreate(aop.sinfo);
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
                const argtype = this.getArgType(njop.arg);
                if (isInlinableType(argtype)) {
                    return new SMTCond(new SMTValue("false"), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
                }
                else {
                    return new SMTCond(new SMTValue(`(= ${this.argToSMT(njop.arg, this.typegen.anyType).emit()} bsq_term_none)`), SMTFreeVar.generate("#true_trgt#"), SMTFreeVar.generate("#false_trgt#"));
                }
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

    generateBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, gas: number, supportcalls: string[]): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas, supportcalls);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = this.typegen.typeToSMTType(this.currentRType);
            let rexp = new SMTValue(`(result_success$${resulttype} _return_)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, gas, supportcalls);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas, supportcalls);

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas, supportcalls);

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl, gas: number): { fulldecl: string, supportcalls: string[] } {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.assembly.typeMap.get(idecl.resultType) as MIRType;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTType(this.assembly.typeMap.get(arg.type) as MIRType)})`);
        const restype = this.typegen.typeToSMTType(this.assembly.typeMap.get(idecl.resultType) as MIRType);
        const decl = `(define-fun ${this.invokenameToSMTName(idecl.key)} (${args.join(" ")}) Result$${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            this.vtypes = new Map<string, MIRType>();
            (idecl.body.vtypes as Map<string, string>).forEach((tkey, name) => {
                this.vtypes.set(name, this.assembly.typeMap.get(tkey) as MIRType);
            });

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            let supportcalls: string[] = [];
            const body = this.generateBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, gas, supportcalls);

            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                return { fulldecl: `${decl} \n${body.emit("  ")})`, supportcalls: supportcalls };
            }
            else {
                let cbody = body;

                if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                    return { fulldecl: `${decl} \n${cbody.emit("  ")})`, supportcalls: supportcalls };
                }
                else {
                    return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string, supportcalls: string[] }>("generateInvoke -- Pre/Post");
                }
            }
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return NOT_IMPLEMENTED<{ fwddecl: string, fulldecl: string, supportcalls: string[] }>("generateInvoke -- MIRInvokePrimitiveDecl");
        }
    }
}

export {
    SMTBodyEmitter
};
