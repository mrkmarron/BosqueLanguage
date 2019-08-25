//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex, MIRConstantTrue, MIRConstantFalse, MIRConstantNone, MIRConstantInt, MIRConstantString, MIRPrefixOp, MIRConstantArgument, MIRBinOp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRAbort, MIRJumpCond, MIRJumpNone, MIRBinEq, MIRBinCmp, MIRModifyWithIndecies, MIRInvokeFixedFunction, MIRInvokeKey, MIRBasicBlock, MIRPhi, MIRJump, MIRConstructorPrimary, MIRAccessFromField, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionSingletons } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType, MIRTypeOption, MIREntityTypeDecl, MIREntityType, MIRRecordType, MIRInvokeDecl, MIRInvokeBodyDecl, MIRInvokePrimitiveDecl } from "../../compiler/mir_assembly";
import { constructCallGraphInfo } from "../../compiler/mir_callg";
import { BuiltinTypes, BuiltinTypeEmit, BuiltinCalls, BuiltinCallEmit } from "./builtins";

function NOT_IMPLEMENTED<T>(action: string): T {
    throw new Error(`Not Implemented: ${action}`);
}

const smt_header = `
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
`;

const smtlib_code = `
(declare-datatypes ( (ResultCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( (BTerm 0) ) (
    (
      (bsq_term_none) (bsq_term_bool (bsq_term_bool_value Bool)) (bsq_term_int (bsq_term_int_value Int)) (bsq_term_string (bsq_term_string_value String))
      (bsq_term_tuple (bsq_term_tuple_size Int) (bsq_term_tuple_entries (Array Int BTerm)))
      (bsq_term_record (bsq_term_record_size Int) (bsq_term_record_properties (Array Int String)) (bsq_term_record_entries (Array String BTerm)))
      (bsq_term_entity (bsq_term_entity_type String) (bsq_term_entity_entries (Array String BTerm)))
      (bsq_term_list (bsq_term_list_type String) (bsq_term_list_size Int) (bsq_term_list_entries (Array Int BTerm)))
    )
))
`;

abstract class SMTExp {
    abstract bind(sval: SMTExp, svar?: string): SMTExp;
    abstract emit(indent?: string): string;
}

class SMTFreeVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();
        this.vname = vname;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return svar === undefined || this.vname === svar ? sval : this;
    }

    emit(indent?: string): string {
        return this.vname;
    }
}

class SMTValue extends SMTExp {
    readonly value: string;

    constructor(value: string) {
        super();
        this.value = value;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return this;
    }

    emit(indent?: string): string {
        return this.value;
    }
}

class SMTLet extends SMTExp {
    readonly lname: string;
    readonly exp: SMTExp;
    readonly body: SMTExp;

    constructor(lname: string, exp: SMTExp, body: SMTExp) {
        super();
        this.lname = lname;
        this.exp = exp;
        this.body = body;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return new SMTLet(this.lname, this.exp.bind(sval, svar), this.body.bind(sval, svar));
    }

    emit(indent?: string): string {
        if (indent === undefined) {
            return `(let ((${this.lname} ${this.exp.emit()})) ${this.body.emit()})`;
        }
        else {
            return `(let ((${this.lname} ${this.exp.emit()}))\n${indent + "  "}${this.body.emit(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTCond extends SMTExp {
    readonly test: SMTExp;
    readonly iftrue: SMTExp;
    readonly iffalse: SMTExp;

    constructor(test: SMTExp, iftrue: SMTExp, iffalse: SMTExp) {
        super();
        this.test = test;
        this.iftrue = iftrue;
        this.iffalse = iffalse;
    }

    bind(sval: SMTExp, svar?: string): SMTExp {
        return new SMTCond(this.test.bind(sval, svar), this.iftrue.bind(sval, svar), this.iffalse.bind(sval, svar));
    }

    emit(indent: string | undefined): string {
        if (indent === undefined) {
            return `(ite ${this.test.emit()} ${this.iftrue.emit()} ${this.iffalse.emit()})`;
        }
        else {
            return `(ite ${this.test.emit()}\n${indent + "  "}${this.iftrue.emit(indent + "  ")}\n${indent + "  "}${this.iffalse.emit(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTLIBGenerator {
    readonly assembly: MIRAssembly;
    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;
    readonly anyType: MIRType;

    private cinvoke: MIRInvokeDecl | undefined = undefined;

    private tmpvarctr = 0;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.noneType = this.assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = this.assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = this.assembly.typeMap.get("NSCore::String") as MIRType;
        this.anyType = this.assembly.typeMap.get("NSCore::Any") as MIRType;
    }

    static smtsanizite(str: string): string {
        return str
        .replace(/::/g, "$cc$")
        .replace(/=/g, "$eq$")
        .replace(/\[/g, "$lb$")
        .replace(/\]/g, "$rb$")
        .replace(/{/g, "$lc$")
        .replace(/}/g, "$rc$")
        .replace(/</g, "$la$")
        .replace(/>/g, "$ra$")
        .replace(/\|/g, "$v$");
    }

    getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.noneType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.boolType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.intType;
            }
            else {
                return this.stringType;
            }
        }
    }

    isTypeExact(type: MIRType | MIRTypeOption): boolean {
        if (type instanceof MIRType) {
            return type.options.length === 1 && this.isTypeExact(type.options[0]);
        }

        if (type instanceof MIREntityType) {
            const tdecl = this.assembly.entityDecls.get(type.ekey) as MIREntityTypeDecl;
            if (!tdecl.isCollectionEntityType && !tdecl.isMapEntityType) {
                return true;
            }
            else {
                return [...tdecl.terms].every((etype) => this.isTypeExact(etype[1]));
            }
        }
        else if (type instanceof MIRTupleType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else if (type instanceof MIRRecordType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else {
            return false;
        }
    }

    typeToSMT2Type(type: MIRType | MIRTypeOption): string {
        if (!this.isTypeExact(type)) {
            return "BTerm";
        }
        else {
            const topt = (type instanceof MIRType) ? type.options[0] : type;
            if (topt instanceof MIREntityType) {
                const tdecl = this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                if (tdecl.ns === "NSCore" && (tdecl.name === "Bool" || tdecl.name === "Int" || tdecl.name === "String")) {
                    return tdecl.name;
                }
                else {
                    return "T" + SMTLIBGenerator.smtsanizite(topt.trkey);
                }
            }
            else if (topt instanceof MIRTupleType) {
                const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
                return `Tbsq_tuple$_${entryinfos.join("$")}_$`;
            }
            else {
                assert(topt instanceof MIRRecordType);

                const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
                return `Tbsq_record$_${entryinfos.join("")}_$`;
            }
        }
    }

    typeToSMT2Constructor(type: MIRType | MIRTypeOption): string {
        assert(this.isTypeExact(type));

        const topt = (type instanceof MIRType) ? type.options[0] : type;
        if (topt instanceof MIREntityType) {
            return SMTLIBGenerator.smtsanizite(topt.trkey);
        }
        else if (topt instanceof MIRTupleType) {
            const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
            return `bsq_tuple$_${entryinfos.join("$")}_$`;
        }
        else {
            assert(topt instanceof MIRRecordType);

            const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
            return `bsq_tuple$_${entryinfos.join("")}_$`;
        }
    }

    invokenameToSMT2(ivk: MIRInvokeKey): string {
        return SMTLIBGenerator.smtsanizite(ivk);
    }

    generateFreeSMTVar(name?: string): SMTFreeVar {
        return new SMTFreeVar(`${name || "#body#"}`);
    }

    varNameToSMT2Name(varg: string): string {
        return varg;
    }

    varToSMT2Name(varg: MIRRegisterArgument): string {
        return this.varNameToSMT2Name(varg.nameID).replace(/#/g, "@");
    }

    propertyToSMT2Name(pname: string): string {
        return pname;
    }

    argToSMT2Direct(arg: MIRArgument): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return new SMTValue(this.varToSMT2Name(arg));
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return new SMTValue("bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue("true");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue("false");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(arg.value);
            }
            else {
                return new SMTValue((arg as MIRConstantString).value);
            }
        }
    }

    argToSMT2Coerce(arg: MIRArgument, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            const rval = new SMTValue(this.varToSMT2Name(arg));
            if (this.isTypeExact(into)) {
                return this.coerceUnBoxIfNeeded(rval, from, into);
            }
            else {
                return this.coerceBoxIfNeeded(rval, from, into);
            }
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return new SMTValue("bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue(this.isTypeExact(into) ? "true" : "(bsq_term_bool true)");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue(this.isTypeExact(into) ? "false" : "(bsq_term_bool false)");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(this.isTypeExact(into) ? arg.value : `(bsq_term_int ${arg.value})`);
            }
            else {
                return new SMTValue(this.isTypeExact(into) ? (arg as MIRConstantString).value : `(bsq_term_string ${(arg as MIRConstantString).value})`);
            }
        }
    }

    private static getExactTypeFrom(from: MIRType | MIRTypeOption): MIRTypeOption {
        return (from instanceof MIRType) ? from.options[0] : from;
    }

    coerceBoxIfNeeded(arg: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        assert(!this.isTypeExact(into));

        if (!this.isTypeExact(from)) {
            return arg;
        }
        else {
            const fromtype = SMTLIBGenerator.getExactTypeFrom(from);
            if (fromtype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(fromtype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTValue(`bsq_term_bool ${arg.emit()}`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int ${arg.emit()})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string ${arg.emit()})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- entity");
            }
            else if (fromtype instanceof MIRTupleType) {
                let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
                for (let i = 0; i < fromtype.entries.length; ++i) {
                    entriesval = `(store ${entriesval} ${i} (${this.typeToSMT2Constructor(fromtype)}@${i} ${arg}))`;
                }

                return new SMTValue(`(bsq_term_tuple ${fromtype.entries.length} ${entriesval})`);
            }
            else {
                assert(fromtype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- record");
            }
        }
    }

    coerceUnBoxIfNeeded(arg: SMTExp, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
        assert(this.isTypeExact(into));

        if (this.isTypeExact(from)) {
            return arg;
        }
        else {
            const intotype = SMTLIBGenerator.getExactTypeFrom(into);
            if (intotype instanceof MIREntityType) {
                const typedecl = this.assembly.entityDecls.get(intotype.ekey) as MIREntityTypeDecl;
                if (typedecl.ns === "NSCore") {
                    if (typedecl.name === "None") {
                        return arg;
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTValue(`(bsq_term_bool_value ${arg.emit()})`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int_value ${arg.emit()})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string_value ${arg.emit()})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- entity");
            }
            else if (intotype instanceof MIRTupleType) {
                let entriesval = [];
                for (let i = 0; i < intotype.entries.length; ++i) {
                    entriesval.push(`(select ${arg} ${i})`);
                }

                return new SMTValue(`(${this.typeToSMT2Constructor(intotype)} ${entriesval.join(" ")})`);
            }
            else {
                assert(intotype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- record");
            }
        }
    }

    private generateTruthyConvert(arg: MIRArgument, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(arg, vtypes);

        if (this.assembly.subtypeOf(argtype, this.noneType)) {
            return new SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.boolType)) {
            return this.argToSMT2Coerce(arg, argtype, this.boolType);
        }
        else {
            return new SMTCond(new SMTValue(`(= ${this.argToSMT2Direct(arg).emit()} bsq_term_none)`), new SMTValue("false"), this.argToSMT2Coerce(arg, argtype, this.boolType));
        }
    }

    private generateMIRConstructorPrimary(cp: MIRConstructorPrimary, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(cp.tkey) as MIREntityTypeDecl;
        const fvals = cp.args.map((arg, i) => {
            const argtype = this.getArgType(arg, vtypes);
            const ftype = this.assembly.typeMap.get(ctype.fields[i].declaredType) as MIRType;
            return this.argToSMT2Coerce(arg, argtype, ftype).emit();
        });

        const smtctype = this.typeToSMT2Constructor(this.assembly.typeMap.get(cp.tkey) as MIRType);
        const cexp = new SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        const bindexp = new SMTLet(this.varToSMT2Name(cp.trgt), cexp, this.generateFreeSMTVar());
        if (ctype.invariants.length === 0) {
            return bindexp;
        }
        else {
            const testexp = new SMTValue(`(${smtctype}@invariant ${this.varToSMT2Name(cp.trgt)})`);
            const resulttype = "Result_" + this.typeToSMT2Type(this.assembly.typeMap.get((this.cinvoke as MIRInvokeDecl).resultType) as MIRType);
            const errexp = new SMTValue(`(${resulttype}@result_with_code (result_error ${cp.sinfo.pos}))`);
            return bindexp.bind(new SMTCond(testexp, this.generateFreeSMTVar(), errexp));
        }
    }

    private generateMIRConstructorPrimaryCollectionEmpty(cpce: MIRConstructorPrimaryCollectionEmpty, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(((this.assembly.typeMap.get(cpce.tkey) as MIRType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        const smtctype = this.typeToSMT2Constructor(this.assembly.typeMap.get(cpce.tkey) as MIRType);
        if (ctype.name === "List") {
            if (this.isTypeExact(this.assembly.typeMap.get(cpce.tkey) as MIRType)) {
                return new SMTLet(this.varToSMT2Name(cpce.trgt), new SMTValue(`(${smtctype} 0 ${smtctype}@emptysingleton)`), this.generateFreeSMTVar());
            }
            else {
                return new SMTLet(this.varToSMT2Name(cpce.trgt), new SMTValue(`(bsq_term_list ${cpce.tkey} 0 ((as const (Array Int BTerm)) bsq_term_none))`), this.generateFreeSMTVar());
            }
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionEmpty -- Map");
        }
    }

    private generateMIRConstructorPrimaryCollectionSingletons(cpcs: MIRConstructorPrimaryCollectionSingletons, vtypes: Map<string, MIRType>): SMTExp {
        const ctype = this.assembly.entityDecls.get(((this.assembly.typeMap.get(cpcs.tkey) as MIRType).options[0] as MIREntityType).ekey) as MIREntityTypeDecl;
        if (ctype.name === "List") {
            const contentstype = ctype.terms.get("T") as MIRType;
            if (this.isTypeExact(this.assembly.typeMap.get(cpcs.tkey) as MIRType)) {
                const smtctype = this.typeToSMT2Constructor(this.assembly.typeMap.get(cpcs.tkey) as MIRType);
                let entriesval = `${smtctype}@emptysingleton`;
                for (let i = 0; i < cpcs.args.length; ++i) {
                    entriesval = `(store ${entriesval} ${i} ${this.argToSMT2Coerce(cpcs.args[i], this.getArgType(cpcs.args[i], vtypes), contentstype).emit()})`;
                }

                return new SMTLet(this.varToSMT2Name(cpcs.trgt), new SMTValue(`(${smtctype} ${cpcs.args.length} ${entriesval})`), this.generateFreeSMTVar());
            }
            else {
                let entriesval = `((as const (Array Int BTerm)) bsq_term_none)`;
                for (let i = cpcs.args.length - 1; i >= 0; --i) {
                    entriesval = `(store ${entriesval} ${i} ${this.argToSMT2Coerce(cpcs.args[i], this.getArgType(cpcs.args[i], vtypes), this.anyType).emit()})`;
                }

                return new SMTLet(this.varToSMT2Name(cpcs.trgt), new SMTValue(`(bsq_term_list "${SMTLIBGenerator.smtsanizite(cpcs.tkey)}" ${cpcs.args.length} ${entriesval})`), this.generateFreeSMTVar());
            }
        }
        else if (ctype.name === "Set") {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Set");
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRConstructorPrimaryCollectionSingletons -- Map");
        }
    }

    private generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): SMTExp {
        const restype = (this.assembly.typeMap.get(op.resultTupleType) as MIRType);
        assert(restype.options.length === 1 && restype.options[0] instanceof MIRTupleType);

        const ttype = restype.options[0] as MIRTupleType;
        const exacttrgt = this.isTypeExact(ttype);
        let tentries: string[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const argt = this.getArgType(op.args[i], vtypes);
            const tt = (exacttrgt && i < ttype.entries.length) ? ttype.entries[i].type : this.anyType;
            tentries.push(this.argToSMT2Coerce(op.args[i], argt, tt).emit());
        }

        if (exacttrgt) {
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(${this.typeToSMT2Constructor(ttype)} ${tentries.join(" ")})`), this.generateFreeSMTVar());
        }
        else {
            let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
            for (let i = 0; i < tentries.length; ++i) {
                entriesval = `(store ${entriesval} ${i} ${tentries[i]}))`;
            }

            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_term_tuple ${op.args.length} ${entriesval})`), this.generateFreeSMTVar());
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, resultAccessType: MIRType, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.isTypeExact(argtype)) {
            const tupinfo = argtype.options[0] as MIRTupleType;

            if (op.idx >= tupinfo.entries.length) {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue("bsq_term_none"), this.generateFreeSMTVar());
            }
            else {
                const fromtype = tupinfo.entries[op.idx].type;
                let access: SMTExp = new SMTValue(`(${this.typeToSMT2Constructor(argtype)}@${op.idx} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`);

                if (this.isTypeExact(resultAccessType)) {
                    return new SMTLet(this.varToSMT2Name(op.trgt), access, this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceBoxIfNeeded(access, fromtype, resultAccessType), this.generateFreeSMTVar());
                }
            }
        }
        else {
            const access = new SMTValue(`(select (bsq_term_tuple_entries ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) ${op.idx})`);
            if (!this.isTypeExact(resultAccessType)) {
                return new SMTLet(this.varToSMT2Name(op.trgt), access, this.generateFreeSMTVar());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceUnBoxIfNeeded(access, this.anyType, resultAccessType), this.generateFreeSMTVar());
            }
        }
    }

    generateMIRAccessFromField(op: MIRAccessFromField, resultAccessType: MIRType, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.isTypeExact(argtype)) {
            const tpfx = this.typeToSMT2Constructor(argtype);
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(${tpfx}@${op.field} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`), this.generateFreeSMTVar());
        }
        else {
            const access = new SMTValue(`(select (bsq_term_entity_entries ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) ${op.field})`);
            if (this.isTypeExact(resultAccessType)) {
                return new SMTLet(this.varToSMT2Name(op.trgt), this.coerceUnBoxIfNeeded(access, this.anyType, resultAccessType), this.generateFreeSMTVar());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), access, this.generateFreeSMTVar());
            }
        }
    }

    generateMIRModifyWithIndecies(mi: MIRModifyWithIndecies, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(mi.arg, vtypes);
        const restype = this.assembly.typeMap.get(mi.resultTupleType) as MIRType;

        if (this.isTypeExact(argtype) && this.isTypeExact(restype)) {
            const atinfo = argtype.options[0] as MIRTupleType;
            const rtinfo = restype.options[0] as MIRTupleType;

            let vals: string[] = [];
            for (let i = 0; i < rtinfo.entries.length; ++i) {
                const upd = mi.updates.find((up) => up[0] === i);
                if (upd !== undefined) {
                    vals.push(this.argToSMT2Coerce(upd[1], this.getArgType(upd[1], vtypes), rtinfo.entries[i].type).emit());
                }
                else if (i < atinfo.entries.length) {
                    vals.push(`(${this.typeToSMT2Constructor(argtype)}@${i} ${this.varToSMT2Name(mi.arg as MIRRegisterArgument)})`);
                }
                else {
                    vals.push("bsq_term_none");
                }
            }

            return new SMTLet(this.varToSMT2Name(mi.trgt), new SMTValue(`(${this.typeToSMT2Constructor(rtinfo)} ${vals.join(" ")})`), this.generateFreeSMTVar());
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRModifyWithIndecies -- not type exact case");
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, vtypes: Map<string, MIRType>): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT2Coerce(ivop.args[i], this.getArgType(ivop.args[i], vtypes), this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit());
        }

        const tv = `@tmpvar@${this.tmpvarctr++}`;
        const ivrtype = "Result_" + this.typeToSMT2Type(this.assembly.typeMap.get((idecl as MIRInvokeDecl).resultType) as MIRType);
        const resulttype = "Result_" + this.typeToSMT2Type(this.assembly.typeMap.get((this.cinvoke as MIRInvokeDecl).resultType) as MIRType);

        const invokeexp = new SMTValue(`(${this.invokenameToSMT2(ivop.mkey)} ${vals.join(" ")})`);
        const checkerror = new SMTValue(`(is-${ivrtype}@result_with_code ${tv})`);
        const extracterror = new SMTValue(`(${resulttype}@result_with_code (${ivrtype}@result_code_value ${tv}))`);
        const normalassign = new SMTLet(this.varToSMT2Name(ivop.trgt), new SMTValue(`(${resulttype}@result_value ${tv})`), this.generateFreeSMTVar());

        return new SMTLet(tv, invokeexp, new SMTCond(checkerror, extracterror, normalassign));
    }

    generateSMTScope(op: MIROp, vtypes: Map<string, MIRType>, fromblck: string): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                vtypes.set(lcv.trgt.nameID, this.getArgType(lcv.src, vtypes));
                return new SMTLet(this.varToSMT2Name(lcv.trgt), this.argToSMT2Direct(lcv.src), this.generateFreeSMTVar());
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
                vtypes.set(lav.trgt.nameID, this.getArgType(lav.name, vtypes));
                return new SMTLet(this.varToSMT2Name(lav.trgt), this.argToSMT2Direct(lav.name), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                vtypes.set(llv.trgt.nameID, this.getArgType(llv.name, vtypes));
                return new SMTLet(this.varToSMT2Name(llv.trgt), this.argToSMT2Direct(llv.name), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRConstructorPrimary: {
                const cp = op as MIRConstructorPrimary;
                vtypes.set(cp.trgt.nameID, this.assembly.typeMap.get(cp.tkey) as MIRType);
                return this.generateMIRConstructorPrimary(cp, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op as MIRConstructorPrimaryCollectionEmpty;
                vtypes.set(cpce.trgt.nameID, this.assembly.typeMap.get(cpce.tkey) as MIRType);
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op as MIRConstructorPrimaryCollectionSingletons;
                vtypes.set(cpcs.trgt.nameID, this.assembly.typeMap.get(cpcs.tkey) as MIRType);
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs, vtypes);
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionCopies");
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorPrimaryCollectionMixed");
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                vtypes.set(tc.trgt.nameID, this.assembly.typeMap.get(tc.resultTupleType) as MIRType);
                return this.generateMIRConstructorTuple(tc, vtypes);
            }
            case MIROpTag.MIRConstructorRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorRecord");
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                vtypes.set(ai.trgt.nameID, this.assembly.typeMap.get(ai.resultAccessType) as MIRType);
                return this.generateMIRAccessFromIndex(ai, this.assembly.typeMap.get(ai.resultAccessType) as MIRType, vtypes);
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
                const af = op as MIRAccessFromField;
                vtypes.set(af.trgt.nameID, this.assembly.typeMap.get(af.resultAccessType) as MIRType);
                return this.generateMIRAccessFromField(af, this.assembly.typeMap.get(af.resultAccessType) as MIRType, vtypes);
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
                const mi = op as MIRModifyWithIndecies;
                vtypes.set(mi.trgt.nameID, this.assembly.typeMap.get(mi.resultTupleType) as MIRType);
                return this.generateMIRModifyWithIndecies(mi, vtypes);
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
                vtypes.set(invk.trgt.nameID, this.assembly.typeMap.get(((this.assembly.invokeDecls.get(invk.mkey) || this.assembly.primitiveInvokeDecls.get(invk.mkey)) as MIRInvokeDecl).resultType) as MIRType);
                return this.generateMIRInvokeFixedFunction(invk, vtypes);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const argtype = this.getArgType(pfx.arg, vtypes);
                if (pfx.op === "!") {
                    vtypes.set(pfx.trgt.nameID, this.boolType);

                    const smttest = this.generateTruthyConvert(pfx.arg, vtypes);
                    return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(not ${smttest.emit()})`), this.generateFreeSMTVar());
                }
                else {
                    vtypes.set(pfx.trgt.nameID, this.intType);

                    if (pfx.op === "-") {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(* ${this.argToSMT2Coerce(pfx.arg, argtype, this.intType).emit()} -1)`), this.generateFreeSMTVar());
                    }
                    else {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), this.argToSMT2Coerce(pfx.arg, argtype, this.intType), this.generateFreeSMTVar());
                    }
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                vtypes.set(bop.trgt.nameID, this.intType);

                const lhvtype = this.getArgType(bop.lhs, vtypes);
                const lhv = this.argToSMT2Coerce(bop.lhs, lhvtype, this.intType).emit();

                const rhvtype = this.getArgType(bop.rhs, vtypes);
                const rhv = this.argToSMT2Coerce(bop.rhs, rhvtype, this.intType).emit();

                switch (bop.op) {
                    case "+":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(+ ${lhv} ${rhv})`), this.generateFreeSMTVar());
                    case "-":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(- ${lhv} ${rhv})`), this.generateFreeSMTVar());
                    case "*": {
                        if (bop.lhs instanceof MIRConstantArgument || bop.rhs instanceof MIRConstantArgument) {
                            return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(* ${lhv} ${rhv}`), this.generateFreeSMTVar());
                        }
                        else {
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear *");
                        }
                    }
                    case "/":
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear /");
                    default:
                            return NOT_IMPLEMENTED<SMTExp>("BINOP -- nonlinear %");
                }
            }
            case MIROpTag.MIRBinEq: {
                const beq = op as MIRBinEq;
                vtypes.set(beq.trgt.nameID, this.boolType);

                const lhvtype = this.getArgType(beq.lhs, vtypes);
                const rhvtype = this.getArgType(beq.rhs, vtypes);
                if (this.isTypeExact(lhvtype) && this.isTypeExact(rhvtype)) {
                    if ((lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool")
                        || (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int")
                        || (lhvtype.trkey === "NSCore::String" && rhvtype.trkey === "NSCore::String")) {
                            const smv = `(= ${this.argToSMT2Coerce(beq.lhs, lhvtype, lhvtype).emit()} ${this.argToSMT2Coerce(beq.rhs, rhvtype, rhvtype).emit()})`;
                            return new SMTLet(this.varToSMT2Name(beq.trgt), new SMTValue(beq.op === "!=" ? `(not ${smv})` : smv), this.generateFreeSMTVar());
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINEQ -- nonprimitive values");
                    }
                }
                else {
                    return NOT_IMPLEMENTED<SMTExp>("BINEQ -- nonexact");
                }
            }
            case MIROpTag.MIRBinCmp: {
                const bcmp = op as MIRBinCmp;
                vtypes.set(bcmp.trgt.nameID, this.boolType);

                const lhvtype = this.getArgType(bcmp.lhs, vtypes);
                const rhvtype = this.getArgType(bcmp.rhs, vtypes);

                if (this.isTypeExact(lhvtype) && this.isTypeExact(rhvtype)) {
                    if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
                        return new SMTLet(this.varToSMT2Name(bcmp.trgt), new SMTValue(`(${bcmp.op} ${this.argToSMT2Coerce(bcmp.lhs, lhvtype, lhvtype).emit()} ${this.argToSMT2Coerce(bcmp.rhs, rhvtype, rhvtype).emit()})`), this.generateFreeSMTVar());
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINCMP -- string");
                    }
                }
                else {
                    const trgttype = (this.assembly.subtypeOf(this.intType, lhvtype) && this.assembly.subtypeOf(this.intType, rhvtype)) ? this.intType : this.stringType;

                    const tvl = `@tmpl@${this.tmpvarctr++}`;
                    const tvr = `@tmpr@${this.tmpvarctr++}`;

                    const lets = new SMTLet(tvl, this.isTypeExact(lhvtype) ? this.argToSMT2Direct(bcmp.lhs) : this.argToSMT2Coerce(bcmp.lhs, lhvtype, trgttype),                     new SMTLet(tvr, this.isTypeExact(rhvtype) ? this.argToSMT2Direct(bcmp.rhs) : this.argToSMT2Coerce(bcmp.rhs, rhvtype, trgttype), this.generateFreeSMTVar()));
                    if (trgttype.trkey === "NSCore::Int") {
                        return lets.bind(new SMTLet(this.varToSMT2Name(bcmp.trgt), new SMTValue(`(${bcmp.op} ${tvl} ${tvr})`), this.generateFreeSMTVar()));
                    }
                    else {
                        return NOT_IMPLEMENTED<SMTExp>("BINCMP -- string");
                    }
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                vtypes.set(ton.trgt.nameID, this.boolType);

                const argtype = this.getArgType(ton.arg, vtypes);
                if (this.isTypeExact(argtype)) {
                    return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTValue(this.assembly.subtypeOf(argtype, this.noneType) ? "true" : "false"), this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTValue(`(= ${this.argToSMT2Direct(ton.arg).emit()} bsq_term_none)`), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                vtypes.set(tos.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);

                const argtype = this.getArgType(tos.arg, vtypes);
                if (this.isTypeExact(argtype)) {
                    return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTValue(this.assembly.subtypeOf(argtype, this.noneType) ? "false" : "true"), this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTValue(`(!= ${this.argToSMT2Direct(tos.arg).emit()} bsq_term_none)`), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<SMTExp>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                vtypes.set(regop.trgt.nameID, this.getArgType(regop.src, vtypes));

                return new SMTLet(this.varToSMT2Name(regop.trgt), this.argToSMT2Direct(regop.src), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                vtypes.set(tcop.trgt.nameID, this.boolType);

                const smttest = this.generateTruthyConvert(tcop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(tcop.trgt), smttest, this.generateFreeSMTVar());
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                vtypes.set(llop.trgt.nameID, this.boolType);

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToSMT2Coerce(llop.lhs, lhvtype, this.boolType).emit();

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToSMT2Coerce(llop.rhs, rhvtype, this.boolType).emit();

                if (llop.op === "&") {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(and ${lhv} ${rhv})`), this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(or ${lhv} ${rhv})`), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                vtypes.set(vsop.name.nameID, this.getArgType(vsop.src, vtypes));

                return new SMTLet(this.varToSMT2Name(vsop.name), this.argToSMT2Direct(vsop.src), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                vtypes.set(raop.name.nameID, this.assembly.typeMap.get((this.cinvoke as MIRInvokeDecl).resultType) as MIRType);

                const totype = vtypes.get(raop.name.nameID) as MIRType;
                const fromtype = this.getArgType(raop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(raop.name), this.argToSMT2Coerce(raop.src, fromtype, totype), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRAbort: {
                const aop = op as MIRAbort;
                const resulttype = "Result_" + this.typeToSMT2Type(this.assembly.typeMap.get((this.cinvoke as MIRInvokeDecl).resultType) as MIRType);
                return new SMTValue(`(${resulttype}@result_with_code (result_error ${aop.sinfo.pos}))`);
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const smttest = this.generateTruthyConvert(cjop.arg, vtypes);
                return new SMTCond(smttest, this.generateFreeSMTVar("#true_trgt#"), this.generateFreeSMTVar("#false_trgt#"));
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const argtype = this.getArgType(njop.arg, vtypes);
                if (this.isTypeExact(argtype)) {
                    return new SMTCond(new SMTValue(this.assembly.subtypeOf(argtype, this.noneType) ? "true" : "false"), this.generateFreeSMTVar("#true_trgt#"), this.generateFreeSMTVar("#false_trgt#"));
                }
                else {
                    return new SMTCond(new SMTValue(`(= ${this.argToSMT2Direct(njop.arg).emit()} bsq_term_none)`), this.generateFreeSMTVar("#true_trgt#"), this.generateFreeSMTVar("#false_trgt#"));
                }
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;
                vtypes.set(pop.trgt.nameID, this.getArgType(uvar, vtypes));

                return new SMTLet(this.varToSMT2Name(pop.trgt), this.argToSMT2Direct(uvar), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default:
                assert(false);
                return undefined;
        }
    }

    private generateSMTBlockExps(block: MIRBasicBlock, fromblock: string, blocks: Map<string, MIRBasicBlock>, vtypes: Map<string, MIRType>): SMTExp {
        const exps: SMTExp[] = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateSMTScope(block.ops[i], vtypes, fromblock);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }

        if (block.label === "exit") {
            const resulttype = "Result_" + this.typeToSMT2Type(this.assembly.typeMap.get((this.cinvoke as MIRInvokeDecl).resultType) as MIRType);
            let rexp = new SMTValue(`(${resulttype}@result_success _return_)`) as SMTExp;
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }

            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === MIROpTag.MIRJump) {
                let rexp = this.generateSMTBlockExps(blocks.get((jop as MIRJump).trgtblock) as MIRBasicBlock, block.label, blocks, vtypes);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
            else {
                assert(jop.tag === MIROpTag.MIRJumpCond || jop.tag === MIROpTag.MIRJumpNone);

                let tblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).trueblock) : blocks.get((jop as MIRJumpNone).noneblock)) as MIRBasicBlock;
                let texp = this.generateSMTBlockExps(tblock, block.label, blocks, new Map<string, MIRType>(vtypes));

                let fblock = ((jop.tag === MIROpTag.MIRJumpCond) ? blocks.get((jop as MIRJumpCond).falseblock) : blocks.get((jop as MIRJumpNone).someblock)) as MIRBasicBlock;
                let fexp = this.generateSMTBlockExps(fblock, block.label, blocks, new Map<string, MIRType>(vtypes));

                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }

                return rexp;
            }
        }
    }

    generateSMTInvoke(idecl: MIRInvokeDecl): string {
        this.cinvoke = idecl;

        let argvars = new Map<string, MIRType>();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type) as MIRType));

        const args = idecl.params.map((arg) => `(${this.varNameToSMT2Name(arg.name)} ${this.typeToSMT2Type(this.assembly.typeMap.get(arg.type) as MIRType)})`);
        const restype = this.typeToSMT2Type(this.assembly.typeMap.get(idecl.resultType) as MIRType);
        const decl = `(define-fun ${this.invokenameToSMT2(idecl.key)} (${args.join(" ")}) Result_${restype}`;

        if (idecl instanceof MIRInvokeBodyDecl) {
            if (idecl.preconditions.length !== 0 || idecl.postconditions.length !== 0) {
                return NOT_IMPLEMENTED<string>("generateSMTLetBody -- pre/post");
            }

            const blocks = (idecl as MIRInvokeBodyDecl).body.body;
            const body = this.generateSMTBlockExps(blocks.get("entry") as MIRBasicBlock, "[NO PREVIOUS]", blocks, argvars);
            return `${decl} \n${body.emit("  ")})`;
        }
        else {
            assert(idecl instanceof MIRInvokePrimitiveDecl);

            return (BuiltinCalls.get(((idecl as MIRInvokePrimitiveDecl).implkey)) as BuiltinCallEmit)(this, idecl as MIRInvokePrimitiveDecl, decl);
        }
    }

    generateSMTType(tdecl: MIRTypeOption): string {
        return NOT_IMPLEMENTED<string>("generateSMTType -- primitive");
    }

    static generateSMTAssembly(assembly: MIRAssembly): string {
        const smtgen = new SMTLIBGenerator(assembly);

        const typedecls: string[] = [];
        const consdecls: [string, string?][] = [];
        assembly.typeMap.forEach((type) => {
            if (smtgen.isTypeExact(type)) {
                const topt = type.options[0];
                if (topt instanceof MIREntityType) {
                    const edecl = assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                    if (edecl.ns === "NSCore" && (edecl.name === "None" || edecl.name === "Bool" || edecl.name === "Int" || edecl.name === "String")) {
                        //don't need to do anything as these are special cases
                    }
                    else if (edecl.isCollectionEntityType || edecl.isMapEntityType) {
                        typedecls.push(`(${smtgen.typeToSMT2Type(topt)} 0)`);
                        consdecls.push((BuiltinTypes.get(edecl.name) as BuiltinTypeEmit)(smtgen.typeToSMT2Constructor(topt), smtgen.typeToSMT2Type(edecl.terms.get("T") as MIRType)));
                    }
                    else {
                        typedecls.push(`(${smtgen.typeToSMT2Type(topt)} 0)`);

                        const tpfx = smtgen.typeToSMT2Constructor(topt);
                        const entries: string[] = [];
                        for (let i = 0; i < edecl.fields.length; ++i) {
                            const ftype = smtgen.assembly.typeMap.get(edecl.fields[i].declaredType) as MIRType;
                            entries.push(`(${tpfx}@${edecl.fields[i].name} ${smtgen.typeToSMT2Type(ftype)})`);
                        }

                        consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
                    }
                }
                else if (topt instanceof MIRTupleType ) {
                    typedecls.push(`(${smtgen.typeToSMT2Type(topt)} 0)`);

                    const tpfx = smtgen.typeToSMT2Constructor(topt);
                    const entries: string[] = [];
                    for (let i = 0; i < topt.entries.length; ++i) {
                        entries.push(`(${tpfx}@${i} ${smtgen.typeToSMT2Type(topt.entries[i].type)})`);
                    }

                    consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
                }
                else if (topt instanceof MIRRecordType) {
                    NOT_IMPLEMENTED<string>("generateSMTAssembly -- records");
                }
                else {
                    //don't need to do anything
                }
            }
        });

        const cginfo = constructCallGraphInfo(assembly.entryPoints, assembly.invokeDecls, assembly.primitiveInvokeDecls);
        assert(cginfo.recursive.length === 0, "TODO: we need to support recursion here");

        const invokedecls: string[] = [];
        const resultset = new Set<string>();
        const bupcg = [...cginfo.topologicalOrder].reverse();
        for (let i = 0; i < bupcg.length; ++i) {
            const idcl = (assembly.invokeDecls.get(bupcg[i].invoke) || assembly.primitiveInvokeDecls.get(bupcg[i].invoke)) as MIRInvokeDecl;
            invokedecls.push(smtgen.generateSMTInvoke(idcl));

            resultset.add(smtgen.typeToSMT2Type(assembly.typeMap.get(idcl.resultType) as MIRType));
        }

        const resultarr = [...resultset];
        const resultdecls = resultarr.map((rd) => `(Result_${rd} 0)`);
        const resultcons = resultarr.map((rd) => `( (Result_${rd}@result_with_code (Result_${rd}@result_code_value ResultCode)) (Result_${rd}@result_success (Result_${rd}@result_value ${rd})) )`);

        return smt_header
        + "\n\n"
        + smtlib_code
        + "\n\n"
        + `${consdecls.map((cd) => cd[1]).filter((d) => d !== undefined).join("\n")}`
        + "\n\n"
        + `(declare-datatypes (${typedecls.join("\n")}) (\n${consdecls.map((cd) => cd[0]).join("\n")}\n))`
        + "\n\n"
        + `(declare-datatypes (${resultdecls.join("\n")}) (\n${resultcons.join("\n")}\n))`
        + "\n\n"
        + invokedecls.join("\n\n")
        + "\n\n";
    }
}

export {
    SMTValue, SMTLet, SMTCond, SMTExp,
    SMTLIBGenerator
};
