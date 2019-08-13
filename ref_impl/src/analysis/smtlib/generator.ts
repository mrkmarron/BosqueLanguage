//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex, MIRConstantTrue, MIRConstantFalse, MIRConstantNone, MIRConstantInt, MIRConstantString, MIRValueOp, MIRVariable, MIRPrefixOp, MIRConstantArgument, MIRBinOp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore, MIRVarStore, MIRReturnAssign, MIRAbort, MIRJumpCond, MIRJumpNone, MIRBinEq, MIRBinCmp, MIRModifyWithIndecies, MIRInvokeFixedFunction, MIRInvokeKey, MIRBasicBlock, MIRPhi, MIRTempRegister } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType, MIRTypeOption, MIREntityTypeDecl, MIREntityType, MIRRecordType, MIRInvokeDecl, MIRConceptType } from "../../compiler/mir_assembly";

function NOT_IMPLEMENTED<T>(action: string): T {
    throw new Error(`Not Implemented: ${action}`);
}

const smt_header = `
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
`;

const smtlib_code = `
(declare-datatypes ( (BTerm 0) ) (
    ( (bsq_term_none) (bsq_term_bool (bsq_term_bool_value Bool)) (bsq_term_int (bsq_term_int_value Int)) (bsq_term_string (bsq_term_string_value String)) 
      (bsq_term_tuple (bsq_term_tuple_size Int) (bsq_term_tuple_entries (Array Int BTerm)))
      (bsq_term_record (bsq_term_record_size Int) (bsq_term_record_properties (Array Int String)) (bsq_term_record_entries (Array String BTerm)))
      (bsq_term_entity (bsq_term_entity_type String) (bsq_term_entity_entries (Array String BTerm)))
    )
))

(declare-datatypes ( (ResultCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( (Result 1)
                     ) (
    (par (T) ((result_with_code (result_code_value ResultCode)) (result_success (result_value T)) ))
))
`;

abstract class SMTExp {
    abstract bind(sval: SMTExp, svar?: string): SMTExp;
    abstract emit(indent: string | undefined): string;
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

    emit(indent: string | undefined): string {
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

    emit(indent: string | undefined): string {
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

    emit(indent: string | undefined): string {
        if (indent === undefined) {
            return `(let ((${this.lname} ${this.exp.emit(undefined)})) ${this.body.emit(undefined)})`;
        }
        else {
            return `(let ((${this.lname} ${this.exp.emit(undefined)}))\n${indent + "  "}${this.body.emit(indent + "  ")}\n${indent})`;
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
            return `(ite ${this.test.emit(undefined)} ${this.iftrue.emit(undefined)} ${this.iffalse.emit(undefined)})`;
        }
        else {
            return `(ite ${this.test.emit(undefined)}\n${indent + "  "}\n${this.iftrue.emit(indent + "  ")}\n${indent + "  "}${this.iffalse.emit(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTLIBGenerator {
    readonly assembly: MIRAssembly;
    readonly sanitychk: boolean;

    constructor(assembly: MIRAssembly, sanitychk: boolean) {
        this.assembly = assembly;
        this.sanitychk = sanitychk;
    }

    private getArgType(arg: MIRArgument, vtypes: Map<string, MIRType>): MIRType {
        if (arg instanceof MIRRegisterArgument) {
            return vtypes.get(arg.nameID) as MIRType;
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return this.assembly.typeMap.get("NSCore::None") as MIRType;
            }
            else if (arg instanceof MIRConstantTrue || arg instanceof MIRConstantFalse) {
                return this.assembly.typeMap.get("NSCore::Bool") as MIRType;
            }
            else if (arg instanceof MIRConstantInt) {
                return this.assembly.typeMap.get("NSCore::Int") as MIRType;
            }
            else {
                return this.assembly.typeMap.get("NSCore::String<NSCore::Any>") as MIRType;
            }
        }
    }

    private isTypeExact(type: MIRType | MIRTypeOption): boolean {
        if (type instanceof MIRType) {
            return type.options.length === 1 && this.isTypeExact(type.options[0]);
        }

        if (type instanceof MIREntityType) {
            if (type.ekey === "NSCore::String<NSCore::Any>") {
                return true;
            }
            else {
                let allexact = true;
                (this.assembly.entityDecls.get(type.ekey) as MIREntityTypeDecl).terms.forEach((term) => {
                    allexact = allexact && this.isTypeExact(term);
                });
                return allexact;
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

    private typeToSMT2(type: MIRType | MIRTypeOption): string {
        return type.trkey.replace(/::/g, "@");
    }

    private invokenameToSMT2(ivk: MIRInvokeKey): string {
        return ivk.replace(/::/g, "@");
    }

    private generateFreeSMTVar(name?: string): SMTFreeVar {
        return new SMTFreeVar(`free@${name || "body"}`);
    }

    private varToSMT2Name(varg: MIRRegisterArgument): string {
        return varg.nameID;
    }

    private argToSMT2Exact(arg: MIRArgument): SMTExp {
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

    private argToSMT2Term(arg: MIRArgument): SMTExp {
        if (arg instanceof MIRRegisterArgument) {
            return new SMTValue(this.varToSMT2Name(arg));
        }
        else {
            if (arg instanceof MIRConstantNone) {
                return new SMTValue("bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue("(bsq_term_bool true)");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue("(bsq_term_bool false)");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(`(bsq_term_int ${arg.value})`);
            }
            else {
                return new SMTValue(`(bsq_term_string ${(arg as MIRConstantString).value})`);
            }
        }
    }

    private argToSMT2Coerce(arg: MIRArgument, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
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

    private coerceBoxIfNeeded(arg: SMTValue, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
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
                        return new SMTValue(`bsq_term_bool ${arg}`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int ${arg})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string ${arg})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- entity");
            }
            else if (fromtype instanceof MIRTupleType) {
                let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
                for (let i = 0; i < fromtype.entries.length; ++i) {
                    entriesval = `(store ${entriesval} ${i} (bsq_tuple@${this.typeToSMT2(fromtype)}@${i} ${arg}))`;
                }

                return new SMTValue(`(bsq_term_tuple ${fromtype.entries.length} ${entriesval})`);
            }
            else {
                assert(fromtype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceBoxIfNeeded -- record");
            }
        }
    }

    private coerceUnBoxIfNeeded(arg: SMTValue, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
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
                        return new SMTValue(`(bsq_term_bool_value ${arg})`);
                    }
                    if (typedecl.name === "Int") {
                        return new SMTValue(`(bsq_term_int_value ${arg})`);
                    }
                    if (typedecl.name === "String") {
                        return new SMTValue(`(bsq_term_string_value ${arg})`);
                    }
                }

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- entity");
            }
            else if (intotype instanceof MIRTupleType) {
                let entriesval = [];
                for (let i = 0; i < intotype.entries.length; ++i) {
                    entriesval.push(`(select ${arg} ${i})`);
                }

                return new SMTValue(`(bsq_tuple@${this.typeToSMT2(intotype)} ${entriesval.join(" ")})`);
            }
            else {
                assert(intotype instanceof MIRRecordType);

                return NOT_IMPLEMENTED<SMTExp>("coerceUnBoxIfNeeded -- record");
            }
        }
    }

    private generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): SMTExp {
        const restype = (this.assembly.typeMap.get(op.resultTupleType) as MIRType);
        assert(restype.options.length === 1 && restype.options[0] instanceof MIRTupleType);

        const ttype = restype.options[0] as MIRTupleType;
        let tentries: SMTExp[] = [];
        for (let i = 0; i < op.args.length; ++i) {
            const argt = this.getArgType(op.args[i], vtypes);
            const tt = ttype.entries.length < i ? ttype.entries[i].type : this.assembly.typeMap.get("NSCore::Any") as MIRType;
            tentries.push(this.argToSMT2Coerce(op.args[i], argt, tt));
        }

        if (this.isTypeExact(ttype)) {
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_tuple@${this.typeToSMT2(ttype)} ${tentries.join(" ")}})`), this.generateFreeSMTVar());
        }
        else {
            let entriesval = "((as const (Array Int BTerm)) bsq_term_none)";
            for (let i = 0; i < tentries.length; ++i) {
                entriesval = `(store ${entriesval} ${i} ${tentries[i]}))`;
            }

            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_term_tuple ${op.args.length} ${entriesval})`), this.generateFreeSMTVar());
        }
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = this.getArgType(op.arg, vtypes);

        if (this.isTypeExact(argtype)) {
            const tupinfo = argtype.options[0] as MIRTupleType;

            if (op.idx >= tupinfo.entries.length) {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue("bsq_term_none"), this.generateFreeSMTVar());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_tuple@${this.typeToSMT2(argtype)}@${op.idx} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`), this.generateFreeSMTVar());
            }
        }
        else {
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(select (${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) ${op.idx})`), this.generateFreeSMTVar());
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
                    vals.push(this.argToSMT2Exact(upd[1]).emit(undefined));
                }
                else if (i < atinfo.entries.length) {
                    vals.push(`(bsq_tuple@${this.typeToSMT2(argtype)}@${i} ${this.varToSMT2Name(mi.arg as MIRRegisterArgument)})`);
                }
                else {
                    vals.push("bsq_term_none");
                }
            }

            return new SMTLet(this.varToSMT2Name(mi.trgt), new SMTValue(`(bsq_tuple@${this.typeToSMT2(rtinfo)} ${vals.join(" ")}})`), this.generateFreeSMTVar());
        }
        else {
            return NOT_IMPLEMENTED<SMTExp>("generateMIRModifyWithIndecies -- not type exact case");
        }
    }

    generateMIRInvokeFixedFunction(ivop: MIRInvokeFixedFunction, vtypes: Map<string, MIRType>): SMTExp {
        let vals: string[] = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey)) as MIRInvokeDecl;

        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT2Coerce(ivop.args[i], this.getArgType(ivop.args[i], vtypes), this.assembly.typeMap.get(idecl.params[i].type) as MIRType).emit(undefined));
        }

        return new SMTLet(this.varToSMT2Name(ivop.trgt), new SMTValue(`(${this.invokenameToSMT2(ivop.mkey)} ${vals.join(" ")})`), new SMTCond(new SMTValue(`((_ is result_with_code) ${this.varToSMT2Name(ivop.trgt)})`), new SMTValue(this.varToSMT2Name(ivop.trgt)), this.generateFreeSMTVar()));
    }

    generateSMTScope(op: MIROp, vtypes: Map<string, MIRType>, fromblck: string): SMTExp | undefined {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                vtypes.set(lcv.trgt.nameID, this.getArgType(lcv.src, vtypes));
                return new SMTLet(this.varToSMT2Name(lcv.trgt), this.argToSMT2Exact(lcv.src), this.generateFreeSMTVar());
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
                xxxx;
                const lav = (op as MIRAccessArgVariable);
                const totype = vtypes.get(lav.trgt.nameID) as MIRType;
                const fromtype = this.getArgType(lav.name, vtypes);
                return new SMTLet(this.varToSMT2Name(lav.trgt), this.argToSMT2(lav.name, fromtype, totype), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                const totype = vtypes.get(llv.trgt.nameID) as MIRType;
                const fromtype = this.getArgType(llv.name, vtypes);
                return new SMTLet(this.varToSMT2Name(llv.trgt), this.argToSMT2(llv.name, fromtype, totype), this.generateFreeSMTVar());
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
                return this.generateMIRConstructorTuple(tc, vtypes);
            }
            case MIROpTag.MIRConstructorRecord: {
                return NOT_IMPLEMENTED<SMTExp>("MIRConstructorRecord");
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return this.generateMIRAccessFromIndex(ai, vtypes);
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
                const mi = op as MIRModifyWithIndecies;
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
                return this.generateMIRInvokeFixedFunction(invk, vtypes);
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED<SMTExp>("MIRInvokeVirtualTarget");
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                const argtype = this.getArgType(pfx.arg, vtypes);
                if (pfx.op === "!") {
                    const totype = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
                    if (this.assembly.subtypeOf(argtype, totype)) {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(not ${this.argToSMT2(pfx.arg, argtype, totype)})`), this.generateFreeSMTVar());
                    }
                    else {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(pfx.arg, argtype, argtype)} bsq_term_none)`), new SMTValue("false"), new SMTValue(`(not ${this.argToSMT2(pfx.arg, argtype, totype)})`)), this.generateFreeSMTVar());
                    }
                }
                else if (pfx.op === "-") {
                    const totype = this.assembly.typeMap.get("NSCore::Int") as MIRType;
                    return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTValue(`(* ${this.argToSMT2(pfx.arg, argtype, totype)} -1)`), this.generateFreeSMTVar());
                }
                else {
                    const totype = this.assembly.typeMap.get("NSCore::Int") as MIRType;
                    return new SMTLet(this.varToSMT2Name(pfx.trgt), this.argToSMT2(pfx.arg, argtype, totype), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                const totype = this.assembly.typeMap.get("NSCore::Int") as MIRType;

                const lhvtype = this.getArgType(bop.lhs, vtypes);
                const lhv = this.argToSMT2(bop.lhs, lhvtype, totype);

                const rhvtype = this.getArgType(bop.rhs, vtypes);
                const rhv = this.argToSMT2(bop.rhs, rhvtype, totype);

                switch (bop.op) {
                    case "+":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(+ ${lhv} ${rhv}`), this.generateFreeSMTVar());
                    case "-":
                        return new SMTLet(this.varToSMT2Name(bop.trgt), new SMTValue(`(- ${lhv} ${rhv}`), this.generateFreeSMTVar());
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
                const lhvtype = this.getArgType(beq.lhs, vtypes);
                const rhvtype = this.getArgType(beq.rhs, vtypes);
                if (this.isTypeExact(lhvtype) && this.isTypeExact(rhvtype)) {
                    if ((lhvtype.trkey === "NSCore::Bool" && rhvtype.trkey === "NSCore::Bool")
                        || (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int")
                        || (lhvtype.trkey === "NSCore::String<NSCore::Any>" && rhvtype.trkey === "NSCore::String<NSCore::Any>")) {
                            const smv = `(= ${this.argToSMT2(beq.lhs, lhvtype, lhvtype)} ${this.argToSMT2(beq.rhs, rhvtype, rhvtype)})`;
                            return new SMTValue(beq.op === "!=" ? `(not ${smv})` : smv);
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
                const lhvtype = this.getArgType(bcmp.lhs, vtypes);
                const rhvtype = this.getArgType(bcmp.rhs, vtypes);
                assert(this.isTypeExact(lhvtype) && this.isTypeExact(rhvtype)); //should be both int or string

                if (lhvtype.trkey === "NSCore::Int" && rhvtype.trkey === "NSCore::Int") {
                    return new SMTValue(`(${bcmp.op} ${this.argToSMT2(bcmp.lhs, lhvtype, lhvtype)} ${this.argToSMT2(bcmp.rhs, rhvtype, rhvtype)})`)
                }
                else {
                    return NOT_IMPLEMENTED<SMTExp>("BINCMP -- string");
                }
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                const argtype = this.getArgType(ton.arg, vtypes);
                assert(!this.isTypeExact(argtype)); //?? shouldn't we report this as a dead branch in the type checker ??

                return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTValue(`(= ${this.argToSMT2(ton.arg, argtype, argtype)} bsq_term_none)`), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                const argtype = this.getArgType(tos.arg, vtypes);
                assert(!this.isTypeExact(argtype)); //?? shouldn't we report this as a dead branch in the type checker ??

                return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTValue(`(!= ${this.argToSMT2(tos.arg, argtype, argtype)} bsq_term_none)`), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRIsTypeOf: {
                return NOT_IMPLEMENTED<SMTExp>("MIRIsTypeOf");
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                const totype = vtypes.get(regop.trgt.nameID) as MIRType;
                const fromtype = this.getArgType(regop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(regop.trgt), this.argToSMT2(regop.src, fromtype, totype), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                const argtype = this.getArgType(tcop.src, vtypes);
                const totype = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
                assert(!this.assembly.subtypeOf(argtype, totype)); //?? why are we emitting this then ??

                return new SMTLet(this.varToSMT2Name(tcop.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(tcop.src, argtype, argtype)} bsq_term_none)`), new SMTValue("false"), this.argToSMT2(tcop.src, argtype, totype)), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                const totype = this.assembly.typeMap.get("NSCore::Bool") as MIRType;

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToSMT2(llop.lhs, lhvtype, totype);

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToSMT2(llop.rhs, rhvtype, totype);

                if (llop.op === "&") {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(and ${lhv} ${rhv})`), this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(or ${lhv} ${rhv})`), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRVarStore: {
                const vsop = op as MIRVarStore;
                const totype = vtypes.get(vsop.name.nameID) as MIRType;
                const fromtype = this.getArgType(vsop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(vsop.name), this.argToSMT2(vsop.src, fromtype, totype), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRReturnAssign: {
                const raop = op as MIRReturnAssign;
                const totype = vtypes.get(raop.name.nameID) as MIRType;
                const fromtype = this.getArgType(raop.src, vtypes);
                return new SMTLet(this.varToSMT2Name(raop.name), this.argToSMT2(raop.src, fromtype, totype), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRAbort: {
                const aop = op as MIRAbort;
                return new SMTValue(`(result_with_code (result_error ${aop.sinfo.pos}))`);
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                const argtype = this.getArgType(cjop.arg, vtypes);
                const totype = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
                if (this.assembly.subtypeOf(argtype, totype)) {
                    return new SMTCond(this.argToSMT2(cjop.arg, argtype, totype), this.generateFreeSMTVar("true"), this.generateFreeSMTVar("false"));
                }
                else {
                    return new SMTCond(new SMTCond(new SMTValue(`(= ${this.argToSMT2(cjop.arg, argtype, argtype)} bsq_term_none)`), new SMTValue("false"), this.argToSMT2(cjop.arg, argtype, totype)), this.generateFreeSMTVar("true"), this.generateFreeSMTVar("false"));
                }
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                const argtype = this.getArgType(njop.arg, vtypes);
                assert(!this.isTypeExact(argtype)); //?? shouldn't we report this as a dead branch in the type checker ??

                return new SMTCond(new SMTValue(`(= ${this.argToSMT2(njop.arg, argtype, argtype)} bsq_term_none)`), this.generateFreeSMTVar("true"), this.generateFreeSMTVar("false"));
            }
            case MIROpTag.MIRPhi: {
                const pop = op as MIRPhi;
                const uvar = pop.src.get(fromblck) as MIRRegisterArgument;
                if (pop.trgt instanceof MIRTempRegister) {
                    fscope.assignTmpReg(pop.trgt.regID, this.getArgValue(fscope, uvar));
                }
                else {
                    assert(pop.trgt instanceof MIRVariable);

                    fscope.assignVar(pop.trgt.nameID, this.getArgValue(fscope, uvar));
                }
                break;
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

    private generateSMTBlockExps(blck: MIRBasicBlock, fromblck: string, blocks: Map<string, MIRBasicBlock>, vtypes: Map<string, MIRType>): SMTExp[] {
        if(blck.label === "exit") {
            xxxx;
        }

        const exps: SMTExp[] = [];
        for (let i = 0; i < block.length; ++i) {
            this.evaluateOP(block[i], fscope);
        }
    }

    generateSMTLetBody(idecl: MIRInvokeDecl): SMTExp {
    }
}

export {
    SMTLIBGenerator
};
