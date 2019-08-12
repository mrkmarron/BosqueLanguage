//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex, MIRConstantTrue, MIRConstantFalse, MIRConstantNone, MIRConstantInt, MIRConstantString, MIRValueOp, MIRVariable, MIRPrefixOp, MIRConstantArgument, MIRBinOp, MIRIsTypeOfNone, MIRIsTypeOfSome, MIRRegAssign, MIRTruthyConvert, MIRLogicStore } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType, MIRTypeOption, MIREntityTypeDecl, MIREntityType, MIRRecordType } from "../../compiler/mir_assembly";

function NOT_IMPLEMENTED<T>(action: string): T {
    throw new Error(`Not Implemented: ${action}`);
}

const smt_header = `
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
`;

const exact_values_template = `
`;

const general_values = `
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

    private freevarctr = 0;

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
        xxxx;
    }

    private typeToSMT2(type: MIRType | MIRTypeOption): string {
        xxxx;
    }

    private generateFreeSMTVar(): SMTFreeVar {
        return new SMTFreeVar(`@freevar${this.freevarctr++}`);
    }

    private varToSMT2Name(varg: MIRRegisterArgument): string {
        return varg.nameID;
    }

    private argToSMT2(arg: MIRArgument, from: MIRType | MIRTypeOption, into: MIRType | MIRTypeOption): SMTExp {
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
                return new SMTValue(this.isTypeExact(into) ? "bsq_none" : "bsq_term_none");
            }
            else if (arg instanceof MIRConstantTrue) {
                return new SMTValue(this.isTypeExact(into) ? "bsq_true" : "bsq_term_true");
            }
            else if (arg instanceof MIRConstantFalse) {
                return new SMTValue(this.isTypeExact(into) ? "bsq_false" : "bsq_term_false");
            }
            else if (arg instanceof MIRConstantInt) {
                return new SMTValue(this.isTypeExact(into) ? `(bsq_int ${arg.value})` : `(bsq_term_int ${arg.value})`);
            }
            else {
                return new SMTValue(this.isTypeExact(into) ? `(bsq_string ${(arg as MIRConstantString).value})` : `(bsq_term_string ${(arg as MIRConstantString).value})`);
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
                        return new SMTValue("bsq_term_none");
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTCond(new SMTValue(`(= ${arg} bsq_true)`), new SMTValue("bsq_term_true"), new SMTValue("bsq_term_false"));
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
                        return new SMTValue("bsq_none");
                    }
                    if (typedecl.name === "Bool") {
                        return new SMTCond(new SMTValue(`(= ${arg} bsq_term_true)`), new SMTValue("bsq_true"), new SMTValue("bsq_false"));
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

    private createTuple(args: MIRArgument[], ttype: MIRTupleType, vtypes: Map<string, MIRType>): SMTValue {
        let tentries: SMTExp[] = [];
        for (let i = 0; i < args.length; ++i) {
            const argt = this.getArgType(args[i], vtypes);
            const tt = ttype.entries.length < i ? ttype.entries[i].type : this.assembly.typeMap.get("NSCore::Any") as MIRType;
            tentries.push(this.argToSMT2(args[i], argt, tt));
        }

        if (this.isTypeExact(ttype)) {
            return new SMTValue(`(bsq_tuple@${this.typeToSMT2(ttype)} ${tentries.join(" ")}})`);
        }
        else {
            return new SMTValue(`(bsq_term_tuple ${args.length} ${tentries.join(" ")}})`);
        }
    }

    private generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): SMTExp {
        const ttype = (this.assembly.typeMap.get(op.getValueOpTypeKey()) as MIRType);
        assert(ttype.options.length === 1 && ttype.options[0] instanceof MIRTupleType);

        return new SMTLet(this.varToSMT2Name(op.trgt), this.createTuple(op.args, ttype.options[0] as MIRTupleType, vtypes), this.generateFreeSMTVar());
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = vtypes.get(op.arg.nameID) as MIRType;

        if (this.isTypeExact(argtype)) {
            const tupinfo = argtype.options[0] as MIRTupleType;

            if (op.idx >= tupinfo.entries.length) {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue("bsq_none"), this.generateFreeSMTVar());
            }
            else {
                return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(`(bsq_tuple@${this.typeToSMT2(argtype)}@${op.idx} ${this.varToSMT2Name(op.arg as MIRRegisterArgument)})`), this.generateFreeSMTVar());
            }
        }
        else {
            return new SMTCond(new SMTValue(`(>= ${op.idx} (bsq_term_tuple_size ${this.varToSMT2Name(op.arg as MIRRegisterArgument)}))`), new SMTValue("bsq_term_none"), new SMTValue(`(select (${this.varToSMT2Name(op.arg as MIRRegisterArgument)}) ${op.idx})`));
        }
    }

    private updatevtypeMap(op: MIROp, vtypes: Map<string, MIRType>) {
        if (op instanceof MIRValueOp) {
            vtypes.set(op.trgt.nameID, this.assembly.typeMap.get(op.getValueOpTypeKey()) as MIRType);
        }
        else {
            switch (op.tag) {
                case MIROpTag.MIRRegAssign: {
                    const rop = op as MIRRegAssign;
                    vtypes.set(rop.trgt.nameID, this.getArgType(rop.src, vtypes));
                }
                case MIROpTag.MIRTruthyConvert:  {
                    const top = op as MIRTruthyConvert;
                    vtypes.set(top.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);
                }
                case MIROpTag.MIRLogicStore: {
                    const top = op as MIRLogicStore;
                    vtypes.set(top.trgt.nameID, this.assembly.typeMap.get("NSCore::Bool") as MIRType);
                }
                default:
                    xxxx;
            }
        }
    }

    generateSMTScope(op: MIROp, vtypes: Map<string, MIRType>): SMTExp | undefined {
        this.updatevtypeMap(op, vtypes);

        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                const totype = vtypes.get(lcv.trgt.nameID) as MIRType;
                const fromtype = this.getArgType(lcv.src, vtypes);
                return new SMTLet(this.varToSMT2Name(lcv.trgt), this.argToSMT2(lcv.src, fromtype, totype), this.generateFreeSMTVar());
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
                mi.arg = processSSA_Use(mi.arg, remap);
                mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
                processValueOpTempSSA(mi, remap, ctrs);
                break;
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
                invk.args = processSSAUse_RemapArgs(invk.args, remap);
                processValueOpTempSSA(invk, remap, ctrs);
                break;
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
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(pfx.arg, argtype, totype)} bsq_true)`), new SMTValue("bsq_false"), new SMTValue("bsq_true")), this.generateFreeSMTVar());
                    }
                    else {
                        return new SMTLet(this.varToSMT2Name(pfx.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(pfx.arg, argtype, argtype)} bsq_term_none)`), new SMTValue("bsq_false"), new SMTCond(new SMTValue(`(= ${this.argToSMT2(pfx.arg, argtype, argtype)} bsq_term_true)`), new SMTValue("bsq_false"), new SMTValue("bsq_true"))), this.generateFreeSMTVar());
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
                beq.lhs = processSSA_Use(beq.lhs, remap);
                beq.rhs = processSSA_Use(beq.rhs, remap);
                processValueOpTempSSA(beq, remap, ctrs);
                break;
            }
            case MIROpTag.MIRBinCmp: {
                const bcp = op as MIRBinCmp;
                bcp.lhs = processSSA_Use(bcp.lhs, remap);
                bcp.rhs = processSSA_Use(bcp.rhs, remap);
                processValueOpTempSSA(bcp, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const ton = op as MIRIsTypeOfNone;
                const argtype = this.getArgType(ton.arg, vtypes);
                assert(!this.isTypeExact(argtype)); //?? shouldn't we report this as a dead branch in the type checker ??

                return new SMTLet(this.varToSMT2Name(ton.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(ton.arg, argtype, argtype)} bsq_term_none)`), new SMTValue("bsq_true"), new SMTValue("bsq_false")), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                const argtype = this.getArgType(tos.arg, vtypes);
                assert(!this.isTypeExact(argtype)); //?? shouldn't we report this as a dead branch in the type checker ??

                return new SMTLet(this.varToSMT2Name(tos.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(tos.arg, argtype, argtype)} bsq_term_none)`), new SMTValue("bsq_false"), new SMTValue("bsq_true")), this.generateFreeSMTVar());
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

                return new SMTLet(this.varToSMT2Name(tcop.trgt), new SMTCond(new SMTValue(`(= ${this.argToSMT2(tcop.src, argtype, argtype)} bsq_term_none)`), new SMTValue("bsq_false"), this.argToSMT2(tcop.src, argtype, totype)), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                const totype = this.assembly.typeMap.get("NSCore::Int") as MIRType;

                const lhvtype = this.getArgType(llop.lhs, vtypes);
                const lhv = this.argToSMT2(llop.lhs, lhvtype, totype);

                const rhvtype = this.getArgType(llop.rhs, vtypes);
                const rhv = this.argToSMT2(llop.rhs, rhvtype, totype);

                if (llop.op === "&") {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(and (= ${lhv} bsq_true) (= ${rhv} bsq_true))`), this.generateFreeSMTVar());
                }
                else {
                    return new SMTLet(this.varToSMT2Name(llop.trgt), new SMTValue(`(or (= ${lhv} bsq_true) (= ${rhv} bsq_true))`), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRVarStore: {
                const vs = op as MIRVarStore;
                vs.src = processSSA_Use(vs.src, remap);
                vs.name = convertToSSA(vs.name, remap, ctrs) as MIRVariable;
                break;
            }
            case MIROpTag.MIRReturnAssign: {
                const ra = op as MIRReturnAssign;
                ra.src = processSSA_Use(ra.src, remap);
                ra.name = convertToSSA(ra.name, remap, ctrs) as MIRVariable;
                break;
            }
            case MIROpTag.MIRAbort: {
                xxxx;
                break;
            }
            case MIROpTag.MIRDebug: {
                return undefined;
            }
            case MIROpTag.MIRJump: {
                return undefined;
            }
            case MIROpTag.MIRJumpCond: {
                const cjop = op as MIRJumpCond;
                cjop.arg = processSSA_Use(cjop.arg, remap);
                break;
            }
            case MIROpTag.MIRJumpNone: {
                const njop = op as MIRJumpNone;
                njop.arg = processSSA_Use(njop.arg, remap);
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
}

export {
    SMTLIBGenerator
};
