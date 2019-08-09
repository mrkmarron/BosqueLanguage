//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIROp, MIROpTag, MIRLoadConst, MIRArgument, MIRRegisterArgument, MIRAccessArgVariable, MIRAccessLocalVariable, MIRConstructorTuple, MIRAccessFromIndex, MIRConstantTrue, MIRConstantFalse, MIRConstantNone, MIRConstantInt, MIRConstantString, MIRValueOp, MIRVariable, MIRPrefixOp } from "../../compiler/mir_ops";
import { MIRType, MIRAssembly, MIRTupleType } from "../../compiler/mir_assembly";

function NOT_IMPLEMENTED(action: string): never {
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

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;
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

    private isTypeExact(type: MIRType): boolean {
        xxxx;
    }

    private typeToSMT2(type: MIRType): string {
        xxxx;
    }

    private varToSMT2Name(varg: MIRRegisterArgument): string {
        return varg.nameID;
    }

    private argToSMT2(arg: MIRArgument, into: MIRType, vtypes: Map<string, MIRType>): SMTValue {
        if (arg instanceof MIRRegisterArgument) {
            if (this.isTypeExact(into)) {
                return this.coerceUnBoxIfNeeded(arg, into, vtypes);
            }
            else {
                return this.coerceUnBoxIfNeeded(arg, into, vtypes);
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

    private generateFreeSMTVar(): SMTFreeVar {
        xxxx;
    }

    private coerceBoxIfNeeded(arg: MIRArgument, into: MIRType, vtypes: Map<string, MIRType>): SMTValue {
        assert(!this.isTypeExact(into));

        const argt = this.getArgType(arg, vtypes);
        if (!this.isTypeExact(argt)) {
            return new SMTValue(arg.nameID);
        }
        else {
            if(argt)
            (bsq_term_none) (bsq_term_bool (bsq_term_bool_value BBool)) (bsq_term_int (bsq_term_int_value BInt)) (bsq_term_string (bsq_term_string_value BString)) (bsq_term_tuple (bsq_term_tuple_value BTuple))
        }
    }

    private coerceUnBoxIfNeeded(arg: MIRArgument, into: MIRType, vtypes: Map<string, MIRType>): SMTValue {
        assert(this.isTypeExact(into));

        const argt = this.getArgType(arg, vtypes);
        if (this.isTypeExact(argt)) {
            return new SMTValue(arg.nameID);
        }
        else {
            if(argt)
            (bsq_term_none) (bsq_term_bool (bsq_term_bool_value BBool)) (bsq_term_int (bsq_term_int_value BInt)) (bsq_term_string (bsq_term_string_value BString)) (bsq_term_tuple (bsq_term_tuple_value BTuple))
        }
    }

    private createTuple(args: MIRArgument[], ttype: MIRType, vtypes: Map<string, MIRType>): SMTValue {
        if (this.isTypeExact(ttype)) {
            return new SMTValue(`(bsq_tuple@${this.typeToSMT2(ttype)} ${args.map((arg) => this.argToSMT2(arg))})`);
        }
        else {
            const args = op.args.map((arg) => { 
                if(this.isTypeExact(vtypes.))
                this.argToSMT2(arg);
            });
            const tc = `(bsq_tuple ${[op.args.length, ...op.args.map((arg) => this.argToSMT2(arg))]}`;
            return new SMTLet(this.varToSMT2Name(op.trgt), new SMTValue(tc), this.generateFreeSMTVar());
        }
    }

    private generateMIRConstructorTuple(op: MIRConstructorTuple, vtypes: Map<string, MIRType>): SMTExp {
        const ttype = (this.assembly.typeMap.get(op.getValueOpTypeKey()) as MIRType);

        return new SMTLet(this.varToSMT2Name(op.trgt), this.createTuple(op.args, ttype, vtypes), this.generateFreeSMTVar());
    }

    generateMIRAccessFromIndex(op: MIRAccessFromIndex, vtypes: Map<string, MIRType>): SMTExp {
        const argtype = vtypes.get(op.arg.nameID) as MIRType;
        const tupinfo = argtype.options[0] as MIRTupleType;

        if (this.isTypeExact(argtype)) {
            if (op.idx >= tupinfo.entries.length) {
                return `((${this.varToSMT2(op.trgt)} bsq_none))`;
            }
            else {
                const tc = `(bsq_tuple@${this.typeToSMT2(argtype)}@${op.idx} ${this.argToSMT2(op.arg)})`;
                return `((${this.varToSMT2(op.trgt)} ${tc}))`;
            }
        }
        else {
            NOT_IMPLEMENTED("generateMIRAccessFromIndex -- else branch");
            return "[NOT IMPL]";
        }
    }

    private updatevtypeMap(op: MIROp, vtypes: Map<string, MIRType>) {
        if (op instanceof MIRValueOp) {
            vtypes.set(op.trgt.nameID, this.assembly.typeMap.get(op.getValueOpTypeKey()) as MIRType);
        }
        else {
            xxxx;
        }
    }

    generateSMTScope(op: MIROp, vtypes: Map<string, MIRType>): SMTExp {
        this.updatevtypeMap(op, vtypes);

        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const lcv = (op as MIRLoadConst);
                return new SMTLet(this.varToSMT2Name(lcv.trgt), this.argToSMT2(lcv.src, vtypes.get(lcv.trgt.nameID) as MIRType, vtypes), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRLoadConstTypedString:  {
                NOT_IMPLEMENTED("MIRLoadConstTypedString");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRAccessConstantValue: {
                NOT_IMPLEMENTED("MIRAccessConstantValue");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRLoadFieldDefaultValue: {
                NOT_IMPLEMENTED("MIRLoadFieldDefaultValue");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRAccessArgVariable: {
                const lav = (op as MIRAccessArgVariable);
                return new SMTLet(this.varToSMT2Name(lav.trgt), this.argToSMT2(lav.name, vtypes.get(lav.trgt.nameID) as MIRType, vtypes), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRAccessLocalVariable: {
                const llv = (op as MIRAccessLocalVariable);
                return new SMTLet(this.varToSMT2Name(llv.trgt), this.argToSMT2(llv.name, vtypes.get(llv.trgt.nameID) as MIRType, vtypes), this.generateFreeSMTVar());
            }
            case MIROpTag.MIRConstructorPrimary: {
                NOT_IMPLEMENTED("MIRConstructorPrimary");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionEmpty");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionSingletons");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionCopies");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionMixed");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRConstructorTuple: {
                const tc = op as MIRConstructorTuple;
                return this.generateMIRConstructorTuple(tc, vtypes);
            }
            case MIROpTag.MIRConstructorRecord: {
                NOT_IMPLEMENTED("MIRConstructorRecord");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRAccessFromIndex: {
                const ai = op as MIRAccessFromIndex;
                return this.generateMIRAccessFromIndex(ai, vtypes);
            }
            case MIROpTag.MIRProjectFromIndecies: {
                NOT_IMPLEMENTED("MIRProjectFromIndecies");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRAccessFromProperty: {
                NOT_IMPLEMENTED("MIRAccessFromProperty");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRProjectFromProperties: {
                NOT_IMPLEMENTED("MIRProjectFromProperties");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRAccessFromField: {
                NOT_IMPLEMENTED("MIRAccessFromField");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRProjectFromFields: {
                NOT_IMPLEMENTED("MIRProjectFromFields");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                NOT_IMPLEMENTED("MIRProjectFromTypeTuple");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                NOT_IMPLEMENTED("MIRProjectFromTypeRecord");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                NOT_IMPLEMENTED("MIRProjectFromTypeConcept");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRModifyWithIndecies: {
                const mi = op as MIRModifyWithIndecies;
                mi.arg = processSSA_Use(mi.arg, remap);
                mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], remap)]);
                processValueOpTempSSA(mi, remap, ctrs);
                break;
            }
            case MIROpTag.MIRModifyWithProperties: {
                NOT_IMPLEMENTED("MIRModifyWithProperties");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRModifyWithFields: {
                NOT_IMPLEMENTED("MIRModifyWithFields");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                NOT_IMPLEMENTED("MIRStructuredExtendTuple");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                NOT_IMPLEMENTED("MIRStructuredExtendRecord");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRStructuredExtendObject: {
                NOT_IMPLEMENTED("MIRStructuredExtendObject");
                return this.generateFreeSMTVar();
            }
            case MIROpTag.MIRInvokeFixedFunction: {
                const invk = op as MIRInvokeFixedFunction;
                invk.args = processSSAUse_RemapArgs(invk.args, remap);
                processValueOpTempSSA(invk, remap, ctrs);
                break;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                NOT_IMPLEMENTED("MIRInvokeVirtualTarget");
                break;
            }
            case MIROpTag.MIRPrefixOp: {
                const pfx = op as MIRPrefixOp;
                if (pfx.op === "!") {
                    fscope.assignTmpReg(pfx.trgt.regID, !ValueOps.convertBoolOrNoneToBool(pvalue));
                }
                else if (pfx.op === "-") {
                    xxxx;
                }
                else {
                    return new SMTLet(this.varToSMT2Name(pfx.trgt), this.argToSMT2(pfx.arg, vtypes.get(pfx.trgt.nameID) as MIRType, vtypes), this.generateFreeSMTVar());
                }
            }
            case MIROpTag.MIRBinOp: {
                const bop = op as MIRBinOp;
                bop.lhs = processSSA_Use(bop.lhs, remap);
                bop.rhs = processSSA_Use(bop.rhs, remap);
                processValueOpTempSSA(bop, remap, ctrs);
                break;
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
                ton.arg = processSSA_Use(ton.arg, remap);
                processValueOpTempSSA(ton, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const tos = op as MIRIsTypeOfSome;
                tos.arg = processSSA_Use(tos.arg, remap);
                processValueOpTempSSA(tos, remap, ctrs);
                break;
            }
            case MIROpTag.MIRIsTypeOf: {
                const tog = op as MIRIsTypeOf;
                tog.arg = processSSA_Use(tog.arg, remap);
                processValueOpTempSSA(tog, remap, ctrs);
                break;
            }
            case MIROpTag.MIRRegAssign: {
                const regop = op as MIRRegAssign;
                regop.src = processSSA_Use(regop.src, remap);
                regop.trgt = convertToSSA(regop.trgt, remap, ctrs) as MIRTempRegister;
                break;
            }
            case MIROpTag.MIRTruthyConvert: {
                const tcop = op as MIRTruthyConvert;
                tcop.src = processSSA_Use(tcop.src, remap);
                tcop.trgt = convertToSSA(tcop.trgt, remap, ctrs) as MIRTempRegister;
                break;
            }
            case MIROpTag.MIRLogicStore: {
                const llop = op as MIRLogicStore;
                llop.lhs = processSSA_Use(llop.lhs, remap);
                llop.rhs = processSSA_Use(llop.rhs, remap);
                llop.trgt = convertToSSA(llop.trgt, remap, ctrs) as MIRTempRegister;
                break;
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
                const dbg = op as MIRDebug;
                if (dbg.value !== undefined) {
                    dbg.value = processSSA_Use(dbg.value, remap);
                }
                break;
            }
            case MIROpTag.MIRJump: {
                break;
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
                break;
            }
            default:
                assert(false);
                break;
        }
    }
}

export {
    SMTLIBGenerator
};
