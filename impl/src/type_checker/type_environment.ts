//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import assert = require("assert");

import { Assembly } from "../ast/assembly";
import { ResolvedType } from "../ast/resolved_type";
import { MIRInvokeKey } from "../compiler/mir_ops";
import { PCode } from "../compiler/mir_emitter";

enum FlowTypeTruthValue {
    True = "True",
    False = "False",
    Unknown = "Unknown"
}

class FlowTypeTruthOps {
    static equal(e1: FlowTypeTruthValue, e2: FlowTypeTruthValue): boolean {
        return e1 === e2;
    }

    static subvalue(e1: FlowTypeTruthValue, e2: FlowTypeTruthValue): boolean {
        return e2 === FlowTypeTruthOps.join(e1, e2);
    }

    static join(...values: FlowTypeTruthValue[]): FlowTypeTruthValue {
        if (values.length === 0) {
            return FlowTypeTruthValue.Unknown;
        }

        const hasunknown = values.indexOf(FlowTypeTruthValue.Unknown) !== -1;
        const hastrue = values.indexOf(FlowTypeTruthValue.True) !== -1;
        const hasfalse = values.indexOf(FlowTypeTruthValue.False) !== -1;

        if (hasunknown || (hastrue && hasfalse)) {
            return FlowTypeTruthValue.Unknown;
        }
        else {
            return hastrue ? FlowTypeTruthValue.True : FlowTypeTruthValue.False;
        }
    }

    static maybeTrueValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.True || e === FlowTypeTruthValue.Unknown);
    }

    static maybeFalseValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.False || e === FlowTypeTruthValue.Unknown);
    }
}

class ExpressionReturnResult {
    readonly exptype: ResolvedType;
    readonly truthval: FlowTypeTruthValue;

    readonly expvar: string | undefined;

    constructor(etype: ResolvedType, tval: FlowTypeTruthValue, expvar: string | undefined) {
        this.exptype = etype;
        this.truthval = tval;

        this.expvar = expvar;
    }

    static join(assembly: Assembly, expvar: string, ...args: ExpressionReturnResult[]): ExpressionReturnResult {
        assert(args.length !== 0);

        const jtype = assembly.typeUpperBound(args.map((ei) => ei.exptype));
        const jtv = FlowTypeTruthOps.join(...args.map((ei) => ei.truthval));

        return new ExpressionReturnResult(jtype, jtv, expvar);
    }
}

class VarInfo {
    readonly declaredType: ResolvedType;
    readonly isConst: boolean;
    readonly isCaptured: boolean;
    readonly mustDefined: boolean;

    readonly flowType: ResolvedType;
    readonly truthval: FlowTypeTruthValue; 

    constructor(dtype: ResolvedType, isConst: boolean, isCaptured: boolean, mustDefined: boolean, ftype: ResolvedType, fvalue: FlowTypeTruthValue) {
        this.declaredType = dtype;
        this.flowType = ftype;
        this.isConst = isConst;
        this.isCaptured = isCaptured;
        this.mustDefined = mustDefined;
        this.truthval = fvalue;
    }

    assign(ftype: ResolvedType, fvalue: FlowTypeTruthValue): VarInfo {
        assert(!this.isConst);
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype, fvalue);
    }

    infer(ftype: ResolvedType, fvalue: FlowTypeTruthValue): VarInfo {
        return new VarInfo(this.declaredType, this.isConst, this.isCaptured, true, ftype, fvalue);
    }

    static join(assembly: Assembly, ...values: VarInfo[]): VarInfo {
        assert(values.length !== 0);

        const jdef = values.every((vi) => vi.mustDefined);
        const jtype = assembly.typeUpperBound(values.map((vi) => vi.flowType));
        const jval = FlowTypeTruthOps.join(...values.map((vi) => vi.truthval));
        return new VarInfo(values[0].declaredType, values[0].isConst, values[0].isCaptured, jdef, jtype, jval);
    }
}

type StructuredAssignmentPathStep = {
    fromtype: ResolvedType,
    t: ResolvedType,
    step: "tuple" | "record" | "elist" | "nominal";
    ival: number;
    nval: string;
};

class TypeEnvironment {
    readonly scope: MIRInvokeKey;
    readonly terms: Map<string, ResolvedType>;

    readonly refparams: string[];
    readonly pcodes: Map<string, { pcode: PCode, captured: string[] }>;

    readonly args: Map<string, VarInfo> | undefined;
    readonly locals: Map<string, VarInfo>[] | undefined;

    readonly inferResult: ResolvedType | undefined;
    readonly inferYield: (ResolvedType | undefined)[];

    readonly expressionResult: ExpressionReturnResult | undefined;
    readonly returnResult: ResolvedType | undefined;
    readonly yieldResult: ResolvedType | undefined;

    readonly frozenVars: Set<string>;

    private constructor(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, refparams: string[], pcodes: Map<string, { pcode: PCode, captured: string[] }>,
        args: Map<string, VarInfo> | undefined, locals: Map<string, VarInfo>[] | undefined, result: ResolvedType | undefined, inferYield: (ResolvedType | undefined)[],
        expressionResult: ExpressionReturnResult | undefined, rflow: ResolvedType | undefined, yflow: ResolvedType | undefined,
        frozenVars: Set<string>) {

        this.scope = scope;
        this.terms = terms;

        this.refparams = refparams;
        this.pcodes = pcodes;

        this.args = args;
        this.locals = locals;

        this.inferResult = result;
        this.inferYield = inferYield;

        this.expressionResult = expressionResult;
        this.returnResult = rflow;
        this.yieldResult = yflow;

        this.frozenVars = frozenVars;
    }

    private updateVarInfo(name: string, nv: VarInfo): TypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
        else {
            const argscopy = new Map<string, VarInfo>(this.args as Map<string, VarInfo>).set(name, nv);
            return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, argscopy, this.locals, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
        }
    }

    static createInitialEnvForCall(scope: MIRInvokeKey, terms: Map<string, ResolvedType>, refparams: string[], pcodes: Map<string, { pcode: PCode, captured: string[] }>, args: Map<string, VarInfo>, inferResult: ResolvedType | undefined): TypeEnvironment {
        return new TypeEnvironment(scope, terms, refparams, pcodes, args, [new Map<string, VarInfo>()], inferResult, [], undefined, undefined, undefined, new Set<string>());
    }

    hasNormalFlow(): boolean {
        return this.locals !== undefined;
    }

    getExpressionResult(): ExpressionReturnResult {
        assert(this.hasNormalFlow() && this.expressionResult !== undefined);

        return this.expressionResult as ExpressionReturnResult;
    }

    setResultExpression(etype: ResolvedType, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const einfo = new ExpressionReturnResult(etype, value || FlowTypeTruthValue.Unknown, undefined);
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setResultExpressionWVarOpt(etype: ResolvedType, evar: string | undefined, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const rvalue = value || FlowTypeTruthValue.Unknown;
        const einfo = new ExpressionReturnResult(etype, rvalue, evar);
        const nte = new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);

        return evar === undefined ? nte : nte.updateVarInfo(evar, (nte.lookupVar(evar) as VarInfo).assign(etype, rvalue));
    }

    setResultExpressionWVarOptNoInfer(etype: ResolvedType, evar: string | undefined, value?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const rvalue = value || FlowTypeTruthValue.Unknown;
        const einfo = new ExpressionReturnResult(etype, rvalue, evar);
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, einfo, this.returnResult, this.yieldResult, this.frozenVars);
    }

    static convertToBoolFlowsOnResult(assembly: Assembly, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        assert(options.every((opt) => assembly.subtypeOf(opt.getExpressionResult().exptype, assembly.getSpecialBoolType())));

        const tvals = options.filter((opt) => opt.getExpressionResult().truthval !== FlowTypeTruthValue.False)
            .map((opt) => opt.setResultExpressionWVarOpt(assembly.getSpecialBoolType(), opt.getExpressionResult().expvar, FlowTypeTruthValue.True));

        const fvals = options.filter((opt) => opt.getExpressionResult().truthval !== FlowTypeTruthValue.True)
            .map((opt) => opt.setResultExpressionWVarOpt(assembly.getSpecialBoolType(), opt.getExpressionResult().expvar, FlowTypeTruthValue.False));

        return {tenvs: tvals, fenvs: fvals};
    }

    static convertToTypeNotTypeFlowsOnResult(assembly: Assembly, witht: ResolvedType, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const pccs = assembly.splitTypes(opt.getExpressionResult().exptype, witht);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(pccs.tp, opt.getExpressionResult().expvar, opt.getExpressionResult().truthval));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(pccs.fp, opt.getExpressionResult().expvar, opt.getExpressionResult().truthval));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    static convertToHasIndexNotHasIndexFlowsOnResult(assembly: Assembly, idx: number, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const pccs = assembly.splitIndex(opt.getExpressionResult().exptype, idx);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(pccs.tp, opt.getExpressionResult().expvar));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(pccs.fp, opt.getExpressionResult().expvar));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    static convertToHasIndexNotHasPropertyFlowsOnResult(assembly: Assembly, pname: string, options: TypeEnvironment[]): {tenvs: TypeEnvironment[], fenvs: TypeEnvironment[]} {
        let tp: TypeEnvironment[] = [];
        let fp: TypeEnvironment[] = [];
        
        for(let i = 0; i < options.length; ++i) {
            const opt = options[i];
            const pccs = assembly.splitProperty(opt.getExpressionResult().exptype, pname);

            if(!pccs.tp.isEmptyType()) {
                tp.push(opt.setResultExpressionWVarOpt(pccs.tp, opt.getExpressionResult().expvar));
            }
            if(!pccs.fp.isEmptyType()) {
                fp.push(opt.setResultExpressionWVarOpt(pccs.fp, opt.getExpressionResult().expvar));
            }
        }
        return {tenvs: tp, fenvs: fp};
    }

    setAbort(): TypeEnvironment {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUpperBound([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, rrtype, this.yieldResult, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUpperBound([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, rytype, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());

        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    isInYieldBlock(): boolean {
        return this.inferYield.length !== 0;
    }

    getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    isVarNameDefined(name: string): boolean {
        return this.getLocalVarInfo(name) !== undefined || (this.args as Map<string, VarInfo>).has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args as Map<string, VarInfo>).get(name) || null;
    }

    lookupPCode(pc: string): { pcode: PCode, captured: string[] } | undefined {
        return this.pcodes.get(pc);
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, infertype: ResolvedType, tv?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined, infertype, tv || FlowTypeTruthValue.Unknown));

        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setVar(name: string, ftype: ResolvedType, tv?: FlowTypeTruthValue): TypeEnvironment {
        assert(this.hasNormalFlow());

        const oldv = this.lookupVar(name) as VarInfo;
        
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, oldv.assign(ftype, tv || FlowTypeTruthValue.Unknown));

        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    multiVarUpdate(allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][], allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][]): TypeEnvironment {
        assert(this.hasNormalFlow());

        let nenv: TypeEnvironment = this;

        for (let i = 0; i < allDeclared.length; ++i) {
            const declv = allDeclared[i];
            nenv = nenv.addVar(declv[1], declv[0], declv[2], true, declv[4]);
        }

        for (let i = 0; i < allAssigned.length; ++i) {
            const assignv = allAssigned[i];
            nenv = nenv.setVar(assignv[0], assignv[2]);
        }

        return nenv;
    }

    getCurrentFrameNames(): string[] {
        let res: string[] = [];
        (this.locals as Map<string, VarInfo>[])[(this.locals as Map<string, VarInfo>[]).length - 1].forEach((v, k) => {
            res.push(k);
        });
        return res;
    }

    getAllLocalNames(): Set<string> {
        let names = new Set<string>();
        (this.locals as Map<string, VarInfo>[]).forEach((frame) => {
            frame.forEach((v, k) => {
                names.add(k);
            });
        });
        return names;
    }

    freezeVars(): TypeEnvironment {
        assert(this.hasNormalFlow());

        let svars = new Set<string>();
        for (let i = 0; i < (this.locals as Map<string, VarInfo>[]).length; ++i) {
            (this.locals as Map<string, VarInfo>[])[i].forEach((v, k) => svars.add(k));
        }

        return new TypeEnvironment(this.scope, this.terms, this.refparams, this.pcodes, this.args, this.locals, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        const fopts = opts.filter((opt) => opt.locals !== undefined);

        let argnames: string[] = [];
        fopts.forEach((opt) => {
            (opt.args as Map<string, VarInfo>).forEach((v, k) => argnames.push(k));
        });

        let args = fopts.length !== 0 ? new Map<string, VarInfo>() : undefined;
        if (args !== undefined) {
            argnames.forEach((aname) => {
                const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => (opt.args as Map<string, VarInfo>).get(aname) as VarInfo));
                (args as Map<string, VarInfo>).set(aname, vinfo);
            });
        }

        let locals = fopts.length !== 0 ? ([] as Map<string, VarInfo>[]) : undefined;
        if (locals !== undefined) {
            for (let i = 0; i < (fopts[0].locals as Map<string, VarInfo>[]).length; ++i) {
                let localsi = new Map<string, VarInfo>();
                (fopts[0].locals as Map<string, VarInfo>[])[i].forEach((v, k) => {
                    localsi.set(k, VarInfo.join(assembly, ...fopts.map((opt) => opt.lookupVar(k) as VarInfo)));
                });

                locals.push(localsi);
            }
        }

        const expresall = fopts.filter((opt) => opt.expressionResult !== undefined).map((opt) => opt.getExpressionResult());
        assert(expresall.length === 0 || expresall.length === fopts.length);

        let expres: ExpressionReturnResult | undefined = undefined;
        if(expresall.length !== 0) {
            const retype = assembly.typeUpperBound(expresall.map((opt) => opt.exptype));
            const rflow = FlowTypeTruthOps.join(...expresall.map((opt) => opt.truthval));
            const evar = expresall.every((ee) => ee.expvar === expresall[0].expvar) ? expresall[0].expvar : undefined;
            expres = new ExpressionReturnResult(retype, rflow, evar);
        }

        const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult as ResolvedType);
        const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult as ResolvedType);

        return new TypeEnvironment(opts[0].scope, opts[0].terms, opts[0].refparams, opts[0].pcodes, args, locals, opts[0].inferResult, opts[0].inferYield, expres, rflow.length !== 0 ? assembly.typeUpperBound(rflow) : undefined, yflow.length !== 0 ? assembly.typeUpperBound(yflow) : undefined, opts[0].frozenVars);
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo, ExpressionReturnResult, StructuredAssignmentPathStep,
    TypeEnvironment
};
