//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTFunction, SMTFunctionUninterpreted } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTCond, SMTConst, SMTExp, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

class RequiredListConstructors {
    //always error
    //always empty
    //always slice
    //always concat2

    havoc: boolean = false;

    fill: boolean = false;
    literalk: Set<number> = new Set<number>();
    filter: Set<string> = new Set<string>();
    map: Set<string> = new Set<string>();
}

type SMTConstructorGenCode = {
    uf: SMTFunctionUninterpreted[],
    if: SMTFunction[],
    ulitype: SMTType,
    cons: { cname: string, cargs: { fname: string, ftype: SMTType }[] }
};

class RequiredListDestructors {
    //always get

    haspredcheck: Set<string> = new Set<string>();
    findIndexOf: Set<string> = new Set<string>();
    findLastIndexOf: Set<string> = new Set<string>();
    countIf: Set<string> = new Set<string>();
}

type SMTDestructorGenCode = {
    uf: SMTFunctionUninterpreted[],
    if: SMTFunction[]
};

class ListOpsInfo {
    readonly ltype: MIRType;
    readonly ctype: MIRType;

    consops: RequiredListConstructors;
    dops: RequiredListDestructors;

    constructor(ltype: MIRType, ctype: MIRType) {
        this.ltype = ltype;
        this.ctype = ctype;

        this.consops = new RequiredListConstructors();
        this.dops = new RequiredListDestructors();
    }
}

class ListOpsManager {
    vopts: VerifierOptions
    temitter: SMTTypeEmitter;

    rangenat: boolean = false;
    rangeint: boolean = false;

    ops: Map<string, ListOpsInfo> = new Map<string, ListOpsInfo>();

    private tmpvarctr = 0;

    
    generateTempName(): string {
        return `@tmpvar_cc@${this.tmpvarctr++}`;
    }

    constructor(vopts: VerifierOptions, temitter: SMTTypeEmitter) {
        this.vopts = vopts;
        this.temitter = temitter;
    }

    private ensureOpsFor(encltype: MIRType): ListOpsInfo {
        if (!this.ops.has(encltype.trkey)) {
            const stypeinfo = (this.temitter.assembly.entityDecls.get(encltype.trkey) as MIREntityTypeDecl).specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[];
            const ctype = this.temitter.getMIRType((stypeinfo.find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);

            this.ops.set(encltype.trkey, new ListOpsInfo(encltype, ctype));
        }

        return this.ops.get(encltype.trkey) as ListOpsInfo;
    }

    processLiteralK_0(ltype: MIRType): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName_Direct(this.temitter.getSMTTypeFor(ltype), "empty");

        const llcons = this.temitter.getSMTConstructorName(ltype);
        return new SMTCallSimple(`${llcons.cons}`, [new SMTConst("BNat@zero"), new SMTConst(fcons)]);
    }

    processLiteralK_Pos(ltype: MIRType, k: number, values: SMTExp[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName_Direct(this.temitter.getSMTTypeFor(ltype), "k");
        ops.consops.literalk.add(k)

        const llcons = this.temitter.getSMTConstructorName(ltype);
        const kcons = new SMTCallSimple(fcons, values);
        return new SMTCallSimple(`${llcons.cons}`, [new SMTConst(`(_ BV${k} ${this.vopts.ISize})`), kcons]);
    }

    processFillOperation(ltype: MIRType, count: SMTExp, value: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "fill");
        ops.consops.fill = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [value]);
    }

    processRangeOfIntOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfInt");
        this.rangeint = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end]);
    }

    processRangeOfNatOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfNat");
        this.rangenat = true;
        
        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end]);
    }

    processHasPredCheck(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "hasPredCheck", code);

        ops.dops.haspredcheck.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processGet(ltype: MIRType, l: SMTExp, n: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "get");
        //get always registered

        return new SMTCallGeneral(op, [l, n]);
    }

    processConcat2(ltype: MIRType, l1: SMTExp, l2: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "concat2");

        return this.generateErrorPropConsCall(ltype, count, fcons, [l1, l2]);
    }

    processFindIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findIndexOf", code);

        ops.dops.findIndexOf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processFindLastIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findLastIndexOf", code);

        ops.dops.findLastIndexOf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processCountIf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "countIf", code);

        ops.dops.countIf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processFilter(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "filter", code);

        ops.consops.filter.add(op);
        xxxx;
        return this.generateErrorPropConsCall(op, [l]);
    }

    processSlice(ltype: MIRType, l1: SMTExp, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "slice");

        return this.generateErrorPropConsCall(ltype, count, fcons, [l1, start, end]);
    }

    processmap(ltype: MIRType, code: string, l: SMTExp, count: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "map", code);

        ops.consops.map.add(op);
        return this.generateErrorPropConsCall(ltype, count, op, [l]);
    }

    generateConsCallName(ltype: SMTType, opname: string): string {
        return `@@consop_${ltype.name}_${opname}`;
    }

    generateConsCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `@@consop_${ltype.name}_${opname}_using_${code}`;
    }

    generateDesCallName(ltype: SMTType, opname: string): string {
        return `@@desop_${ltype.name}_${opname}`;
    }

    generateDesCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `@@desop_${ltype.name}_${opname}_using_${code}`;
    }

    generateULITypeFor(ltype: SMTType): SMTType {
        return new SMTType(ltype.name + "$uli");
    }

    generateULIFieldFor(ltype: SMTType, consname: string, fname: string): string {
        return this.generateConsCallName_Direct(ltype, consname) + "_" + fname;
    }

    generateULIFieldUsingFor(ltype: SMTType, consname: string, code: string, fname: string): string {
        return this.generateConsCallNameUsing_Direct(ltype, consname, code) + "_" + fname;
    }

    generateConsCallName_Direct(ltype: SMTType, opname: string): string {
        return `@@cons_${ltype.name}_${opname}`;
    }

    generateConsCallNameUsing_Direct(ltype: SMTType, opname: string, code: string): string {
        return `@@cons_${ltype.name}_${opname}_using_${code}`;
    }

    generateListSizeCall(exp: SMTExp, etype: SMTType): SMTExp {
        return new SMTCallSimple(`${etype.name}@size`, [exp]);
    }

    generateGetULIFieldFor(ltype: SMTType, consname: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldFor(ltype, consname, fname), [arg]);
    }

    generateGetULIFieldUsingFor(ltype: SMTType, consname: string, code: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldUsingFor(ltype, consname, code, fname), [arg]);
    }

    emitConstructorError(ltype: SMTType): SMTConstructorGenCode {
        return {
            uf: [],
            if: [],
            ulitype: this.generateULITypeFor(ltype),
            cons: {
                cname: this.generateConsCallName_Direct(ltype, "error"), 
                cargs: []
            }
        }
    }

    emitConstructorEmpty(ltype: SMTType): SMTConstructorGenCode {
        return {
            uf: [],
            if: [],
            ulitype: this.generateULITypeFor(ltype),
            cons: {
                cname: this.generateConsCallName_Direct(ltype, "empty"), 
                cargs: []
            }
        }
    }

    ////////
    //Slice
    emitConstructorSlice_Slice(ltype: SMTType, ll: SMTExp, start: SMTExp, end: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [
            this.generateGetULIFieldFor(ltype, "slice", "l", ll), 
            new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "slice", "start", ll), start]),
            new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "slice", "start", ll), end])
        ]);
    }

    emitConstructorSlice_Concat(mtype: MIRType, ltype: SMTType, ll: SMTExp, start: SMTExp, end: SMTExp): SMTExp {
        const l1v = this.generateTempName();
        const l2v = this.generateTempName();
        const l1vs = this.generateTempName();
        const l2vs = this.generateTempName();

        return new SMTLetMulti([
            { vname: l1v, value: this.generateGetULIFieldFor(ltype, "concat2", "l1", ll) },
            { vname: l2v, value: this.generateGetULIFieldFor(ltype, "concat2", "l2", ll) },
        ],
            new SMTLetMulti([
                { vname: l1vs, value: this.generateListSizeCall(new SMTVar(l1v), ltype) },
                { vname: l2vs, value: this.generateListSizeCall(new SMTVar(l2v), ltype) },
            ],
                new SMTCond([
                    //if(end <= lv1.size) => slice(lv1, start, end, count)
                    { test: new SMTCallSimple("bvule", [end, new SMTVar(l1vs)]), result: new SMTCallSimple(this.generateConsCallName(ltype, "slice"), [new SMTVar(l1v), start, end]) },
                    //if(lv1.size <= start) => slice(lv2, start - lv1.size, end - lv1.size, count)
                    { test: new SMTCallSimple("bvule", [new SMTVar(l1vs), start]), result: new SMTCallSimple(this.generateConsCallName(ltype, "slice"), [new SMTVar(l2v), new SMTCallSimple("bvsub", [start, new SMTVar(l1vs)]), new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)])]) }
                ],
                    //concat(slice(lv1, start, lv1.size), slice(lv2, 0, end - lv1.size)) 
                    new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [
                        this.generateSafePropConsCall(mtype, new SMTCallSimple("bvsub", [new SMTVar(l1vs), start]), this.generateConsCallName(ltype, "slice"), [new SMTVar(l1v), start, new SMTVar(l1vs)]),
                        this.generateSafePropConsCall(mtype, new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)]), this.generateConsCallName(ltype, "slice"), [new SMTVar(l2v), new SMTConst("BNat@zero"), new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)])])
                    ])
                )
            )
        );
    }

    emitConstructorSlice(mtype: MIRType, ctype: MIRType, ltype: SMTType, sl: SMTExp, start: SMTExp, end: SMTExp, count: SMTExp): SMTConstructorGenCode {
        let ufs: SMTFunctionUninterpreted[] = [];
        let ifs: SMTFunction[] = [];

        const llname = this.generateTempName();
        const llv = new SMTVar(llname);
        
        //if(count == 0) => empty
        const emptyaction = { test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), []) };
        //if(count == sl.size) => sl
        const sameaction = { test: new SMTCallSimple("=", [count, this.generateListSizeCall(sl, ltype)]), result: llv };

        let tsops: {test: SMTExp, result: SMTExp }[] = [];

        //if(is-type slice) => get base list and use new start/end
        tsops.push({test: new SMTCallSimple(`is-${this.generateConsCallName(ltype, "slice")}`, [llv]), result: this.emitConstructorSlice_Slice(ltype, llv, start, end)});

        //if(is-type concat) => check exclude l1 or l2 otherwise concat(slice(l1), slice(l2))
        tsops.push({test: new SMTCallSimple(`is-${this.generateConsCallName(ltype, "concat2")}`, [llv]), result: this.emitConstructorSlice_Concat(mtype, ltype, llv, start, end)});
        
        //if(is-type fill) => fill with new index
        tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName(ltype, "fill")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "fill"), [this.generateGetULIFieldFor(ltype, "fill", "v", llv), new SMTCallSimple("bvsub", [count])]) });

        //if(is-natrange) => range with new bounds
        if (this.rangenat && ctype.trkey === "NSCore::Nat") {
            tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName(ltype, "rangeOfNat")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "rangeOfNat"), [new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), start]), new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), end])]) });
        }
        //if(is-intrange) => range with new bounds
        if (this.rangeint && ctype.trkey === "NSCore::Int") {
            tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName(ltype, "rangeOfInt")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "rangeOfNat"), [new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), start]), new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), end])]) });
        }

        //default construct
        xxxx;
    }
    ////////

    emitConstructorConcat2(): {

    }

    havoc: boolean = false;

    fill: boolean = false;
    literalk: Set<number> = new Set<number>();
    filter: Set<string> = new Set<string>();
    map: Set<string> = new Set<string>();

    //always get

    haspredcheck: Set<string> = new Set<string>();
    findIndexOf: Set<string> = new Set<string>();
    findLastIndexOf: Set<string> = new Set<string>();
    countIf: Set<string> = new Set<string>();

    generateErrorPropConsCall(ltype: MIRType, count: SMTExp, ullcons: string, args: SMTExp[]): SMTExp {
        const llcons = this.temitter.getSMTConstructorName(ltype);

        const tvar = this.generateTempName();
        return new SMTLet(tvar, new SMTCallGeneral(ullcons, args),
            new SMTIf(new SMTCallSimple("=", [new SMTVar(tvar), new SMTConst(this.generateConsCallName_Direct(this.temitter.getSMTTypeFor(ltype), "error"))]),
                this.temitter.generateErrorResultAssert(ltype),
                this.temitter.generateResultTypeConstructorSuccess(ltype, new SMTCallSimple(`${llcons.cons}`, [count, new SMTVar(tvar)]))
            )
        );
    }

    generateSafePropConsCall(ltype: MIRType, count: SMTExp, ullcons: string, args: SMTExp[]): SMTExp {
        const llcons = this.temitter.getSMTConstructorName(ltype);
        return new SMTCallSimple(`${llcons.cons}`, [count, new SMTCallGeneral(ullcons, args)]);
    }

    generateListBoundsCheckCallUpper(nidx: string, upper: SMTExp): SMTExp {
        //lower bound is assumed to be 0
        return new SMTCallSimple("bvult", [new SMTVar(nidx), upper]);
    }

    generateListBoundsCheckCallBoth(nidx: string, lower: SMTExp, upper: SMTExp): SMTExp {
        return new SMTCallSimple("and", [
            new SMTCallSimple("bvule", [lower, new SMTVar(nidx)]),
            new SMTCallSimple("bvult", [new SMTVar(nidx), upper])
        ]);
    }
}

export {
    ListOpsManager
};
