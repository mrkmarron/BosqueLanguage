//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRPCode, MIRType } from "../../compiler/mir_assembly";
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

    safeapply: Set<string> = new Set<string>();
    isequence: Set<string> = new Set<string>();

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

    private booltype: SMTType;
    private nattype: SMTType;
    
    generateTempName(): string {
        return `@tmpvar_cc@${this.tmpvarctr++}`;
    }

    constructor(vopts: VerifierOptions, temitter: SMTTypeEmitter) {
        this.vopts = vopts;
        this.temitter = temitter;

        this.booltype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Bool"));
        this.nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));
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
        const fcons = this.generateConsCallName_Direct(this.temitter.getSMTTypeFor(ltype), `_${k}`);
        ops.consops.literalk.add(k)

        const llcons = this.temitter.getSMTConstructorName(ltype);
        const kcons = new SMTCallSimple(fcons, values);
        return new SMTCallSimple(`${llcons.cons}`, [new SMTConst(`(_ BV${k} ${this.vopts.ISize})`), kcons]);
    }

    processFillOperation(ltype: MIRType, count: SMTExp, value: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "fill");
        ops.consops.fill = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [count, value]);
    }

    processRangeOfIntOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfInt");
        this.rangeint = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end, count]);
    }

    processRangeOfNatOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfNat");
        this.rangenat = true;
        
        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end, count]);
    }

    processHasPredCheck(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "hasPredCheck", code);

        xxxx;
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

        return this.generateErrorPropConsCall(ltype, count, fcons, [l1, l2, count]);
    }

    processFindIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findIndexOf", code);

        xxxx;
        ops.dops.findIndexOf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processFindLastIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findLastIndexOf", code);

        xxxx;
        ops.dops.findLastIndexOf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processCountIf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "countIf", code);

        xxxx;
        ops.dops.countIf.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processFilter(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "filter", code);

        xxxx;
        ops.consops.filter.add(op);
        xxxx;
        return this.generateErrorPropConsCall(op, [l]);
    }

    processSlice(ltype: MIRType, l1: SMTExp, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "slice");

        return this.generateErrorPropConsCall(ltype, count, fcons, [l1, start, end, count]);
    }

    processmap(ltype: MIRType, code: string, l: SMTExp, count: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "map", code);

        xxxx;
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

    generateListContentsCall(exp: SMTExp, etype: SMTType): SMTExp {
        return new SMTCallSimple(`${etype.name}@contents`, [exp]);
    }

    generateGetULIFieldFor(ltype: SMTType, consname: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldFor(ltype, consname, fname), [arg]);
    }

    generateGetULIFieldUsingFor(ltype: SMTType, consname: string, code: string, fname: string, arg: SMTExp): SMTExp {
        return new SMTCallSimple(this.generateULIFieldUsingFor(ltype, consname, code, fname), [arg]);
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

    emitExtractISequence(ltype: SMTType, code: string): SMTFunction {
        
        //Assume all special cases have been handled (including error case) in callers so this is always general case 

        //default construct
        const ffunc = new SMTIf(emptyaction.test, emptyaction.result,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), [start, end])
        );

        xxxx;
    }

    ////////
    //Slice
    emitConstructorSlice_Slice(mtype: MIRType, ltype: SMTType, lcons: string, count: SMTVar, ll: SMTVar, start: SMTVar, end: SMTExp): SMTExp {
        return this.temitter.generateResultTypeConstructorSuccess(mtype,
            new SMTCallSimple(lcons, [
                count,
                new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [
                    this.generateGetULIFieldFor(ltype, "slice", "l", ll),
                    new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "slice", "start", ll), start]),
                    new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "slice", "start", ll), end])
                ])
            ])
        );
    }

    emitConstructorSlice_Concat(mtype: MIRType, ltype: SMTType, lcons: string, count: SMTVar, ll: SMTVar, start: SMTVar, end: SMTVar): SMTExp {
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
                    { 
                        test: new SMTCallSimple("bvule", [end, new SMTVar(l1vs)]), 
                        result: new SMTCallGeneral(this.generateConsCallName(ltype, "slice"), [
                            new SMTVar(l1v), start, end
                        ]) 
                    },
                    //if(lv1.size <= start) => slice(lv2, start - lv1.size, end - lv1.size, count)
                    { 
                        test: new SMTCallSimple("bvule", [new SMTVar(l1vs), start]), 
                        result: new SMTCallGeneral(this.generateConsCallName(ltype, "slice"), [
                            new SMTVar(l2v), 
                            new SMTCallSimple("bvsub", [start, new SMTVar(l1vs)]), 
                            new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)])
                        ]) 
                    }
                ],
                    //concat(slice(lv1, start, lv1.size), slice(lv2, 0, end - lv1.size)) 
                    this.temitter.generateResultTypeConstructorSuccess(mtype,
                        new SMTCallSimple(lcons, [
                            count,
                            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [
                                this.temitter.generateResultGetSuccess(mtype,
                                    new SMTCallGeneral(this.generateConsCallName(ltype, "slice"), [
                                        new SMTVar(l1v),
                                        start,
                                        new SMTVar(l1vs),
                                        new SMTCallSimple("bvsub", [new SMTVar(l1vs), start])
                                    ])
                                ),
                                this.temitter.generateResultGetSuccess(mtype,
                                    new SMTCallGeneral(this.generateConsCallName(ltype, "slice"), [
                                        new SMTVar(l2v),
                                        new SMTConst("BNat@zero"),
                                        new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)]),
                                        new SMTCallSimple("bvsub", [end, new SMTVar(l1vs)])
                                    ])
                                )
                            ])
                        ])
                    )
                )
            )
        );
    }

    emitConstructorSlice(mtype: MIRType, ctype: MIRType, ltype: SMTType, sl: SMTVar, start: SMTVar, end: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const llname = this.generateTempName();
        const llv = new SMTVar(llname);
        
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        //if(count == 0) => empty
        const emptyaction = { 
            test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]),
            result: this.temitter.generateResultTypeConstructorSuccess(mtype,
                new SMTCallSimple(lcons, [
                    new SMTConst("BNat@zero"),
                    new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), [])
                ])
            )
        };
        
        //if(count == sl.size) => sl
        const sameaction = { 
            test: new SMTCallSimple("=", [count, this.generateListSizeCall(sl, ltype)]), 
            result: this.temitter.generateResultTypeConstructorSuccess(mtype, sl)
        };

        let tsops: {test: SMTExp, result: SMTExp }[] = [];

        //if(is-type slice) => get base list and use new start/end
        tsops.push({
            test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "slice")}`, [llv]), 
            result: this.emitConstructorSlice_Slice(ltype, llv, start, end)
        });

        //if(is-type concat) => check exclude l1 or l2 otherwise concat(slice(l1), slice(l2))
        tsops.push({test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "concat2")}`, [llv]), result: this.emitConstructorSlice_Concat(mtype, ltype, llv, start, end)});
        
        //if(is-type fill) => fill with new index
        tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "fill")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "fill"), [count, this.generateGetULIFieldFor(ltype, "fill", "v", llv)]) });

        //if(is-natrange) => range with new bounds
        if (this.rangenat && ctype.trkey === "NSCore::Nat") {
            tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "rangeOfNat")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "rangeOfNat"), [new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), start]), new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), end]), count]) });
        }
        //if(is-intrange) => range with new bounds
        if (this.rangeint && ctype.trkey === "NSCore::Int") {
            tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "rangeOfInt")}`, [llv]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "rangeOfNat"), [new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), start]), new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), end]), count]) });
        }

        //default construct
        const ffunc = new SMTLet(llname, this.generateListContentsCall(sl, ltype),
            new SMTIf(emptyaction.test, emptyaction.result,
                new SMTIf(sameaction.test, sameaction.result,
                    new SMTCond(
                        tsops,
                        new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [sl, start, end])
                    )
                )
            )
        );

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "slice"), cargs: [{ fname: this.generateULIFieldFor(ltype, "slice", "l"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "slice", "start"), ftype: this.nattype }, { fname: this.generateULIFieldFor(ltype, "slice", "end"), ftype: this.nattype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "slice"), [{ vname: "l", vtype: ltype }, { vname: "start", vtype: this.nattype }, { vname: "end", vtype: this.nattype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Concat
    emitConstructorConcat2(ltype: SMTType, l1: SMTExp, l2: SMTExp, count: SMTExp): SMTConstructorGenCode {
        const ll1name = this.generateTempName();
        const ll1v = new SMTVar(ll1name);
        const ll2name = this.generateTempName();
        const ll2v = new SMTVar(ll2name);
        
        //if(count == 0) => empty
        const emptyaction = { test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), []) };
        //if(l1.size == 0) => l2
        const l1emptyaction = { test: new SMTCallSimple("=", [this.generateListSizeCall(l1, ltype)]), result: ll2v };
        //if(l2.size == 0) => l1
        const l2emptyaction = { test: new SMTCallSimple("=", [this.generateListSizeCall(l2, ltype)]), result: ll1v };

        //default construct
        const ffunc = new SMTLetMulti([{ vname: ll1name, value: this.generateListContentsCall(l1, ltype) }, { vname: ll2name, value: this.generateListContentsCall(l2, ltype) }],
            new SMTIf(emptyaction.test, emptyaction.result,
                new SMTIf(l1emptyaction.test, l1emptyaction.result,
                    new SMTIf(l2emptyaction.test, l2emptyaction.result,
                        new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [l1, l2])
                    )
                )
            )
        );

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "concat2"), cargs: [{ fname: this.generateULIFieldFor(ltype, "concat2", "l1"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "concat2", "l2"), ftype: ltype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "concat2"), [{ vname: "l1", vtype: ltype }, { vname: "l2", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Havoc
    xxxx;

    ////////
    //Fill
    emitConstructorFill(ltype: SMTType, ctype: MIRType, value: SMTExp, count: SMTExp): SMTConstructorGenCode {
        //if(count == 0) => empty
        const emptyaction = { test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), []) };

        //default construct
        const ffunc = new SMTIf(emptyaction.test, emptyaction.result,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "fill"), [count, value])
        );

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "fill"), cargs: [{ fname: this.generateULIFieldFor(ltype, "fill", "count"), ftype: this.nattype }, { fname: this.generateULIFieldFor(ltype, "fill", "value"), ftype: this.temitter.getSMTTypeFor(ctype) }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "fill"), [{ vname: "count", vtype: this.nattype }, { vname: "value", vtype: this.temitter.getSMTTypeFor(ctype) }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //RangeNat/Int
    emitConstructorRange(ltype: SMTType, ctype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTConstructorGenCode {
        //if(count == 0) => empty
        const emptyaction = { test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), []) };

        const opname = ctype.trkey === "NSCore::Nat" ? "rangeOfNat" : "rangeOfInt";
        const rtype = this.temitter.getSMTTypeFor(ctype);
        //default construct
        const ffunc = new SMTIf(emptyaction.test, emptyaction.result,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), [start, end])
        );

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: [{ fname: this.generateULIFieldFor(ltype, opname, "start"), ftype: rtype }, { fname: this.generateULIFieldFor(ltype, opname, "end"), ftype: rtype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), [{ vname: "start", vtype: rtype }, { vname: "end", vtype: rtype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //LiteralK
    emitConstructorLiteralK(ltype: SMTType, ctype: MIRType, values: SMTExp[]): SMTConstructorGenCode {
        const smtctype = this.temitter.getSMTTypeFor(ctype);
        const opname = `_${values.length}`;

        //default construct
        const ffunc = new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), values);

        let kfields: {fname: string, ftype: SMTType}[] = [];
        let kfargs: {vname: string, vtype: SMTType}[] = [];
        for(let i = 0; i < values.length; ++i) {
            kfields.push({fname: this.generateULIFieldFor(ltype, opname, `idx${i}`), ftype: smtctype});
            kfargs.push({vname: `idx${i}`, vtype: smtctype});
        }

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: kfields },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), kfargs, undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Filter
    emitConstructorFilter_Concat(mtype: MIRType, ltype: SMTType, lcons: string, uli_concat: SMTVar, code: string): SMTExp {
        const l1v = this.generateTempName();
        const l2v = this.generateTempName();

        return new SMTLetMulti([
            //compute filter on each list
            { 
                vname: l1v, 
                value: this.temitter.generateResultGetSuccess(mtype, new SMTCallGeneral(this.generateConsCallNameUsing(ltype, "filter", code), [this.generateGetULIFieldFor(ltype, "concat2", "l1", uli_concat)])) 
            },
            { 
                vname: l2v, 
                value: this.temitter.generateResultGetSuccess(mtype, new SMTCallGeneral(this.generateConsCallNameUsing(ltype, "filter", code), [this.generateGetULIFieldFor(ltype, "concat2", "l2", uli_concat)])) 
            }
        ],
            //compute size of result
            new SMTCallSimple(`${lcons}`, [
                new SMTCallSimple("bvadd", [this.generateListSizeCall(new SMTVar(l1v), ltype), this.generateListSizeCall(new SMTVar(l2v), ltype)]),
                new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [new SMTVar(l1v), new SMTVar(l2v)])
            ])
        );
    }

    emitConstructorFilter(ltype: SMTType, mtype: MIRType, lcons: string, sl: SMTVar, count: SMTVar, code: string, pc: MIRPCode, issafe: boolean): SMTConstructorGenCode {
        const ll = this.generateTempName();
        const llsize = this.generateTempName();
        const llv = new SMTVar(ll);

        const isq = this.generateTempName();
        const isqv = new SMTVar(isq);

        const emptytest = new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]);
        const emptyresult = new SMTCallSimple(`${lcons}`, [new SMTConst("BNat@zero"), new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), [])]);

        const checksafe = new SMTCallSimple("not", [new SMTCallSimple(this.generateDesCallNameUsing(ltype, "safeapply", this.temitter.mangle(code)), [sl])]);
        const haspred = new SMTCallSimple(this.generateDesCallNameUsing(ltype, "haspred_safe", this.temitter.mangle(code)), [llv]);

        let tsops: { test: SMTExp, result: SMTExp }[] = [];
        //
        //Filter on literals seems hard (like forcing a bunch of enumeration -- so leaving alone for now)
        //
        //if(is-type fill) => check fill value -- return empty or identity
        tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "fill")}`, [llv]), result: new SMTIf(this.generateLambdaCallKnownSafe(pc, this.temitter.getMIRType("NSCore::Bool"), issafe, [this.generateGetULIFieldFor(ltype, "fill", "v", llv)]), sl, emptyresult) });
        //if(is-type concat2) => return concat of filter(l1), filter(l2)
        tsops.push({ test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "concat2")}`, [llv]), result: this.emitConstructorFilter_Concat(mtype, ltype, lcons, llv, code) });

        //default construct
        const ffunc = new SMTLetMulti([{ vname: ll, value: this.generateListContentsCall(sl, ltype) }, { vname: llsize, value: this.generateListSizeCall(sl, ltype) }],
            new SMTIf(emptytest, emptyresult,
                new SMTIf(checksafe, this.temitter.generateResultTypeConstructorError()),
                    new SMTIf(haspred, emptyresult,
                        new SMTCond(
                            tsops,
                            new SMTLet(isq, new SMTCallGeneral(this.generateConsCallNameUsing(ltype, "isequence", code), [sl]),
                                new SMTIf(new SMTCallSimple("is-ISequence@Result_error", [isqv]),
                                    new SMTConst(this.generateConsCallName_Direct(ltype, "error")),
                                    new SMTCallSimple(this.generateConsCallNameUsing_Direct(ltype, "filter", code), [isqv])
                                )
                            )
                        )
                    )
                )
            )
        );

        return {
            cons: { cname: this.generateConsCallNameUsing_Direct(ltype, "filter", code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, "filter", code, "l"), ftype: ltype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallNameUsing(ltype, "filter", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Map
    emitConstructorMap(ltype: SMTType, ctype: MIRType, code: string, count: SMTExp): SMTConstructorGenCode {
        //if(count == 0) => empty
        const emptyaction = { test: new SMTCallSimple("=", [count, new SMTConst("BNat@zero")]), result: new SMTCallSimple(this.generateConsCallName_Direct(ltype, "empty"), []) };

        //safe apply check if needed
        
        //if(is-type concat2) => apply map to each and concat

        //if(is-type fill) => fill with mapped value
    
        //if(is-type literal k) => new literal k with map applied

        //default construct
        const ffunc = new SMTIf(emptyaction.test, emptyaction.result,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), [start, end])
        );

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: [{ fname: this.generateULIFieldFor(ltype, opname, "start"), ftype: rtype }, { fname: this.generateULIFieldFor(ltype, opname, "end"), ftype: rtype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), [{ vname: "start", vtype: rtype }, { vname: "end", vtype: rtype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    //always get

    safeapply: Set<string> = new Set<string>();
    isequence: Set<string> = new Set<string>();

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

    generateLambdaCallKnownSafe(pc: MIRPCode, rtype: MIRType, issafe: boolean, args: SMTExp[]): SMTExp {
        const cargs = pc.cargs.map((ca) => new SMTVar(this.temitter.mangle(ca)));
        const call = new SMTCallGeneral(this.temitter.mangle(pc.code), [...args, ...cargs]);

        if(issafe) {
            return call;
        }
        else {
            return this.temitter.generateResultGetSuccess(rtype, call);
        }
    }
}

export {
    ListOpsManager
};
