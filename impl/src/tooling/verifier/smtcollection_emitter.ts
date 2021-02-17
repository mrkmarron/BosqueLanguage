//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRPCode, MIRType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTFunction, SMTFunctionUninterpreted } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTCond, SMTConst, SMTExists, SMTExp, SMTForAll, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

class RequiredListConstructors {
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

    safecheck: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    isequence: Map<string, MIRPCode> = new Map<string, MIRPCode>();

    haspredcheck: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    findIndexOf: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    findLastIndexOf: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    countIf: Map<string, MIRPCode> = new Map<string, MIRPCode>();
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

    processHavoc(ltype: MIRType, path: SMTVar): SMTExp {
        const ops = this.ensureOpsFor(ltype);

        ops.consops.havoc = true;
        if (this.vopts.SpecializeSmallModelGen) {
            ops.consops.literalk.add(1);
            ops.consops.literalk.add(2);
            ops.consops.literalk.add(3);
        }

        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "havoc"), [path])
    }

    processLiteralK_0(ltype: MIRType): SMTExp {
        this.ensureOpsFor(ltype);
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "empty"), []);
    }

    processLiteralK_Pos(ltype: MIRType, k: number, values: SMTExp[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const opname = `_${values.length}`;
        ops.consops.literalk.add(k)

        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), opname), values);
    }

    processFillOperation(ltype: MIRType, count: SMTExp, value: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        ops.consops.fill = true;

        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "fill"), [value, count]);
    }

    processRangeOfIntOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        this.rangeint = true;

        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfInt"),  [start, end, count]);
    }

    processRangeOfNatOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        this.rangenat = true;
        
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfNat"),  [start, end, count]);
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

        xxxx;
        return new SMTCallGeneral(op, [l, n]);
    }

    processConcat2(ltype: MIRType, l1: SMTExp, l2: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "concat2"), [l1, l2, count]);
    }

    processFindIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findIndexOf", code);

        xxxx;
        ops.dops.findIndexOf.add(op);
        ops.dops.errorapply.set(code, [pc, ltype]);
        ops.dops.haspredcheck.set();
        return new SMTCallGeneral(op, [l]);
    }

    processFindLastIndexOf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "findLastIndexOf", code);

        xxxx;
        ops.dops.findLastIndexOf.add(op);
        ops.dops.errorapply.set(code, [pc, ltype]);
        ops.dops.haspredcheck.set();
        return new SMTCallGeneral(op, [l]);
    }

    processCountIf(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "countIf", code);

        xxxx;
        ops.dops.countIf.add(op);
        ops.dops.errorapply.set(code, [pc, ltype]);
        ops.dops.haspredcheck.set(code, pc);
        ops.dops.isequence.set(code, pc);
        return new SMTCallGeneral(op, [l]);
    }

    processFilter(ltype: MIRType, code: string, l: SMTVar, isq: SMTVar, count: SMTVar): SMTExp {
        const ops = this.ensureOpsFor(ltype);

        ops.consops.filter.set(code);
        return new SMTCallGeneral(this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "filter", code), [l, isq, count]);
    }

    processSlice(ltype: MIRType, l1: SMTExp, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        return new SMTCallSimple(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "slice"), [l1, start, end, count]);
    }

    processMap(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);

        ops.consops.map.add(code);
        return new SMTCallGeneral(this.generateConsCallNameUsing(this.temitter.getSMTTypeFor(ltype), "map", code), [l]);
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

    emitConstructorEmpty(mtype: MIRType, ltype: SMTType): SMTConstructorGenCode {
        const ffunc = new SMTCallSimple(this.temitter.getSMTConstructorName(mtype).cons, [
            new SMTConst("BNat@zero"),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [])
        ]);

        return {
            cons: {
                cname: this.generateConsCallName_Direct(ltype, "empty"), 
                cargs: []
            },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "empty"), [], undefined, 0, ltype, ffunc)],
            uf: []
        }
    }

    ////////
    //Slice
    emitConstructorSlice(mtype: MIRType, ltype: SMTType, sl: SMTVar, start: SMTVar, end: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            count,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "slice"), [sl, start, end])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "slice"), cargs: [{ fname: this.generateULIFieldFor(ltype, "slice", "l"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "slice", "start"), ftype: this.nattype }, { fname: this.generateULIFieldFor(ltype, "slice", "end"), ftype: this.nattype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "slice"), [{ vname: "l", vtype: ltype }, { vname: "start", vtype: this.nattype }, { vname: "end", vtype: this.nattype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Concat
    emitConstructorConcat2(mtype: MIRType, ltype: SMTType, l1: SMTVar, l2: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            count,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "concat2"), [l1, l2])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "concat2"), cargs: [{ fname: this.generateULIFieldFor(ltype, "concat2", "l1"), ftype: ltype }, { fname: this.generateULIFieldFor(ltype, "concat2", "l2"), ftype: ltype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "concat2"), [{ vname: "l1", vtype: ltype }, { vname: "l2", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //Havoc
    emitConstructorHavoc(mtype: MIRType, ctype: MIRType, ltype: SMTType, path: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;
        const ptype = new SMTType("(Seq BNat)");


        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.vopts.SpecializeSmallModelGen) {
            const size = this.generateTempName();
            const sizev = new SMTVar(size);

            ffunc = new SMTLet(size, new SMTCallSimple("BNat@UFCons_API", [path]),
                new SMTCond([
                    {
                        test: new SMTCallSimple("=", [sizev, new SMTConst("BNat@zero")]),
                        result: this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "empty"), []))
                    },
                    {
                        test: new SMTCallSimple("=", [sizev, new SMTConst(`(_ BV1 ${this.vopts.ISize})`)]),
                        result: new SMTLetMulti([
                            { vname: "@val0", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) }
                        ],
                            new SMTIf(this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val0")),
                                this.temitter.generateErrorResultAssert(mtype),
                                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "_1"), [new SMTVar("@val0")]))
                            )
                        )
                    },
                    {
                        test: new SMTCallSimple("=", [sizev, new SMTConst(`(_ BV2 ${this.vopts.ISize})`)]),
                        result: new SMTLetMulti([
                            { vname: "@val0", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) },
                            { vname: "@val1", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) }
                        ],
                            new SMTIf(new SMTCallSimple("or", [
                                this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val0")),
                                this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val1"))
                            ]),
                                this.temitter.generateErrorResultAssert(mtype),
                                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "_2"), [new SMTVar("@val0"), new SMTVar("@val1")]))
                            )
                        )
                    },
                    {
                        test: new SMTCallSimple("=", [sizev, new SMTConst(`(_ BV3 ${this.vopts.ISize})`)]),
                        result: new SMTLetMulti([
                            { vname: "@val0", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) },
                            { vname: "@val1", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) },
                            { vname: "@val2", value: new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []) }
                        ],
                            new SMTIf(new SMTCallSimple("or", [
                                this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val0")),
                                this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val1")),
                                this.temitter.generateResultIsErrorTest(ctype, new SMTVar("@val2"))
                            ]),
                                this.temitter.generateErrorResultAssert(mtype),
                                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName(ltype, "_3"), [new SMTVar("@val0"), new SMTVar("@val1"), new SMTVar("@val2")]))
                            )
                        )
                    }
                ],
                    new SMTCallSimple(lcons, [
                        sizev,
                        this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName_Direct(ltype, "havoc"), [path]))
                    ])
                )
            )
        }
        else {
            ffunc = new SMTCallSimple(lcons, [
                new SMTCallSimple("BNat@UFCons_API", [path]),
                this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(this.generateConsCallName_Direct(ltype, "havoc"), [path]))
            ]);
        }

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "havoc"), cargs: [{ fname: this.generateULIFieldFor(ltype, "havoc", "path"), ftype: ptype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "havoc"), [{ vname: "path", vtype: ptype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Fill
    emitConstructorFill(mtype: MIRType, ltype: SMTType, ctype: MIRType, value: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = new SMTCallSimple(lcons, [
            count,
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "fill"), [value])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, "fill"), cargs: [{ fname: this.generateULIFieldFor(ltype, "fill", "value"), ftype: this.temitter.getSMTTypeFor(ctype) }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, "fill"), [{ vname: "value", vtype: this.temitter.getSMTTypeFor(ctype) }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //RangeNat/Int
    emitConstructorRange(mtype: MIRType, ltype: SMTType, ctype: MIRType, start: SMTVar, end: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const opname = ctype.trkey === "NSCore::Nat" ? "rangeOfNat" : "rangeOfInt";
        const rtype = this.temitter.getSMTTypeFor(ctype);
        
        const ffunc = new SMTCallSimple(lcons, [
            new SMTCallSimple("bvsub", [end, start]),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), [start, end])
        ]);

        return {
            cons: { cname: this.generateConsCallName_Direct(ltype, opname), cargs: [{ fname: this.generateULIFieldFor(ltype, opname, "start"), ftype: rtype }, { fname: this.generateULIFieldFor(ltype, opname, "end"), ftype: rtype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallName(ltype, opname), [{ vname: "start", vtype: rtype }, { vname: "end", vtype: rtype }, { vname: "count", vtype: this.nattype }], undefined, 0, ltype, ffunc)],
            uf: []
        };
    }

    ////////
    //LiteralK
    emitConstructorLiteralK(mtype: MIRType, ltype: SMTType, ctype: MIRType, values: SMTExp[]): SMTConstructorGenCode {
        const smtctype = this.temitter.getSMTTypeFor(ctype);
        
        const opname = `_${values.length}`;
        //default construct
        const ffunc = new SMTCallSimple(this.temitter.getSMTConstructorName(mtype).cons, [
            new SMTConst(`(_ BV${values.length} ${this.vopts.ISize})`),
            new SMTCallSimple(this.generateConsCallName_Direct(ltype, opname), values)
        ]);

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
    emitConstructorFilter(ltype: SMTType, mtype: MIRType, code: string, sl: SMTVar, isq: SMTVar, osize: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.vopts.SimpleQuantifierMode) {
            ffunc = new SMTLet("@rsize", this.generateListSize_1_to_Max_PickCall(this.generateConsCallNameUsing(ltype, "filter", code), sl, osize),
                new SMTIf(this.temitter.generateResultIsErrorTest(this.temitter.getMIRType("NSCore::Nat"), new SMTVar("@rsize")),
                    this.temitter.generateErrorResultAssert(mtype),
                    this.temitter.generateResultTypeConstructorSuccess(mtype,
                        new SMTCallSimple(lcons, [
                            this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Nat"), new SMTVar("@rsize")),
                            new SMTCallSimple(this.generateConsCallName_Direct(ltype, "filter"), [sl, isq])
                        ])
                    )
                )
            );
        }
        else {
            ffunc = this.temitter.generateResultTypeConstructorSuccess(mtype,
                new SMTCallSimple(lcons, [
                    new SMTCallSimple("ISequence@size", [isq]),
                    new SMTCallSimple(this.generateConsCallName_Direct(ltype, "filter"), [sl, isq])
                ])
            );
        }

        return {
            cons: { cname: this.generateConsCallNameUsing_Direct(ltype, "filter", code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, "filter", code, "l"), ftype: ltype }, {fname: this.generateULIFieldUsingFor(ltype, "filter", code, "isq"), ftype: new SMTType("ISequence")}] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallNameUsing(ltype, "filter", code), [{ vname: "l", vtype: ltype }, { vname: "isq", vtype: new SMTType("ISequence") }, { vname: "osize", vtype: this.nattype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Map
    emitConstructorMap(ltype: SMTType, mtype: MIRType, code: string, sl: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const ffunc = this.temitter.generateResultTypeConstructorSuccess(mtype,
            new SMTCallSimple(lcons, [
                count,
                new SMTCallSimple(this.generateConsCallName_Direct(ltype, "map"), [sl])
            ])
        );

        return {
            cons: { cname: this.generateConsCallNameUsing_Direct(ltype, "map", code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, "map", code, "l"), ftype: ltype }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallNameUsing(ltype, "map", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Get
    emitDestructorGet_Slice(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        return new SMTCallGeneral(getop, [
            ll,
            new SMTCallSimple("bvadd", [
                n,
                this.generateGetULIFieldFor(ltype, "slice", "start", ll)
            ])
        ]);
    }

    emitDestructorGet_Concat2(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        const l1 = this.generateTempName();
        const l1v = new SMTVar(l1);
        const l2 = this.generateTempName();
        const l2v = new SMTVar(l2);

        const l1s = this.generateTempName();
        const l1sv = new SMTVar(l1s);

        return new SMTLet(l1, this.generateGetULIFieldFor(ltype, "concat2", "l1", ll),
            new SMTLet(l1s, this.generateListSizeCall(l1v, ltype),
                new SMTIf(new SMTCallSimple("bvult", [n, l1sv]),
                    new SMTCallGeneral(getop, [l1v, n]),
                    new SMTCallGeneral(getop, [l2v, new SMTCallSimple("bvsub", [n, l1sv])])
                )
            )
        );
    }

    emitDestructorGet_K(ltype: SMTType, ctype: MIRType, ll: SMTVar, n: SMTVar, k: number): SMTExp {
        if (k === 1) {
            return this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${0}`, ll));
        }
        else {
            let kops: { test: SMTExp, result: SMTExp }[] = [];

            for (let i = 0; i < k - 1; ++i) {
                kops.push({
                    test: new SMTCallSimple("=", [n, new SMTConst(`${i}`)]),
                    result: this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${i}`, ll))
                });
            }
            
            const klast = this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${k - 1}`, ll))
            return new SMTCond(
                kops,
                klast
            );
        }
    }

    emitDestructorGet_Filter(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar, code: string): SMTExp {
        if (this.vopts.SimpleQuantifierMode) {

            generateListIndexPickCall
        }
        else {
            return new SMTCallGeneral(getop, [
                this.generateGetULIFieldUsingFor(ltype, "filter", code, "l", ll),
                new SMTCallSimple("ISequence@get", [this.generateGetULIFieldUsingFor(ltype, "filter", code, "irv", ll), n])
            ]);
        }
    }

    emitDestructorGet_Map(ltype: SMTType, ctype: MIRType, srcltype: SMTType, ll: SMTVar, n: SMTVar, code: string, pc: MIRPCode): SMTExp {
        const getop = this.generateDesCallName(srcltype, "get_internal");
        const getsrc = new SMTCallGeneral(getop, [ll, n]);
        const applyfn = this.temitter.generateResultTypeConstructorSuccess(ctype, this.generateLambdaCallKnownSafe(pc, ctype, xxx, [yy]));

        zzz;
    }

    emitDestructorGet(ltype: SMTType, mtype: MIRType, ctype: MIRType, sl: SMTVar, n: SMTVar, consopts: RequiredListConstructors): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get_internal");

        const ll = this.generateTempName();
        const llv = new SMTVar(ll);
        let tsops: { test: SMTExp, result: SMTExp }[] = [];

        //always slice
        tsops.push({
            test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "slice")}`, [llv]),
            result: this.emitDestructorGet_Slice(getop, ltype, llv, n)
        });

        //always concat2
        tsops.push({
            test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "concat2")}`, [llv]),
            result: this.emitDestructorGet_Concat2(getop, ltype, llv, n)
        });

        if(consopts.havoc) {
            zzz;
        }

        if(consopts.fill) {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "fill")}`, [llv]),
                result: this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, "fill", "v", llv))
            });
        }

        //if(is-natrange) => range with new bounds
        if (this.rangenat && ctype.trkey === "NSCore::Nat") {
            tsops.push({ 
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "rangeOfNat")}`, [llv]), 
                result: new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfNat", "start", llv), n])
            });
        }

        //if(is-intrange) => range with new bounds
        if (this.rangeint && ctype.trkey === "NSCore::Int") {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "rangeOfInt")}`, [llv]),
                result: new SMTCallSimple("bvadd", [this.generateGetULIFieldFor(ltype, "rangeOfInt", "start", llv), n])
            });
        }

        consopts.literalk.forEach((k) => {
            if (k !== 0) {
                tsops.push({
                    test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, `_${k}`)}`, [llv]),
                    result: this.emitDestructorGet_K(ltype, ctype, llv, n, k)
                })
            }
        });
        
        consopts.filter.forEach((pcode, code) => {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallNameUsing_Direct(ltype, "filter", code)}`, [llv]),
                result: this.emitDestructorGet_Filter(getop, ltype, llv, n, code)
            })
        });

        consopts.map.forEach((pcode, code) => {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallNameUsing_Direct(ltype, "map", code)}`, [llv]),
                result: this.emitDestructorGet_Map(getop, ltype, ctype, llv, n, code)
            })
        });

        const ffunc = new SMTLetMulti([{ vname: ll, value: this.generateListContentsCall(sl, ltype) }],
            new SMTCond(tsops, this.temitter.generateErrorResultAssert(ctype))
        );

        return {
            if: [new SMTFunction(this.generateConsCallName(ltype, "get"), [{ vname: "l", vtype: ltype }, { vname: "n", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(ctype), ffunc)],
            uf: []
        };
    }

    ////////
    //ErrorApply
    emitDestructorErrorApply_K(ltype: SMTType, ctype: MIRType, ll: SMTVar, n: SMTVar, k: number): SMTExp {
        if (k === 1) {
            return this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${0}`, ll));
        }
        else {
            let kops: { test: SMTExp, result: SMTExp }[] = [];

            for (let i = 0; i < k - 1; ++i) {
                kops.push({
                    test: new SMTCallSimple("=", [n, new SMTConst(`${i}`)]),
                    result: this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${i}`, ll))
                });
            }
            
            const klast = this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, `_${k}`, `idx${k - 1}`, ll))
            return new SMTCond(
                kops,
                klast
            );
        }
    }

    emitDestructorErrorApply(ltype: SMTType, mtype: MIRType, ctype: MIRType, sl: SMTVar, code: string, pcode: MIRPCode, ispcsafe: boolean, restype: MIRType, consopts: RequiredListConstructors): SMTDestructorGenCode {
        const errop = this.generateDesCallNameUsing(ltype, "errorapply_internal", code);

        const ll = this.generateTempName();
        const llv = new SMTVar(ll);
        const llsize = this.generateTempName();
        const llsizev = new SMTVar(llsize);

        let tsops: { test: SMTExp, result: SMTExp }[] = [];

        if(consopts.fill) {
            xxx;
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "fill")}`, [llv]),
                result: this.temitter.generateResultGetSuccess(ctype, this.generateGetULIFieldFor(ltype, "fill", "v", llv))
            });
        }

        consopts.literalk.forEach((k) => {
            if (k !== 0) {
                tsops.push({
                    test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, `_${k}`)}`, [llv]),
                    result: this.emitDestructorErrorApply_K(ltype, ctype, llv, n, k)
                })
            }
        });
        
        const ten = this.generateTempName();
        const tenv = new SMTVar(ten);
        const gen = this.generateTempName();
        const genv = new SMTVar(gen);

        const tecase = new SMTExists([{vname: ten, vtype: this.nattype}],
            new SMTCallSimple("and", [
                new SMTCallSimple("bvult", [tenv, llsizev]),
                new SMTCallSimple("=", [this.generateLambdaCallGeneral(pcode, restype, [xxx get]), this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))])
            ])
        );

        const gecase = new SMTExists([{vname: gen, vtype: this.nattype}],
            new SMTCallSimple("and", [
                new SMTCallSimple("bvult", [genv, llsizev]),
                new SMTCallSimple("=", [this.generateLambdaCallGeneral(pcode, restype, [xxx get]), this.temitter.generateErrorResultAssert(restype)])
            ])
        );

        const ffunc = new SMTLetMulti([{ vname: ll, value: this.generateListContentsCall(sl, ltype) }],
            new SMTCond(tsops, this.temitter.generateErrorResultAssert(ctype))
        );

        return {
            if: [new SMTFunction(this.generateConsCallName(ltype, "get"), [{ vname: "l", vtype: ltype }, { vname: "n", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(ctype), ffunc)],
            uf: []
        };
    }

    ////////
    //ISequence
    emitDestructorISequence(ltype: SMTType, mtype: MIRType, ctype: MIRType, sl: SMTVar, n: SMTVar, consopts: RequiredListConstructors): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "errorapply_internal");

        const ll = this.generateTempName();
        const llv = new SMTVar(ll);
        let tsops: { test: SMTExp, result: SMTExp }[] = [];

        xxxx;
    }

    ////////
    //HasPredCheck
    emitDestructorHasPredCheck(ltype: SMTType, mtype: MIRType, ctype: MIRType, sl: SMTVar, n: SMTVar, consopts: RequiredListConstructors): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "errorapply_internal");

        const ll = this.generateTempName();
        const llv = new SMTVar(ll);
        let tsops: { test: SMTExp, result: SMTExp }[] = [];

        xxxx;
    }

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

    generateLambdaCallGeneral(pc: MIRPCode, rtype: MIRType, args: SMTExp[]): SMTExp {
        const cargs = pc.cargs.map((ca) => new SMTVar(this.temitter.mangle(ca)));
        return new SMTCallGeneral(this.temitter.mangle(pc.code), [...args, ...cargs]);
    }
}

export {
    ListOpsManager
};
