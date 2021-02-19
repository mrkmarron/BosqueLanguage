//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRInvokeBodyDecl, MIRPCode, MIRType } from "../../compiler/mir_assembly";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
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
    filter: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    map: Map<string, [MIRPCode, SMTType]> = new Map<string, [MIRPCode, SMTType]>();
}

type SMTConstructorGenCode = {
    uf: SMTFunctionUninterpreted[],
    if: SMTFunction[],
    ulitype: SMTType,
    cons: { cname: string, cargs: { fname: string, ftype: SMTType }[] }
};

class RequiredListDestructors {
    //always get

    safecheckpred: Map<string, MIRPCode> = new Map<string, MIRPCode>();
    safecheckfn: Map<string, MIRPCode> = new Map<string, MIRPCode>();
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
    readonly vopts: VerifierOptions
    readonly temitter: SMTTypeEmitter;
    readonly safecalls: Set<MIRInvokeKey>; 

    rangenat: boolean = false;
    rangeint: boolean = false;

    ops: Map<string, ListOpsInfo> = new Map<string, ListOpsInfo>();

    private tmpvarctr = 0;

    private booltype: SMTType;
    private nattype: SMTType;
    
    generateTempName(): string {
        return `@tmpvar_cc@${this.tmpvarctr++}`;
    }

    constructor(vopts: VerifierOptions, temitter: SMTTypeEmitter, safecalls: Set<MIRInvokeKey>) {
        this.vopts = vopts;
        this.temitter = temitter;
        this.safecalls = safecalls;

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
            const size = "@size";
            const sizev = new SMTVar(size);

            ffunc = new SMTLet(size, new SMTCallSimple("ListSize@UFCons_API", [path]),
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
                new SMTIf(new SMTForAll([{ vname: "@n", vtype: this.nattype }],
                    new SMTCallSimple("=>", [
                        new SMTCallSimple("bvult", [new SMTVar("@n"), sizev]),
                        this.temitter.generateResultIsSuccessTest(ctype, new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []))
                    ])
                    ),
                        this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(lcons, [sizev, new SMTCallSimple(this.generateConsCallName_Direct(ltype, "havoc"), [path])])),
                        this.temitter.generateErrorResultAssert(mtype)
                    )
                )
            )
        }
        else {
            const size = "@size";
            const sizev = new SMTVar(size);

            ffunc = new SMTLet(size, new SMTCallSimple("ListSize@UFCons_API", [path]),
                new SMTIf(new SMTForAll([{ vname: "@n", vtype: this.nattype }],
                    new SMTCallSimple("=>", [
                        new SMTCallSimple("bvult", [new SMTVar("@n"), sizev]),
                        this.temitter.generateResultIsSuccessTest(ctype, new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC]", []))
                    ])
                ),
                    this.temitter.generateResultTypeConstructorSuccess(mtype, new SMTCallSimple(lcons, [sizev, new SMTCallSimple(this.generateConsCallName_Direct(ltype, "havoc"), [path])])),
                    this.temitter.generateErrorResultAssert(mtype)
                )
            );
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
    emitConstructorFilter(ltype: SMTType, mtype: MIRType, ctype: MIRType, code: string, pcode: MIRPCode, sl: SMTVar, isq: SMTVar, osize: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedparams = pcode.cargs.map((arg) => new SMTVar(arg));
        const ufpickargs = [ltype, this.nattype, ...lambdainfo.params.slice(1).map((p) => this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)))];

        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        let ufuncs: SMTFunctionUninterpreted[] = [];
        if (this.vopts.SimpleQuantifierMode) {
            const getop = this.generateDesCallName(ltype, "get");

            const getcheck = new SMTForAll([{vname: "@n", vtype: this.nattype}],
                new SMTCallSimple("=>", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), new SMTVar("@rsize")]),
                    new SMTLet("@nn", this.generateListIndexPickCall_Kth(this.generateConsCallNameUsing(ltype, "skolem_list_index", code), sl, new SMTVar("@n"), capturedparams),
                        new SMTCallSimple("and", [
                            new SMTCallSimple("bvult", [new SMTVar("@nn"), osize]),
                            this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTCallSimple(getop, [sl, new SMTVar("@nn")])], capturedparams)
                        ])
                    )]
                )
            );

            ffunc = new SMTLet("@rsize", this.generateListSize_1_to_Max_m1_PickCall(this.generateDesCallNameUsing(ltype, "skolem_list_size", code), sl, osize, capturedparams),
                new SMTIf(getcheck,
                    this.temitter.generateResultTypeConstructorSuccess(mtype,
                    new SMTCallSimple(lcons, [
                        new SMTVar("@rsize"),
                        new SMTCallSimple(this.generateConsCallName_Direct(ltype, "filter"), [sl, isq])
                    ])
                ),
                this.temitter.generateErrorResultAssert(ctype)
                )
            );

            ufuncs = [
                new SMTFunctionUninterpreted(this.generateDesCallNameUsing(ltype, "skolem_list_size", code), ufpickargs, this.nattype),
                new SMTFunctionUninterpreted(this.generateConsCallNameUsing(ltype, "skolem_list_index", code), ufpickargs, this.nattype)
            ];  
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
            cons: { cname: this.generateConsCallNameUsing_Direct(ltype, "filter", code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, "filter", code, "l"), ftype: ltype }, { fname: this.generateULIFieldUsingFor(ltype, "filter", code, "isq"), ftype: new SMTType("ISequence") }] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallNameUsing(ltype, "filter", code), [{ vname: "l", vtype: ltype }, { vname: "isq", vtype: new SMTType("ISequence") }, { vname: "osize", vtype: this.nattype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: ufuncs
        };
    }

    ////////
    //Map
    emitConstructorMap(ltype: SMTType, mtype: MIRType, code: string, pcode: MIRPCode, sl: SMTVar, count: SMTVar): SMTConstructorGenCode {
        const lcons = this.temitter.getSMTConstructorName(mtype).cons;

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedfields = lambdainfo.params.slice(1).map((p) => {
            return { fname: this.generateULIFieldUsingFor(ltype, "map", code, p.name), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)) }
        });

        const ffunc = this.temitter.generateResultTypeConstructorSuccess(mtype,
            new SMTCallSimple(lcons, [
                count,
                new SMTCallSimple(this.generateConsCallName_Direct(ltype, "map"), [sl])
            ])
        );

        return {
            cons: { cname: this.generateConsCallNameUsing_Direct(ltype, "map", code), cargs: [{ fname: this.generateULIFieldUsingFor(ltype, "map", code, "l"), ftype: ltype }, ...capturedfields] },
            ulitype: this.generateULITypeFor(ltype),
            if: [new SMTFunction(this.generateConsCallNameUsing(ltype, "map", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
            uf: []
        };
    }

    ////////
    //Get
    emitDestructorGet_Slice(getop: string, ltype: SMTType, ll: SMTVar, n: SMTVar): SMTExp {
        return new SMTCallSimple(getop, [
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
                    new SMTCallSimple(getop, [l1v, n]),
                    new SMTCallSimple(getop, [l2v, new SMTCallSimple("bvsub", [n, l1sv])])
                )
            )
        );
    }

    emitDestructorGet_K(ltype: SMTType, ll: SMTVar, n: SMTVar, k: number): SMTExp {
        if (k === 1) {
            return this.generateGetULIFieldFor(ltype, `_${k}`, `idx${0}`, ll);
        }
        else {
            let kops: { test: SMTExp, result: SMTExp }[] = [];

            for (let i = 0; i < k - 1; ++i) {
                kops.push({
                    test: new SMTCallSimple("=", [n, new SMTConst(`${i}`)]),
                    result: this.generateGetULIFieldFor(ltype, `_${k}`, `idx${i}`, ll)
                });
            }
            
            const klast = this.generateGetULIFieldFor(ltype, `_${k}`, `idx${k - 1}`, ll)
            return new SMTCond(
                kops,
                klast
            );
        }
    }

    emitDestructorGet_Filter(getop: string, ltype: SMTType, code: string, pcode: MIRPCode, ll: SMTVar, n: SMTVar): SMTExp {
        if (this.vopts.SimpleQuantifierMode) {
            const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
            const capturedfieldlets = lambdainfo.params.slice(1).map((p) => {
                return { vname: "c@" + p.name, value: this.generateGetULIFieldUsingFor(ltype, "filter", code, p.name, ll) };
            });

            return new SMTLet("@olist", this.generateGetULIFieldUsingFor(ltype, "filter", code, "l", ll),
                new SMTLetMulti(capturedfieldlets,
                    new SMTLet("@nn", this.generateListIndexPickCall_Kth(this.generateConsCallNameUsing(ltype, "skolem_list_index", code), new SMTVar("@olist"), n, capturedfieldlets.map((cfl) => new SMTVar(cfl.vname))),
                        new SMTCallSimple(getop, [new SMTVar("@olist"), new SMTVar("@nn")])
                    )
                )
            );
        }
        else {
            return new SMTLet("@olist", this.generateGetULIFieldUsingFor(ltype, "filter", code, "l", ll),
                new SMTCallSimple(getop, [new SMTVar("@olist"), new SMTCallSimple("ISequence@get", [this.generateGetULIFieldUsingFor(ltype, "filter", code, "irv", ll), n])])
            );
        }
    }

    emitDestructorGet_Map(ltype: SMTType, ctype: MIRType, srcltype: SMTType, ll: SMTVar, n: SMTVar, code: string, pcode: MIRPCode): SMTExp {
        const getop = this.generateDesCallName(srcltype, "get");

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedfieldlets = lambdainfo.params.slice(1).map((p) => {
            return { vname: "c@" + p.name, value: this.generateGetULIFieldUsingFor(ltype, "map", code, p.name, ll) };
        });

        return new SMTLet("@olist", this.generateGetULIFieldUsingFor(ltype, "map", code, "l", ll),
            new SMTLetMulti(capturedfieldlets,
                this.generateLambdaCallKnownSafe(code, ctype, [new SMTCallSimple(getop, [new SMTVar("@olist"), n])], capturedfieldlets.map((cfl) => new SMTVar(cfl.vname)))
            )
        );
    }

    emitDestructorGet(ltype: SMTType, ctype: MIRType, sl: SMTVar, n: SMTVar, consopts: RequiredListConstructors): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get");
        const llv = new SMTVar("@list_contents");

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
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "havoc")}`, [llv]),
                result: this.temitter.generateResultGetSuccess(ctype, new SMTCallGeneral("[PLACEHOLDER GENERATE API HAVOC -- get path field as arg]", []))
            }); 
        }

        if(consopts.fill) {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallName_Direct(ltype, "fill")}`, [llv]),
                result: this.generateGetULIFieldFor(ltype, "fill", "v", llv)
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
                    result: this.emitDestructorGet_K(ltype, llv, n, k)
                })
            }
        });
        
        consopts.filter.forEach((pcode, code) => {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallNameUsing_Direct(ltype, "filter", code)}`, [llv]),
                result: this.emitDestructorGet_Filter(getop, ltype, code, pcode, llv, n)
            })
        });

        consopts.map.forEach((omi, code) => {
            tsops.push({
                test: new SMTCallSimple(`is-${this.generateConsCallNameUsing_Direct(ltype, "map", code)}`, [llv]),
                result: this.emitDestructorGet_Map(ltype, ctype, omi[1], llv, n, code, omi[0])
            })
        });

        const ffunc = new SMTLetMulti([{ vname: "@list_contents", value: this.generateListContentsCall(sl, ltype) }],
            new SMTCond(tsops.slice(0, tsops.length - 1), tsops[tsops.length - 1].result)
        );

        return {
            if: [new SMTFunction(this.generateDesCallName(ltype, "get"), [{ vname: "l", vtype: ltype }, { vname: "n", vtype: this.nattype}], undefined, 0, this.temitter.getSMTTypeFor(ctype), ffunc)],
            uf: []
        };
    }

    ////////
    //SafeCheck
    emitSafeCheckPred(ltype: SMTType, mtype: MIRType, sl: SMTVar, count: SMTVar, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const restype = this.temitter.getMIRType("NSCore::Bool");

        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [sl, new SMTVar("@n")]);

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

        if (this.safecalls.has(code)) {
            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "safeCheckPred", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(mtype), this.temitter.generateResultTypeConstructorSuccess(mtype, sl))],
                uf: []
            };
        }
        else {
            const tecase = new SMTExists([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), count]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, [getcall], capturedargs), 
                        this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))
                    ])
                ])
            );

            const gecase = new SMTExists([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), count]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, [getcall], capturedargs), 
                        this.temitter.generateErrorResultAssert(restype)
                    ])
                ])
            );

            const ffunc = new SMTCond([
                { test: tecase, result: this.temitter.generateResultTypeConstructorError(mtype, new SMTConst("ErrorID_Target")) },
                { test: gecase, result: this.temitter.generateErrorResultAssert(mtype) }
            ],
                this.temitter.generateResultTypeConstructorSuccess(mtype, sl)
            );

            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "safeCheckPred", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
                uf: []
            };
        }
    }

    emitSafeCheckFn(ltype: SMTType, mtype: MIRType, restype: MIRType, sl: SMTVar, count: SMTVar, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [sl, new SMTVar("@n")]);

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

        if (this.safecalls.has(code)) {
            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "safeCheckFn", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(mtype), this.temitter.generateResultTypeConstructorSuccess(mtype, sl))],
                uf: []
            };
        }
        else {
            const tecase = new SMTExists([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), count]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, [getcall], capturedargs), 
                        this.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))
                    ])
                ])
            );

            const gecase = new SMTExists([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), count]),
                    new SMTCallSimple("=", [
                        this.generateLambdaCallGeneral(code, restype, [getcall], capturedargs), 
                        this.temitter.generateErrorResultAssert(restype)
                    ])
                ])
            );

            const ffunc = new SMTCond([
                { test: tecase, result: this.temitter.generateResultTypeConstructorError(mtype, new SMTConst("ErrorID_Target")) },
                { test: gecase, result: this.temitter.generateErrorResultAssert(mtype) }
            ],
                this.temitter.generateResultTypeConstructorSuccess(mtype, sl)
            );

            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "safeCheckFn", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.temitter.generateResultType(mtype), ffunc)],
                uf: []
            };
        }
    }

    ////////
    //ISequence
    emitDestructorISequence(ltype: SMTType, mtype: MIRType, ctype: MIRType, sl: SMTVar, count: SMTVar, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        if (this.vopts.SimpleQuantifierMode) {
            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "isequence", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, new SMTType(`$Result_ISequence`), new SMTCallSimple("$Result_ISequence@success", [new SMTConst("ISequence@empty")]))],
                uf: []
            };
        }
        else {
            const cvar = "@cseq";
            const getop = this.generateDesCallName(ltype, "get");

            const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
            const ufpickargs = [ltype, this.nattype, ...lambdainfo.params.slice(2).map((p) => this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)))];
            const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

            const cff = new SMTFunctionUninterpreted(this.generateConsCallNameUsing(new SMTType("ISequence"), "ISequence@@cons", code), [ltype,... ufpickargs], new SMTType("ISequence"));

            //size(res) <= size(arg0)
            const assertsize = new SMTCallSimple("bvule", [new SMTCallSimple("ISequence@size", [new SMTVar(cvar)]), count]);

            //\forall n \in [0, size(res)) get(res) < size(arg0)
            const assertrange = new SMTCallSimple("ISequence@assertValuesRange", [new SMTVar(cvar), count]);
            
            //sorted constraint
            const assertsorted = new SMTCallSimple("ISequence@assertSorted", [new SMTVar(cvar)]);

            //\forall j (j \in [lower, upper) /\ p(get(arg0, j))) => (\exists n \in [0, size(res)) /\ get(res, n) = j)
            const fromassert = new SMTForAll([{ vname: "@j", vtype: this.nattype }],
                new SMTCallSimple("=>", [
                    new SMTCallSimple("and", [
                        new SMTCallSimple("bvult", [new SMTVar("@j"), count]),
                        this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTCallSimple(getop, [sl, new SMTVar("@j")])], capturedargs)
                    ]),
                    new SMTExists([{ vname: "@n", vtype: this.nattype }],
                        new SMTCallSimple("and", [
                            new SMTCallSimple("bvult", [new SMTVar("@n"), new SMTCallSimple("ISequence@size", [new SMTVar(cvar)])]),
                            new SMTCallSimple("=", [
                                new SMTCallSimple("ISequence@get", [new SMTVar(cvar), new SMTVar("@n")]),
                                new SMTVar("@j")
                            ])
                        ])
                    )
                ])
            );

            //\forall n (n \in [0, size(res)), get(res, n) = j) => p(get(arg0, j))) --- j \in [lower, upper) is checked by the ISequence@assertValuesRange action
            const toassert = new SMTForAll([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("=>", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), new SMTCallSimple("ISequence@size", [new SMTVar(cvar)])]),
                    this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTCallSimple(getop, [sl, new SMTCallSimple("ISequence@get", [new SMTVar(cvar), new SMTVar("@n")])])], capturedargs)
                ])
            );

            const icons = new SMTCallSimple(this.generateConsCallNameUsing(new SMTType("ISequence"), "ISequence@@cons", code), [sl, ...capturedargs]);

            const fbody = new SMTLet(cvar, icons,
                new SMTIf(
                    new SMTCallSimple("and", [assertsize, assertrange, assertsorted, fromassert, toassert]),
                    new SMTCallSimple("$Result_ISequence@success", [new SMTVar(cvar)]),
                    new SMTCallSimple("$Result_ISequence@error", [new SMTConst("ErrorID_AssumeCheck")])
                )
            );

            return {
                if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "isequence", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype }], undefined, 0, new SMTType(`$Result_ISequence`), fbody)],
                uf: [cff]
            };
        }
    }

    ////////
    //HasPredCheck
    emitDestructorHasPredCheck(ltype: SMTType, sl: SMTVar, count: SMTVar, code: string, pcode: MIRPCode): SMTDestructorGenCode {
        const getop = this.generateDesCallName(ltype, "get");
        const getcall = new SMTCallSimple(getop, [sl, new SMTVar("@n")]);

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

        const ffunc = this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Bool"),
            new SMTExists([{ vname: "@n", vtype: this.nattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("@n"), count]),
                    this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [getcall], capturedargs)
                ])
            )
        );

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "hasPred", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.booltype, ffunc)],
            uf: []
        };
    }

    ////////
    //FindIndexOf
    emitDestructorFindIndexOf(ltype: SMTType, code: string, pcode: MIRPCode, sl: SMTVar, osize: SMTVar): SMTDestructorGenCode {
        const [nn, suf] = this.emitDestructorFindIndexOf_Shared(ltype, code, pcode, sl, osize, new SMTConst("BNat@zero"));

        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.vopts.SimpleQuantifierMode) {
            ffunc = nn
        }
        else {
            const getop = this.generateDesCallName(ltype, "get");

            const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
            const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

            ffunc = new SMTIf(
                new SMTForAll([{ vname: "@j", vtype: this.nattype }],
                    new SMTCallSimple("=>", [
                        new SMTCallSimple("bvult", [new SMTVar("@j"), this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Nat"), nn)]),
                        new SMTCallSimple("not", [this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTCallSimple(getop, [sl, new SMTVar("@j")])], capturedargs)])
                    ])
                ),
                nn,
                this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
            );
        }

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "findIndexOf", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.nattype, ffunc)],
            uf: [suf]
        };
    }

    ////////
    //FindLastIndexOf
    emitDestructorFindIndexOfLast(ltype: SMTType, code: string, pcode: MIRPCode, sl: SMTVar, osize: SMTVar): SMTDestructorGenCode {
        const [nn, suf] = this.emitDestructorFindIndexOf_Shared(ltype, code, pcode, sl, osize, new SMTConst("BNat@max"));

        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.vopts.SimpleQuantifierMode) {
            ffunc = nn
        }
        else {
            const getop = this.generateDesCallName(ltype, "get");

            const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
            const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

            ffunc = new SMTIf(
                new SMTForAll([{ vname: "@j", vtype: this.nattype }],
                    new SMTCallSimple("=>", [
                        new SMTCallSimple("bvult", [this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Nat"), nn), new SMTVar("@j")]),
                        new SMTCallSimple("not", [this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTCallSimple(getop, [sl, new SMTVar("@j")])], capturedargs)])
                    ])
                ),
                nn,
                this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
            );
        }

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "findIndexOfLast", code), [{ vname: "l", vtype: ltype }, { vname: "count", vtype: this.nattype}], undefined, 0, this.nattype, ffunc)],
            uf: [suf]
        };
    }

    ////////
    //CountIf
    emitDestructorCountIf(ltype: SMTType, code: string, pcode: MIRPCode, sl: SMTVar, isq: SMTVar, osize: SMTVar): SMTDestructorGenCode {
        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const capturedparams = pcode.cargs.map((arg) => new SMTVar(arg));
        const ufpickargs = [ltype, this.nattype, ...lambdainfo.params.slice(1).map((p) => this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)))];

        let ffunc: SMTExp = new SMTConst("[UNDEFINED]");
        if (this.vopts.SimpleQuantifierMode) {
            ffunc = new SMTLet("@rsize", this.generateListSize_1_to_Max_m1_PickCall(this.generateDesCallNameUsing(ltype, "skolem_list_size", code), sl, osize, capturedparams),
                this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Nat"), new SMTVar("@rsize"))
            );
        }
        else {
            ffunc = this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Nat"), new SMTCallSimple("ISequence@size", [isq]));
        }

        return {
            if: [new SMTFunction(this.generateDesCallNameUsing(ltype, "countIf", code), [{ vname: "l", vtype: ltype }, { vname: "isq", vtype: new SMTType("ISequence") }, { vname: "count", vtype: this.nattype}], undefined, 0, this.nattype, ffunc)],
            uf: [new SMTFunctionUninterpreted(this.generateDesCallNameUsing(ltype, "skolem_list_size", code), ufpickargs, this.nattype)]
        };
    }

    private emitDestructorFindIndexOf_Shared(ltype: SMTType, code: string, pcode: MIRPCode, sl: SMTVar, osize: SMTVar, k: SMTExp): [SMTExp, SMTFunctionUninterpreted] {
        const getop = this.generateDesCallName(ltype, "get");

        const lambdainfo = this.temitter.assembly.invokeDecls.get(pcode.code) as MIRInvokeBodyDecl;
        const ufpickargs = [ltype, this.nattype, ...lambdainfo.params.slice(1).map((p) => this.temitter.getSMTTypeFor(this.temitter.getMIRType(p.type)))];
        const capturedargs = lambdainfo.params.slice(1).map((p) => new SMTVar(p.name));

        const findidx =
            new SMTLet("@nn", this.generateListIndexPickCall_Kth(this.generateConsCallNameUsing(ltype, "skolem_list_index", code), sl, k, capturedargs),
                new SMTIf(new SMTCallSimple("bvult", [new SMTVar("@nn"), osize]),
                    new SMTLet("@getnn", new SMTCallSimple(getop, [sl, new SMTVar("@nn")]),
                        new SMTIf(this.generateLambdaCallKnownSafe(code, this.temitter.getMIRType("NSCore::Bool"), [new SMTVar("@getnn")], capturedargs),
                            this.temitter.generateResultTypeConstructorSuccess(this.temitter.getMIRType("NSCore::Nat"), new SMTVar("@nn")),
                            this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
                        )
                    ),
                    this.temitter.generateErrorResultAssert(this.temitter.getMIRType("NSCore::Nat"))
                )
            );

        return [
            findidx,
            new SMTFunctionUninterpreted(this.generateConsCallNameUsing(ltype, "skolem_list_index", code), ufpickargs, this.nattype)
        ];
    }

    private generateListSize_1_to_Max_m1_PickCall(ctxname: string, sl: SMTVar, osize: SMTVar, cargs: SMTExp[]): SMTExp {
        return new SMTLet("@skolem_size", new SMTCallSimple(ctxname, [sl, osize, ...cargs]),
            new SMTIf(new SMTCallSimple("and", [
                new SMTCallSimple("bvugt", [new SMTConst("BNat@zero"), new SMTVar("@skolem_size")]),
                new SMTCallSimple("bvult", [new SMTVar("@skolem_size"), osize]),
            ]),
                new SMTVar("@skolem_size"),
                new SMTConst("BNat@one")
            )
        );
    }

    private generateListIndexPickCall_Kth(ctxname: string, sl: SMTVar, k: SMTExp, capturedargs: SMTVar[]): SMTExp {
        return new SMTCallSimple(ctxname, [sl, k, ...capturedargs]);
    }

    private generateLambdaCallKnownSafe(code: string, restype: MIRType, args: SMTExp[], cargs: SMTExp[]): SMTExp {
        if(this.safecalls.has(code)) {
            return new SMTCallSimple(this.temitter.mangle(code), [...args, ...cargs]);
        }
        else {
            return this.temitter.generateResultGetSuccess(restype, new SMTCallGeneral(this.temitter.mangle(code), [...args, ...cargs]));
        }
    }

    private generateLambdaCallGeneral(code: string, restype: MIRType, args: SMTExp[], cargs: SMTExp[]): SMTExp {
        return new SMTCallGeneral(this.temitter.mangle(code), [...args, ...cargs]);
    }
}

export {
    ListOpsManager
};
