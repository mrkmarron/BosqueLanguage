//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { BSQRegex } from "../../ast/bsqregex";
import { unescapeLiteralString } from "../../ast/parser";

import { MIRAssembly, MIRConceptType, MIREntityType, MIREntityTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRRecordType, MIRSpecialTypeCategory, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { constructCallGraphInfo, markSafeCalls } from "../../compiler/mir_callg";
import { MIRInvokeKey, MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTBodyEmitter } from "./smtbody_emitter";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTAssembly, SMTConstantDecl, SMTEntityDecl, SMTEphemeralListDecl, SMTFunction, SMTFunctionUninterpreted, SMTListDecl, SMTModelState, SMTRecordDecl, SMTTupleDecl } from "./smt_assembly";
import { SMTCallGeneral, SMTCallSimple, SMTCond, SMTConst, SMTExists, SMTExp, SMTForAll, SMTIf, SMTLet, SMTLetMulti, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

const BuiltinEntityDeclNames = [
    "None",
    "Bool",
    "Int",
    "Nat",
    "BigInt",
    "BigNat",
    "Rational",
    "Float",
    "Decimal",
    "String",
    "Regex"
];

class SMTEmitter {
    readonly temitter: SMTTypeEmitter;
    readonly bemitter: SMTBodyEmitter;
    readonly assembly: SMTAssembly;

    private lastVInvokeIdx = 0;
    private lastVOperatorIdx = 0;
    private lastVEntityUpdateIdx = 0;

    constructor(temitter: SMTTypeEmitter, bemitter: SMTBodyEmitter, assembly: SMTAssembly) {
        this.temitter = temitter;
        this.bemitter = bemitter;
        this.assembly = assembly;
    }

    private static readonly _s_intRe = /^(-)?(0|[1-9][0-9]*)i$/;
    private static readonly _s_natRe = /^(0|[1-9][0-9]*)n$/;

    private static readonly _s_floatRe = /^(-)?([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f$/;
    private static readonly _s_decimalRe = /^(-)?([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d$/;

    private static readonly _s_bigintRe = /^(-)?(0|[1-9][0-9]*)I$/;
    private static readonly _s_bignatRe = /^(0|[1-9][0-9]*)N$/;
    private static readonly _s_rationalRe = /^(-)?(0|[1-9][0-9]*)|(0|[1-9][0-9]*)\/([1-9][0-9]*)R$/;

    //private static readonly _s_stringRe = /^"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"$/u;
    private static readonly _s_typedStringRe = /^'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/u;

    private generateAPITypeConstructorFunction_Primitive(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        if (this.temitter.isType(tt, "NSCore::None")) {
            return [new SMTConst("bsq_none@literal"), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Bool")) {
            return [new SMTCallSimple("BBool@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Int")) {
            return [new SMTCallSimple("BInt@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Nat")) {
            return [new SMTCallSimple("BNat@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::BigInt")) {
            return [new SMTCallSimple("BBigInt@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::BigNat")) {
            return [new SMTCallSimple("BBigNat@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Float")) {
            return [new SMTCallSimple("BFloat@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Decimal")) {
            return [new SMTCallSimple("BDecimal@UFCons_API", [depthexp, widthexp]), false];
        }
        else if (this.temitter.isType(tt, "NSCore::Rational")) {
            return [new SMTCallSimple("BRational@UFCons_API", [depthexp, widthexp]), false];
        }
        else {
            const sstr = new SMTCallSimple("BString@UFCons_API", [depthexp, widthexp]);
            const tstr = this.bemitter.generateTempName();

            const chksize = new SMTLet(tstr, sstr, 
                new SMTIf(
                    new SMTCallSimple("<=", [new SMTCallSimple("str.len", [new SMTVar(tstr)]), new SMTConst(`${this.bemitter.vopts.ISize}`)]),
                    this.temitter.generateResultTypeConstructorSuccess(tt, new SMTVar(tstr)),
                    this.bemitter.generateErrorAssertFact(tt)
                )
            );

            return [chksize, true];
        }
    }

    private generateAPITypeConstructorFunction_TypedNumber(tt: MIRType, depthexp: SMTExp): [SMTExp, boolean] {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
        const mf = this.bemitter.assembly.fieldDecls.get("v") as MIRFieldDecl;
        const mftype = this.temitter.getMIRType(mf.declaredType);
        
        const bcreate = this.generateAPITypeConstructorFunction_Primitive(mftype, new SMTCallSimple("bvadd", [depthexp, new SMTConst("BNat@one")]), new SMTConst("BNat@zero"));
        return [new SMTCallSimple(this.temitter.mangle(tdecl.consfunc), [bcreate[0]]), !this.bemitter.isSafeConstructorInvoke(tt)];
    }

    private generateAPITypeConstructorFunction_ValidatedString(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        const sstr = new SMTCallSimple("BString@UFCons_API", [depthexp, widthexp]);
        const svar = this.bemitter.generateTempName();

        const vre = this.bemitter.assembly.validatorRegexs.get(tt.trkey) as BSQRegex;
        const lre = vre.compileToSMTValidator(this.bemitter.vopts.StringOpt === "ASCII");

        const lenok = new SMTCallSimple("<=", [new SMTCallSimple("str.len", [new SMTVar(svar)]), new SMTConst(`${this.bemitter.vopts.ISize}`)]);
        const accept = new SMTCallSimple("str.in.re", [new SMTConst(lre), new SMTVar(svar)]);
        const construct = new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, [new SMTVar(svar)]);

        return [
            new SMTLet(svar, sstr,
                new SMTIf(new SMTCallSimple("and", [lenok, accept]),
                    this.temitter.generateResultTypeConstructorSuccess(tt, construct),
                    this.bemitter.generateErrorAssertFact(tt)
                )
            ),
            true
        ];
    }

    private generateAPITypeConstructorFunction_Tuple(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        const ttuple = tt.options[0] as MIRTupleType;

        const ctors = ttuple.entries.map((ee, i) => {
            const cc = this.generateAPITypeConstructorFunction(ee.type, new SMTCallSimple("bvadd", [depthexp, new SMTConst("BNat@one")]), new SMTConst(`(_ bv${i} ${this.bemitter.vopts.ISize})`));
            const ccvar = this.bemitter.generateTempName();
            const chkfun = cc[1] ? this.temitter.generateResultIsSuccessTest(tt, new SMTVar(ccvar)) : undefined;
            const access = cc[1] ? this.temitter.generateResultGetSuccess(ee.type, new SMTVar(ccvar)) : new SMTVar(ccvar);

            return { ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const anyerror = ctors.some((ctor) => ctor.chk !== undefined);
        if(!anyerror) {
            return [new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)), false];
        }
        else {
            return [
                new SMTLetMulti(
                    ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc[0] }; }),
                    new SMTIf(
                        new SMTCallSimple("and", ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)),
                        new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)),
                        this.bemitter.generateErrorAssertFact(tt)
                    )
                ),
                true
            ];
        }
    }

    private generateAPITypeConstructorFunction_Record(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        const trecord = tt.options[0] as MIRRecordType;

        const ctors = trecord.entries.map((ee, i) => {
            const cc = this.generateAPITypeConstructorFunction(ee.type, new SMTCallSimple("bvadd", [depthexp, new SMTConst("BNat@one")]), new SMTConst(`(_ bv${i} ${this.bemitter.vopts.ISize})`));
            const ccvar = this.bemitter.generateTempName();
            const chkfun = cc[1] ? this.temitter.generateResultIsSuccessTest(tt, new SMTVar(ccvar)) : undefined;
            const access = cc[1] ? this.temitter.generateResultGetSuccess(ee.type, new SMTVar(ccvar)) : new SMTVar(ccvar);

            return { pname: ee.name, ccvar: ccvar, cc: cc, chk: chkfun, access: access };
        });

        const anyerror = ctors.some((ctor) => ctor.chk !== undefined);
        if(!anyerror) {
            return [new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)), false];
        }
        else {
            return [
                new SMTLetMulti(
                    ctors.map((ctor) => { return { vname: ctor.ccvar, value: ctor.cc[0] }; }),
                    new SMTIf(
                        new SMTCallSimple("and", ctors.filter((ctor) => ctor.chk !== undefined).map((ctor) => ctor.chk as SMTExp)),
                        new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, ctors.map((ctor) => ctor.access)),
                        this.bemitter.generateErrorAssertFact(tt)
                    )
                ),
                true
            ];
        }
    }

    private generateAPITypeConstructorFunction_List(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        const smttt = this.temitter.getSMTTypeFor(tt);
        const stypeinfo = (this.temitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl).specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[];
        const ctype = this.temitter.getMIRType((stypeinfo.find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);
        const smtnattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));

        const fcons = `@@cons_${smttt.name}_entrypoint`;
        this.bemitter.requiredCollectionConstructors_Operational.push({cname: fcons, oftype: tt.trkey, argtypes: [smtnattype, smtnattype], implkey: "entrypoint"});

        const ressize = this.bemitter.generateTempName();
        const cvar = this.bemitter.generateTempName();
        const resvar = this.bemitter.generateTempName();

        const dwexp = this.generateAPITypeConstructorFunction(ctype, new SMTCallSimple("bvadd", [depthexp, new SMTConst("BNat@one")]), new SMTVar("n"));
        const rwexp = dwexp[1] ? this.temitter.generateResultGetSuccess(ctype, dwexp[0]) : dwexp[0];

        //\forall n, n \in [0, size(l)) get_axiom(res, n) = gen(d + 1, n)
        const eqassert = new SMTForAll([{vname: "n", vtype: smtnattype}], 
            new SMTCallSimple("=>", [
                new SMTCallSimple("bvult", [new SMTVar("n"), new SMTVar(ressize)]),
                new SMTCallSimple("=", [
                    new SMTCallSimple(`${smttt.name}@get_axiom`, [new SMTVar(cvar), new SMTVar("n")]),
                    rwexp
                ])
            ])
        );

        const fsize = new SMTCallSimple("BNat@UFCons_API", [depthexp, widthexp]);
        const icons = new SMTCallSimple(fcons, [depthexp, widthexp]);
        const fres = new SMTCallSimple(`${fcons}@gen`, [new SMTVar(ressize), new SMTVar(cvar)]);

        const crrlistexp = new SMTLet(
            resvar, fres,
            new SMTIf(
                eqassert,
                this.temitter.generateResultTypeConstructorSuccess(tt, new SMTVar(resvar)),
                this.bemitter.generateErrorAssertFact(tt)
            )
        );

        if (dwexp[1]) {
            const echeck = new SMTExists(
                [{ vname: "nn", vtype: smtnattype }],
                new SMTCallSimple("and", [
                    new SMTCallSimple("bvult", [new SMTVar("nn"), new SMTVar(ressize)]),
                    this.temitter.generateResultIsErrorTest(ctype, this.generateAPITypeConstructorFunction(ctype, new SMTCallSimple("bvadd", [depthexp, new SMTConst("BNat@one")]), new SMTVar("nn"))[0])
                ])
            );

            return [
                new SMTLet(
                    ressize, fsize,
                    new SMTIf(
                        echeck,
                        this.bemitter.generateErrorAssertFact(tt),
                        new SMTLet(
                            cvar, icons,
                            crrlistexp
                        )
                    )
                ),
                true
            ];
        }
        else {
            return [
                new SMTLetMulti(
                    [{ vname: ressize, value: fsize }, { vname: cvar, value: icons }],
                    crrlistexp
                ),
                false
            ]
        }
    }

    private generateAPITypeConstructorFunction_Set(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        //
        //TODO: not implemented yet
        //
        assert(false);
        return [new SMTConst("bsq_none@literal"), false];
    }

    private generateAPITypeConstructorFunction_Map(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        //
        //TODO: not implemented yet
        //
        assert(false);
        return [new SMTConst("bsq_none@literal"), false];
    }

    private generateAPITypeConstructorFunction(tt: MIRType, depthexp: SMTExp, widthexp: SMTExp): [SMTExp, boolean] {
        if(tt.options.length !== 1) {
            return [new SMTConst("bsq_none@literal"), false];
        }

        if (this.temitter.isType(tt, "NSCore::None") || this.temitter.isType(tt, "NSCore::Bool")
            || this.temitter.isType(tt, "NSCore::Int") || this.temitter.isType(tt, "NSCore::Nat") || this.temitter.isType(tt, "NSCore::BigInt") || this.temitter.isType(tt, "NSCore::BigNat")
            || this.temitter.isType(tt, "NSCore::Float") || this.temitter.isType(tt, "NSCore::Decimal") || this.temitter.isType(tt, "NSCore::Rational")
            || this.temitter.isType(tt, "NSCore::String")) {
            return this.generateAPITypeConstructorFunction_Primitive(tt, depthexp, widthexp);
        }
        else if (this.temitter.isUniqueTupleType(tt)) {
            return this.generateAPITypeConstructorFunction_Tuple(tt, depthexp, widthexp);
        }
        else if (this.temitter.isUniqueRecordType(tt)) {
            return this.generateAPITypeConstructorFunction_Record(tt, depthexp, widthexp);
        }
        else if (this.temitter.isUniqueEntityType(tt)) {
            const etype = tt.options[0] as MIREntityType;
            const edecl = this.temitter.assembly.entityDecls.get(etype.trkey) as MIREntityTypeDecl;

            if(edecl.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
                return this.generateAPITypeConstructorFunction_TypedNumber(tt, depthexp);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
                return this.generateAPITypeConstructorFunction_ValidatedString(tt, depthexp, widthexp);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                return this.generateAPITypeConstructorFunction_List(tt, depthexp, widthexp);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                return this.generateAPITypeConstructorFunction_Set(tt, depthexp, widthexp);
            }
            else if( edecl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                return this.generateAPITypeConstructorFunction_Map(tt, depthexp, widthexp);
            }
            else {
                return [new SMTConst("bsq_none@literal"), false];
            }
        }
        else {
            return [new SMTConst("bsq_none@literal"), false];
        }
    }

    private parseAPITypeConstructorFunction_Primitive(tt: MIRType, json: string): SMTExp | undefined {
        if (this.temitter.isType(tt, "NSCore::None")) {
            return json === "none" ? new SMTConst("bsq_none@literal") : undefined;
        }
        else if (this.temitter.isType(tt, "NSCore::Bool")) {
            if(json === "true") {
                return new SMTConst("true");
            }
            else if(json === "false") {
                return new SMTConst("false");
            }
            else {
                return undefined;
            }
        }
        else if (this.temitter.isType(tt, "NSCore::Int")) {
            if (!SMTEmitter._s_intRe.test(json)) {
                return undefined;
            }
            else {
                if (!json.startsWith("-")) {
                    return new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${this.bemitter.vopts.ISize})`);
                }
                else {
                    return new SMTCallSimple("bvneg", [new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${this.bemitter.vopts.ISize})`)]);
                }
            }
        }
        else if (this.temitter.isType(tt, "NSCore::Nat")) {
            if (!SMTEmitter._s_natRe.test(json)) {
                return undefined;
            }
            else {
                return new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${this.bemitter.vopts.ISize})`);
            }
        }
        else if (this.temitter.isType(tt, "NSCore::BigInt")) {
            if (!SMTEmitter._s_bigintRe.test(json)) {
                return undefined;
            }
            else {
                if (this.bemitter.vopts.BigXMode === "Int") {
                    return new SMTConst(json.slice(0, json.length - 1));
                }
                else {
                    if (!json.startsWith("-")) {
                        return new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${2 * this.bemitter.vopts.ISize})`);
                    }
                    else {
                        return new SMTCallSimple("bvneg", [new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${2 * this.bemitter.vopts.ISize})`)]);
                    }
                }
            }
        }
        else if (this.temitter.isType(tt, "NSCore::BigNat")) {
            if (!SMTEmitter._s_bignatRe.test(json)) {
                return undefined;
            }
            else {
                if (this.bemitter.vopts.BigXMode === "Int") {
                    return new SMTConst(json.slice(0, json.length - 1));
                }
                else {
                    return new SMTConst(`(_ bv${json.slice(0, json.length - 1)} ${2 * this.bemitter.vopts.ISize})`);
                }
            }
        }
        else if (this.temitter.isType(tt, "NSCore::Float")) {
            if (!SMTEmitter._s_floatRe.test(json)) {
                return undefined;
            }
            else {
                const sv = json.includes(".") ? json.slice(0, json.length - 1) : (json.slice(0, json.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (this.temitter.isType(tt, "NSCore::Decimal")) {
            if (!SMTEmitter._s_decimalRe.test(json)) {
                return undefined;
            }
            else {
                const sv = json.includes(".") ? json.slice(0, json.length - 1) : (json.slice(0, json.length - 1) + ".0");
                return new SMTConst(sv);
            }
        }
        else if (this.temitter.isType(tt, "NSCore::Rational")) {
            if (!SMTEmitter._s_rationalRe.test(json)) {
                return undefined;
            }
            else {
                const spos = json.indexOf("/");
                const num = new SMTConst(json.slice(0, spos) + ".0");
                const denom = new SMTConst(json.slice(spos + 1, json.length - 1) + ".0");
                return new SMTCallSimple("/", [num, denom]);
            }
        }
        else {
            if(json.length > this.bemitter.vopts.ISize) {
                return undefined;
            }
            else {
                assert(this.bemitter.vopts.StringOpt === "ASCII", "We need to UNICODE!!!🦄🚀✨");
            
                return new SMTConst(json);
            }
        }
    }

    private parseAPITypeConstructorFunction_TypedNumber(tt: MIRType, json: string): SMTExp | undefined {
        const tdecl = this.bemitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl;
        const mf = this.bemitter.assembly.fieldDecls.get("v") as MIRFieldDecl;
        const mftype = this.temitter.getMIRType(mf.declaredType);

        const ppos = json.indexOf("_");
        const nvs = ppos !== -1 ? json.slice(0, ppos) : json; 
        const tts = ppos !== -1 ? json.slice(ppos + 1) : tt.trkey;
        
        if(tts !== tt.trkey) {
            return undefined;
        }

        const nv = this.parseAPITypeConstructorFunction_Primitive(mftype, nvs);
        if(nv === undefined) {
            return undefined;
        }

        return new SMTCallSimple(this.temitter.mangle(tdecl.consfunc), [nv]);
    }

    private parseAPITypeConstructorFunction_ValidatedString(tt: MIRType, json: string): SMTExp | undefined {
        const vre = this.bemitter.assembly.validatorRegexs.get(tt.trkey) as BSQRegex;

        const mm = SMTEmitter._s_typedStringRe.exec(json);
        if(mm === null) {
            return undefined;
        }

        const tss = mm[0];
        const argstr = unescapeLiteralString(tss.substring(1, tss.length - 1));
        const ttypes = tss.length !== json.length ? json.slice(tss.length) : tt.trkey;

        if(tt.trkey !== ttypes) {
            return undefined;
        }

        const mtch = new RegExp(vre.compileToJS()).exec(argstr);
        if(json.length > this.bemitter.vopts.ISize || mtch === null || mtch[0].length !== json.length) {
            return undefined;
        }

        const lss = `"${tss.substring(1, tss.length - 1)}"`
        return new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, [new SMTConst(lss)]);
    }

    private parseAPITypeConstructorFunction_Tuple(tt: MIRType, json: any): SMTExp | undefined {
        const ttuple = tt.options[0] as MIRTupleType;

        if(!Array.isArray(json) || ttuple.entries.length !== json.length) {
            return undefined;
        }

        const entries = ttuple.entries.map((entry, i) => this.parseAPIType(entry.type, json[i]));
        if(entries.some((vv) => vv === undefined)) {
            return undefined;
        }

        return new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, entries as SMTExp[]);
    }

    private parseAPITypeConstructorFunction_Record(tt: MIRType, json: any): SMTExp | undefined {
        const trecord = tt.options[0] as MIRRecordType;

        if(trecord.entries.some((entry) => json[entry.name] === undefined)) {
            return undefined;
        }

        const entries = trecord.entries.map((entry) => this.parseAPIType(entry.type, json[entry.name]));
        if(entries.some((vv) => vv === undefined)) {
            return undefined;
        }

        return new SMTCallSimple(this.temitter.getSMTConstructorName(tt).cons, entries as SMTExp[]);
    }

    private parseAPITypeConstructorFunction_List(tt: MIRType, json: any): SMTExp | undefined {
        const stypeinfo = (this.temitter.assembly.entityDecls.get(tt.trkey) as MIREntityTypeDecl).specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[];
        const ctype = this.temitter.getMIRType((stypeinfo.find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);
        
        if(!Array.isArray(json)) {
            return undefined;
        }

        const entries = json.map((entry) => this.parseAPIType(ctype, entry));
        if(entries.some((vv) => vv === undefined)) {
            return undefined;
        }

        const consf = this.bemitter.generateConstructorOfSizeName(tt.trkey, entries.length);
        if (this.bemitter.requiredCollectionConstructors_Literal.find((ee) => ee.cname === consf) === undefined) {
            this.bemitter.requiredCollectionConstructors_Literal.push({ cname: consf, oftype: tt.trkey, argc: entries.length });
        }

        return new SMTCallSimple(`${consf}@gen`, [new SMTConst(`(_ bv${entries.length} ${this.temitter.vopts.ISize})`), new SMTCallSimple(consf, entries as SMTExp[])]);
    }

    private parseAPITypeConstructorFunction_Set(tt: MIRType, json: any): SMTExp | undefined{
        //
        //TODO: not implemented yet
        //
        assert(false);
        return undefined;
    }

    private parseAPITypeConstructorFunction_Map(tt: MIRType, json: any): SMTExp | undefined {
        //
        //TODO: not implemented yet
        //
        assert(false);
        return undefined;
    }

    private parseAPIType(tt: MIRType, json: any): SMTExp | undefined {
        if(tt.options.length !== 1) {
            return undefined;
        }

        if (this.temitter.isType(tt, "NSCore::None") || this.temitter.isType(tt, "NSCore::Bool")
            || this.temitter.isType(tt, "NSCore::Int") || this.temitter.isType(tt, "NSCore::Nat") || this.temitter.isType(tt, "NSCore::BigInt") || this.temitter.isType(tt, "NSCore::BigNat")
            || this.temitter.isType(tt, "NSCore::Float") || this.temitter.isType(tt, "NSCore::Decimal") || this.temitter.isType(tt, "NSCore::Rational")
            || this.temitter.isType(tt, "NSCore::String")) {
            return this.parseAPITypeConstructorFunction_Primitive(tt, json);
        }
        else if (this.temitter.isUniqueTupleType(tt)) {
            return this.parseAPITypeConstructorFunction_Tuple(tt, json);
        }
        else if (this.temitter.isUniqueRecordType(tt)) {
            return this.parseAPITypeConstructorFunction_Record(tt, json);
        }
        else if (this.temitter.isUniqueEntityType(tt)) {
            const etype = tt.options[0] as MIREntityType;
            const edecl = this.temitter.assembly.entityDecls.get(etype.trkey) as MIREntityTypeDecl;

            if(edecl.specialDecls.has(MIRSpecialTypeCategory.TypeDeclNumeric)) {
                return this.parseAPITypeConstructorFunction_TypedNumber(tt, json);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.StringOfDecl)) {
                return this.parseAPITypeConstructorFunction_ValidatedString(tt, json);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                return this.parseAPITypeConstructorFunction_List(tt, json);
            }
            else if (edecl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                return this.parseAPITypeConstructorFunction_Set(tt, json);
            }
            else if( edecl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                return this.parseAPITypeConstructorFunction_Map(tt, json);
            }
            else {
                return undefined;
            }
        }
        else {
            return undefined;
        }
    }

    private processISequenceTypeDecl(idecl: MIREntityTypeDecl) {
        this.bemitter.requiredISequenceConstructors.forEach((isq) => {
            const isqtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(idecl.tkey));
            const nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));
            const ltype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(isq.oftype));

            const argtypes = [ltype, nattype, nattype];
            const ufcons = new SMTFunctionUninterpreted(isq.cname, argtypes, isqtype);

            this.assembly.uninterpfunctions.push(ufcons);
        });
    }

    private processVectorTypeDecl(vdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processListTypeDecl(ldecl: MIREntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(ldecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);
        const mirctype = this.temitter.getMIRType(((ldecl.specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[]).find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);
        const smtctype = this.temitter.getSMTTypeFor(mirctype);
        const nattype = this.temitter.getSMTTypeFor(this.temitter.getMIRType("NSCore::Nat"));

        const lccftype = smttype.name + "$uli";
        const get_axiom = new SMTFunctionUninterpreted(`${smttype.name}@get_axiom`, [new SMTType(lccftype), nattype], smtctype);

        const constructors: { cname: string, cargs: { fname: string, ftype: SMTType }[] }[] = [];
        const getdirectops: { test: SMTExp, result: SMTExp }[] = [];
        
        this.bemitter.requiredCollectionConstructors_Literal
            .sort((a, b) => a.cname.localeCompare(b.cname))
            .forEach((dc) => {
                if(dc.argc === 0) {
                    constructors.push({cname: dc.cname, cargs: []});
                    getdirectops.push({test: new SMTCallSimple(`is-${dc.cname}`, [new SMTVar("lc")]), result: new SMTConst(this.bemitter.generateUFConstantForType(mirctype)) });
                }
                else if (dc.argc === 1) {
                    constructors.push({cname: dc.cname, cargs: [{ fname: `${dc.cname}$arg_0`, ftype: new SMTType(lccftype) }]});
                    getdirectops.push({test: new SMTCallSimple(`is-${dc.cname}`, [new SMTVar("lc")]), result: new SMTCallSimple(`${dc.cname}$arg_0`, [new SMTVar("lc")]) });
                }
                else {
                    let cargs: { fname: string, ftype: SMTType }[] = [];
                    for (let i = 0; i < dc.argc; ++i) {
                        cargs.push({ fname: `${dc.cname}$arg_i`, ftype: new SMTType(lccftype) });
                    }
                    constructors.push({ cname: dc.cname, cargs: cargs });

                    const testexp = new SMTCallSimple(`is-${dc.cname}`, [new SMTVar("lc")]);
                    const lastop = new SMTCallSimple(`${dc.cname}$arg_${dc.argc - 1}`, [new SMTVar("lc")]);
                    let altops: {test: SMTExp, result: SMTExp}[] = [];
                    for (let i = 0; i < dc.argc - 1; ++i) {
                        altops.push({test: new SMTCallSimple("=", [new SMTVar("n"), new SMTConst(`(_ bv${i} ${this.bemitter.vopts.ISize})`)]), result: new SMTCallSimple(`${dc.cname}$arg_${i}`, [new SMTVar("lc")])});
                    }
                    getdirectops.push({test: testexp, result: new SMTCond(altops.reverse(), lastop)});
                }
            });
        
        this.bemitter.requiredCollectionConstructors_Structural
            .sort((a, b) => a.cname.localeCompare(b.cname))
            .forEach((sc) => {
                if(sc.implkey === "list_fill") {
                    constructors.push({cname: sc.cname, cargs: [{ fname: `${sc.cname}$value`, ftype: smtctype }]});
                    getdirectops.push({test: new SMTCallSimple(`is-${sc.cname}`, [new SMTVar("lc")]), result: new SMTCallSimple(`${sc.cname}$value`, [new SMTVar("lc")]) });
                }
                else if (sc.implkey === "list_rangeofint") {
                    constructors.push({cname: sc.cname, cargs: [{ fname: `${sc.cname}$lb`, ftype: smtctype }, { fname: `${sc.cname}$ub`, ftype: smtctype }]});
                    getdirectops.push({test: new SMTCallSimple(`is-${sc.cname}`, [new SMTVar("lc")]), result: new SMTCallSimple("bvadd", [new SMTCallSimple(`${sc.cname}$lb`, [new SMTVar("lc")]), new SMTVar("n")]) });
                }
                else {
                    assert(sc.implkey === "list_rangeofnat");

                    constructors.push({cname: sc.cname, cargs: [{ fname: `${sc.cname}$lb`, ftype: smtctype }, { fname: `${sc.cname}$ub`, ftype: smtctype }]});
                    getdirectops.push({test: new SMTCallSimple(`is-${sc.cname}`, [new SMTVar("lc")]), result: new SMTCallSimple("bvadd", [new SMTCallSimple(`${sc.cname}$lb`, [new SMTVar("lc")]), new SMTVar("n")]) });
                }
            });
    
        //
        //TODO: would be nice if we could make these macros but for now we just rely on quantifier magic
        //
        this.bemitter.requiredCollectionConstructors_Operational
            .sort((a, b) => a.cname.localeCompare(b.cname))
            .forEach((oc) => {
                switch(oc.implkey) {
                    case "entrypoint": {
                        constructors.push({cname: oc.cname, cargs: [
                            {fname: `${oc.cname}$depth`, ftype: oc.argtypes[0]},
                            {fname: `${oc.cname}$width`, ftype: oc.argtypes[1]},
                        ]});
                        break;
                    }
                    case "list_zip": {
                        constructors.push({cname: oc.cname, cargs: [
                            {fname: `${oc.cname}$l`, ftype: oc.argtypes[0]},
                            {fname: `${oc.cname}$u`, ftype: oc.argtypes[1]},
                        ]});
                        break;
                    }
                    case "list_slice_helper": {
                        constructors.push({cname: oc.cname, cargs: [
                            {fname: `${oc.cname}$l`, ftype: oc.argtypes[0]},
                            {fname: `${oc.cname}$start`, ftype: oc.argtypes[1]},
                            {fname: `${oc.cname}$end`, ftype: oc.argtypes[2]}
                        ]});
                        break;
                    }
                    case "list_append_helper": {
                        constructors.push({cname: oc.cname, cargs: [
                            {fname: `${oc.cname}$l`, ftype: oc.argtypes[0]},
                            {fname: `${oc.cname}$u`, ftype: oc.argtypes[1]},
                            {fname: `${oc.cname}$size`, ftype: oc.argtypes[2]}
                        ]});
                        break;
                    }
                    default: {
                        assert(false);
                    }
                }
            });
            

        this.bemitter.requiredCollectionConstructors_Computational
            .sort((a, b) => a.cname.localeCompare(b.cname))
            .forEach((cc) => {
                switch(cc.implkey) {
                    case "list_filter_helper": {
                        constructors.push({cname: cc.cname, cargs: [
                            {fname: `${cc.cname}$l`, ftype: cc.argtypes[0]},
                            {fname: `${cc.cname}$start`, ftype: cc.argtypes[1]},
                            {fname: `${cc.cname}$end`, ftype: cc.argtypes[2]},
                            {fname: `${cc.cname}$il`, ftype: cc.argtypes[3]}
                        ]});
                        break;
                    }
                    case "list_map_helper": {
                        constructors.push({cname: cc.cname, cargs: [
                            {fname: `${cc.cname}$l`, ftype: cc.argtypes[0]},
                            {fname: `${cc.cname}$start`, ftype: cc.argtypes[1]},
                            {fname: `${cc.cname}$end`, ftype: cc.argtypes[2]}
                        ]});
                        break;
                    }
                    default: {
                        assert(false);
                    }
                }
            });

        const ttag = `TypeTag_${smttype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
        const isapi = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: [
                { fname: `${smttype.name}@size`, ftype: nattype },
                { fname: `${smttype.name}@uli`, ftype: new SMTType(lccftype) }
            ]
        };

        const getbody = new SMTLet("lc", new SMTCallSimple(`${smttype.name}@uli`, [new SMTVar("l")]), 
            new SMTCond(
                getdirectops,
                new SMTCallSimple(get_axiom.fname, [new SMTVar("lc"), new SMTVar("n")])
            )
        );

        const getdecl = new SMTFunction(`${smttype.name}@get`, [{vname: "l", vtype: smttype}, {vname: "n", vtype: nattype}], undefined, smtctype, getbody);

        const smtdecl = new SMTListDecl(iskey, isapi, lccftype, constructors, get_axiom, smttype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield, getdecl);
        this.assembly.listDecls.push(smtdecl);
    }
        
    private processStackTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processQueueTypeDecl(qdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
       
    private processSetTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processDynamicSetTypeDecl(sdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
        
    private processMapTypeDecl(mdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }
    
    private processDynamicMapTypeDecl(mdecl: MIREntityTypeDecl) {
        //NOT IMPLEMENTED YET
        assert(false);
    }

    private processEntityDecl(edecl: MIREntityTypeDecl) {
        const mirtype = this.temitter.getMIRType(edecl.tkey);
        const smttype = this.temitter.getSMTTypeFor(mirtype);

        const ttag = `TypeTag_${smttype.name}`;
        const iskey = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
        const isapi = this.temitter.assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

        const consfuncs = this.temitter.getSMTConstructorName(mirtype);
        const consdecl = {
            cname: consfuncs.cons, 
            cargs: edecl.fields.map((fd) => {
                return { fname: this.temitter.generateEntityFieldGetFunction(edecl, fd.fkey), ftype: this.temitter.getSMTTypeFor(this.temitter.getMIRType(fd.declaredType)) };
            })
        };

        const smtdecl = new SMTEntityDecl(iskey, isapi, smttype.name, ttag, consdecl, consfuncs.box, consfuncs.bfield);
        this.assembly.entityDecls.push(smtdecl);
    }

    private processVirtualInvokes() {
        for(let i = this.lastVInvokeIdx; i < this.bemitter.requiredVirtualFunctionInvokes.length; ++i) {
            this.bemitter.generateVirtualFunctionInvoke(this.bemitter.requiredVirtualFunctionInvokes[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredVirtualFunctionInvokes.length;

        for(let i = this.lastVOperatorIdx; i < this.bemitter.requiredVirtualOperatorInvokes.length; ++i) {
            this.bemitter.generateVirtualOperatorInvoke(this.bemitter.requiredVirtualOperatorInvokes[i]);
        }
        this.lastVOperatorIdx = this.bemitter.requiredVirtualOperatorInvokes.length;
    }

    private processVirtualEntityUpdates() {
        for(let i = this.lastVEntityUpdateIdx; i < this.bemitter.requiredUpdateVirtualEntity.length; ++i) {
            this.bemitter.generateUpdateEntityFieldVirtual(this.bemitter.requiredUpdateVirtualEntity[i]);
        }
        this.lastVInvokeIdx = this.bemitter.requiredUpdateVirtualEntity.length;
    }

    private initializeSMTAssembly(assembly: MIRAssembly, entrypoint: MIRInvokeKey, callsafety: Map<MIRInvokeKey, { safe: boolean, trgt: boolean }>, maxgas: number) {
        let doneset = new Set<MIRInvokeKey>();
        const cginfo = constructCallGraphInfo([entrypoint], assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();

        for (let i = 0; i < rcg.length; ++i) {
            const cn = rcg[i];
            if(doneset.has(cn.invoke)) {
                continue;
            }

            const cscc = cginfo.recursive.find((scc) => scc.has(cn.invoke));
            const currentSCC = cscc || new Set<string>();
            let worklist = cscc !== undefined ? [...cscc].sort() : [cn.invoke];

            let gasmax: number | undefined = cscc !== undefined ? maxgas : 1;
            for (let gasctr = 1; gasctr <= gasmax; gasctr++) {
                for (let mi = 0; mi < worklist.length; ++mi) {
                    const ikey = worklist[mi];

                    let gas: number | undefined = undefined;
                    let gasdown: number | undefined = undefined;
                    if (gasctr !== gasmax) {
                        gas = gasctr;
                        gasdown = gasctr - 1;
                    }
                    else {
                        gasdown = gasmax - 1;
                    }

                    const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey)) as MIRInvokeDecl;
                    const finfo = this.bemitter.generateSMTInvoke(idcl, currentSCC, gas, gasdown);
                    this.processVirtualInvokes();
                    this.processVirtualEntityUpdates();

                    if (finfo !== undefined) {
                        if (finfo instanceof SMTFunction) {
                            this.assembly.functions.push(finfo);
                        }
                        else {
                            this.assembly.uninterpfunctions.push(finfo);
                        }
                    }

                    const rtype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(idcl.resultType));
                    if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
                        this.assembly.resultTypes.push(({hasFlag: false, rtname: idcl.resultType, ctype: rtype}));
                    }
                }

                if(cscc !== undefined) {
                    cscc.forEach((v) => doneset.add(v));
                }
            }
        }   

        this.bemitter.requiredLoadVirtualTupleIndex.forEach((rvlt) => this.assembly.functions.push(this.bemitter.generateLoadTupleIndexVirtual(rvlt)));
        this.bemitter.requiredLoadVirtualRecordProperty.forEach((rvlr) => this.assembly.functions.push(this.bemitter.generateLoadRecordPropertyVirtual(rvlr)));
        this.bemitter.requiredLoadVirtualEntityField.forEach((rvle) => this.assembly.functions.push(this.bemitter.generateLoadEntityFieldVirtual(rvle)));
        
        this.bemitter.requiredProjectVirtualTupleIndex.forEach((rvpt) => this.assembly.functions.push(this.bemitter.generateProjectTupleIndexVirtual(rvpt)));
        this.bemitter.requiredProjectVirtualRecordProperty.forEach((rvpr) => this.assembly.functions.push(this.bemitter.generateProjectRecordPropertyVirtual(rvpr)));
        this.bemitter.requiredProjectVirtualEntityField.forEach((rvpe) => this.assembly.functions.push(this.bemitter.generateProjectEntityFieldVirtual(rvpe)));
    
        this.bemitter.requiredUpdateVirtualTuple.forEach((rvut) => this.assembly.functions.push(this.bemitter.generateUpdateTupleIndexVirtual(rvut)));
        this.bemitter.requiredUpdateVirtualRecord.forEach((rvur) => this.assembly.functions.push(this.bemitter.generateUpdateRecordPropertyVirtual(rvur)));

        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        
        const iargs = mirep.params.map((param, i) => {
            const mirptype = this.temitter.getMIRType(param.type);

            const vname = this.temitter.mangle(param.name);
            const vtype = this.temitter.getSMTTypeFor(mirptype);
            const vexp = this.generateAPITypeConstructorFunction(mirptype, new SMTConst(`(_ bv${i} ${this.assembly.vopts.ISize})`), new SMTConst("BNat@zero"));

            if (vexp[1]) {
                return { vname: vname, vtype: this.temitter.generateResultType(mirptype), vexp: vexp[0], vchk: this.temitter.generateResultIsSuccessTest(mirptype, new SMTVar(vname)), vinit: this.temitter.generateResultGetSuccess(mirptype, new SMTVar(vname)) };
            }
            else {
                return { vname: vname, vtype: vtype, vexp: vexp[0], vchk: undefined, vinit: new SMTVar(vname) };
            }
        });

        const restype = this.temitter.getMIRType(mirep.resultType);
        const rtype = this.temitter.getSMTTypeFor(restype);
        if (this.assembly.resultTypes.find((rtt) => rtt.ctype.name === rtype.name) === undefined) {
            this.assembly.resultTypes.push(({ hasFlag: false, rtname: mirep.resultType, ctype: rtype }));
        }

        assembly.entityDecls.forEach((edcl) => {
            const mirtype = this.temitter.getMIRType(edcl.tkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype).name}`;

            this.assembly.typeTags.push(ttag);
            if(assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"))) {
                this.assembly.keytypeTags.push(ttag);
            }

            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(edcl.tkey));
            if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({hasFlag: false, rtname: edcl.tkey, ctype: restype}));
            }

            if(edcl.specialDecls.has(MIRSpecialTypeCategory.VectorTypeDecl)) {
                this.processVectorTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.ListTypeDecl)) {
                this.processListTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.StackTypeDecl)) {
                this.processStackTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.QueueTypeDecl)) {
                this.processQueueTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.SetTypeDecl)) {
                this.processSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicSetTypeDecl)) {
                this.processDynamicSetTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.MapTypeDecl)) {
                this.processMapTypeDecl(edcl);
            }
            else if(edcl.specialDecls.has(MIRSpecialTypeCategory.DynamicMapTypeDecl)) {
                this.processDynamicMapTypeDecl(edcl);
            }
            else {
                if(edcl.ns === "NSCore" && edcl.name === "ISequence") {
                    this.processISequenceTypeDecl(edcl);
                }
                else {
                    if(edcl.ns !== "NSCore" || BuiltinEntityDeclNames.find((be) => be[0] === edcl.name) === undefined) {
                        this.processEntityDecl(edcl);
                    }
                }
            }
        });

        this.bemitter.requiredSubtypeTagChecks.forEach((stc) => {
            const occ = stc.oftype.options[0] as MIRConceptType;
            for(let i = 0; i < occ.ckeys.length; ++i) {
                const atname = `AbstractTypeTag_${this.temitter.getSMTTypeFor(this.temitter.getMIRType(occ.ckeys[i]))}`;
                if(!this.assembly.abstractTypes.includes(atname)) {
                    this.assembly.abstractTypes.push(atname);
                }

                assembly.typeMap.forEach((mtype) => {
                    if(this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, stc.t)) {
                        const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype).name}`;

                        if(this.assembly.subtypeRelation.find((ee) => ee.ttype === ttag && ee.atype === atname) === undefined) {
                            const issub = assembly.subtypeOf(mtype, stc.oftype);
                            this.assembly.subtypeRelation.push({ttype: ttag, atype: atname, value: issub});
                        }
                    }
                });
            }
        });

        this.bemitter.requiredIndexTagChecks.forEach((itc) => {
            const itag = `TupleIndexTag_${itc.idx}`;
            if(!this.assembly.indexTags.includes(itag)) {
                this.assembly.indexTags.push(itag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, itc.oftype)) {
                    const ttype = mtype.options[0] as MIRTupleType;
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype).name}`;

                    if (this.assembly.hasIndexRelation.find((ee) => ee.idxtag === itag && ee.atype === ttag) === undefined) {
                        const hasidx = itc.idx < ttype.entries.length;
                        this.assembly.hasIndexRelation.push({ idxtag: itag, atype: ttag, value: hasidx });
                    }
                }
            });
        });

        this.bemitter.requiredRecordTagChecks.forEach((rtc) => {
            const ptag = `RecordPropertyTag_${rtc.pname}`;
            if(!this.assembly.propertyTags.includes(ptag)) {
                this.assembly.propertyTags.push(ptag);
            }

            assembly.typeMap.forEach((mtype) => {
                if (this.temitter.isUniqueType(mtype) && assembly.subtypeOf(mtype, rtc.oftype)) {
                    const ttype = mtype.options[0] as MIRRecordType;
                    const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mtype).name}`;

                    if (this.assembly.hasPropertyRelation.find((ee) => ee.pnametag === ptag && ee.atype === ttag) === undefined) {
                        const haspname = ttype.entries.find((entry) => entry.name === rtc.pname) !== undefined;
                        this.assembly.hasPropertyRelation.push({ pnametag: ptag, atype: ttag, value: haspname });
                    }
                }
            });
        });

        assembly.tupleDecls.forEach((ttup) => {
            const mirtype = this.temitter.getMIRType(ttup.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype).name}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }

            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(ttup.trkey));
            if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({hasFlag: false, rtname: ttup.trkey, ctype: restype}));
            }
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ttup.entries.map((entry, i) => {
                return { fname: this.temitter.generateTupleIndexGetFunction(ttup, i), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.tupleDecls.push(new SMTTupleDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.recordDecls.forEach((trec) => {
            const mirtype = this.temitter.getMIRType(trec.trkey);
            const ttag = `TypeTag_${this.temitter.getSMTTypeFor(mirtype).name}`;
            const iskey = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::KeyType"));
            const isapi = assembly.subtypeOf(mirtype, this.temitter.getMIRType("NSCore::APIType"));

            this.assembly.typeTags.push(ttag);
            if(iskey) {
                this.assembly.keytypeTags.push(ttag);
            }
            
            const restype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(trec.trkey));
            if(this.assembly.resultTypes.find((rtt) => rtt.ctype.name === restype.name) === undefined) {
                this.assembly.resultTypes.push(({hasFlag: false, rtname: trec.trkey, ctype: restype}));
            }

            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = trec.entries.map((entry) => {
                return { fname: this.temitter.generateRecordPropertyGetFunction(trec, entry.name), ftype: this.temitter.getSMTTypeFor(entry.type) };
            });

            this.assembly.recordDecls.push(new SMTRecordDecl(iskey, isapi, smttype.name, ttag, { cname: ops.cons, cargs: consargs }, ops.box, ops.bfield));
        });

        assembly.ephemeralListDecls.forEach((ephl) => {
            const mirtype = this.temitter.getMIRType(ephl.trkey);
            
            const smttype = this.temitter.getSMTTypeFor(mirtype);
            const ops = this.temitter.getSMTConstructorName(mirtype);
            const consargs = ephl.entries.map((entry, i) => {
                return { fname: this.temitter.generateEphemeralListGetFunction(ephl, i), ftype: this.temitter.getSMTTypeFor(entry) };
            });

            this.assembly.ephemeralDecls.push(new SMTEphemeralListDecl(smttype.name, { cname: ops.cons, cargs: consargs }));
        });

        assembly.constantDecls.forEach((cdecl) => {
            const smtname = this.temitter.mangle(cdecl.gkey);
            const consf = this.temitter.mangle(cdecl.value);
            const ctype = this.temitter.getSMTTypeFor(this.temitter.getMIRType(cdecl.declaredType));
            this.assembly.constantDecls.push(new SMTConstantDecl(smtname, ctype, consf));
        });

        this.assembly.maskSizes = this.bemitter.maskSizes;

        const smtcall = this.temitter.mangle(mirep.key);
        const callargs = iargs.map((arg) => arg.vinit);
        const issafe = (callsafety.get(entrypoint) as {safe: boolean, trgt: boolean}).safe;

        let iexp: SMTExp | undefined = undefined;
        let argchk: SMTExp[] | undefined = undefined;
        if(issafe) {
            iexp = this.temitter.generateResultTypeConstructorSuccess(restype, new SMTCallSimple(smtcall, callargs));
        }
        else {
            iexp = new SMTCallGeneral(smtcall, callargs);
            if(mirep.preconditions !== undefined) {
                argchk = mirep.preconditions.map((pc) => {
                    const ispcsafe = (callsafety.get(pc) as {safe: boolean, trgt: boolean}).safe;
                    if(ispcsafe) {
                        return new SMTCallSimple(this.temitter.mangle(pc), callargs); 
                    }
                    else {
                        return new SMTLet(
                            "pcres",
                            new SMTCallGeneral(this.temitter.mangle(pc), callargs),
                            new SMTCallSimple("and", [
                                this.temitter.generateResultIsSuccessTest(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres")),
                                this.temitter.generateResultGetSuccess(this.temitter.getMIRType("NSCore::Bool"), new SMTVar("pcres"))
                            ])
                        )
                    }
                });
            }
        }
        
        this.assembly.model = new SMTModelState(iargs, argchk, this.temitter.generateResultType(restype), iexp);
        this.assembly.allErrors = this.bemitter.allErrors;
    }

    static generateSMTAssemblyForValidate(assembly: MIRAssembly, vopts: VerifierOptions, errorTrgtPos: { file: string, line: number, pos: number }, entrypoint: MIRInvokeKey, maxgas: number): SMTAssembly {
        const callsafety = markSafeCalls([entrypoint], assembly, errorTrgtPos);

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, errorTrgtPos);
        const smtassembly = new SMTAssembly(vopts);

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety, maxgas);

        ////////////
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;
        const restype = temitter.getMIRType(mirep.resultType);

        const eqerrexp = new SMTCallSimple("=", [new SMTVar("@smtres@"), smtemit.temitter.generateResultTypeConstructorError(restype, new SMTConst("ErrorID_Target"))]);
        smtemit.assembly.modes = {
            refute: new SMTCallSimple("not", [eqerrexp]),
            generate: eqerrexp,
            evaluate: ["[INVALID]", new SMTConst("bsq_none")]
        };

        return smtemit.assembly;
    }

    static generateSMTAssemblyEvaluate(assembly: MIRAssembly, vopts: VerifierOptions, entrypoint: MIRInvokeKey, args: any[], maxgas: number): SMTAssembly | undefined {
        const callsafety = markSafeCalls([entrypoint], assembly, { file: "[NO TARGET]", line: -1, pos: -1 });

        const temitter = new SMTTypeEmitter(assembly, vopts);
        const bemitter = new SMTBodyEmitter(assembly, temitter, vopts, callsafety, { file: "[NO TARGET]", line: -1, pos: -1 });
        const smtassembly = new SMTAssembly(vopts);

        let smtemit = new SMTEmitter(temitter, bemitter, smtassembly);
        smtemit.initializeSMTAssembly(assembly, entrypoint, callsafety, maxgas);

        ////////////
        
        const mirep = assembly.invokeDecls.get(entrypoint) as MIRInvokeDecl;

        const cargs = args.map((arg, i) => smtemit.parseAPIType(smtemit.temitter.getMIRType(mirep.params[i].type), arg));
        if (cargs.includes(undefined)) {
            return undefined;
        }

        smtemit.assembly.modes = {
            refute: new SMTConst("false"),
            generate: new SMTConst("false"),
            evaluate: [
                `${entrypoint}(${args.join(", ")})`,
                new SMTCallSimple(temitter.mangle(entrypoint), cargs as SMTExp[])
            ],
        };

        return smtemit.assembly;
    }
}

export {
    SMTEmitter
};
