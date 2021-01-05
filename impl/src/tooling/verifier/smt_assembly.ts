//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { BSQRegex } from "../../ast/bsqregex";
import { SMTExp, SMTType, VerifierOptions } from "./smt_exp";

type SMT2FileInfo = {
    TYPE_TAG_DECLS: string[],
    ABSTRACT_TYPE_TAG_DECLS: string[],
    INDEX_TAG_DECLS: string[],
    PROPERTY_TAG_DECLS: string[],
    SUBTYPE_DECLS: string[],
    TUPLE_HAS_INDEX_DECLS: string[],
    RECORD_HAS_PROPERTY_DECLS: string[],
    KEY_TYPE_TAG_RANK: string[],
    BINTEGRAL_TYPE_ALIAS: string[],
    BINTEGRAL_CONSTANTS: string[],
    BFLOATPOINT_TYPE_ALIAS: string[],
    BFLOATPOINT_CONSTANTS: string[],
    STRING_TYPE_ALIAS: string,
    KEY_TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] }
    EPHEMERAL_DECLS: { decls: string[], constructors: string[] },
    RESULT_INFO: { decls: string[], constructors: string[] },
    MASK_INFO: { decls: string[], constructors: string[] },
    GLOBAL_DECLS: string[],
    UF_DECLS: string[],
    FUNCTION_DECLS: string[],
    GLOBAL_DEFINITIONS: string[]
};

class SMTFunction {
    readonly fname: string;
    readonly args: { vname: string, vtype: SMTType }[];
    readonly mask: string | undefined;
    readonly result: SMTType;

    readonly body: SMTExp;

    constructor(fname: string, args: { vname: string, vtype: SMTType }[], mask: string | undefined, result: SMTType, body: SMTExp) {
        this.fname = fname;
        this.args = args;
        this.mask = mask;
        this.result = result;

        this.body = body;
    }

    emitSMT2(): string {
        const args = this.args.map((arg) => `(${arg.vname} ${arg.vtype})`);
        const body = this.body.emitSMT2("  ");
        return `(define-fun ${this.fname} (${args.join(" ")}${this.mask !== undefined ? this.mask : ""}) ${this.result.name}\n${body}\n)`;
    }
}

class SMTFunctionUninterpreted {
    readonly fname: string;
    readonly args: SMTType[];
    readonly result: SMTType;

    constructor(fname: string, args: SMTType[], result: SMTType) {
        this.fname = fname;
        this.args = args;
        this.result = result;
    }

    emitSMT2(): string {
        return `(declare-fun ${this.fname} (${this.args.map((arg) => arg.name).join(" ")}) ${this.result.name})`;
    }
}

class SMTEntityDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;

    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    readonly invfunc: string | undefined;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string, invfunc: string | undefined) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;

        this.invfunc = invfunc;
    }
}

class SMTTupleDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTRecordDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    constructor(iskeytype: boolean, isapitype: boolean, smtname: string, typetag: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }, boxf: string, ubf: string) {
        this.iskeytype = iskeytype;
        this.isapitype = isapitype;

        this.smtname = smtname;
        this.typetag = typetag;
        this.consf = consf;
        this.boxf = boxf;
        this.ubf = ubf;
    }
}

class SMTEphemeralListDecl {
    readonly smtname: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };

    constructor(smtname: string, consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] }) {
        this.smtname = smtname;
        this.consf = consf;
    }
}

class SMTConstantDecl {
    readonly gkey: string;
    readonly ctype: SMTType;

    readonly consf: string;

    constructor(gkey: string, ctype: SMTType, consf: string) {
        this.gkey = gkey;
        this.ctype = ctype;

        this.consf = consf;
    }
}

class SMTAssembly {
    readonly vopts: VerifierOptions;
    
    entityDecls: SMTEntityDecl[] = [];
    tupleDecls: SMTTupleDecl[] = [];
    recordDecls: SMTRecordDecl[] = [];
    ephemeralDecls: SMTEphemeralListDecl[] = [];

    typeTags: string[] = [];
    abstractTypes: string[] = [];
    indexTags: string[] = [];
    propertyTags: string[] = [];
    keytypeTags: string[] = [];

    subtypeRelation: { ttype: string, atype: string, value: boolean }[] = [];
    hasIndexRelation: { idxtag: string, atype: string, value: boolean }[] = [];
    hasPropertyRelation: { pnametag: string, atype: string, value: boolean }[] = [];

    literalRegexs: BSQRegex[] = [];
    validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    constantDecls: SMTConstantDecl[] = [];
    
    uninterpfunctions: SMTFunctionUninterpreted[] = [];

    maskSizes: Set<number> = new Set<number>();
    resultTypes: { hasFlag: boolean, rtname: string, ctype: SMTType }[] = [];
    functions: SMTFunction[] = [];

    constructor(vopts: VerifierOptions) {
        this.vopts = vopts;
    }

    computeBVMinSigned(bits: bigint): string {
        const bbn = 1n << bits;
        return bbn.toString();
    }

    computeBVMaxSigned(bits: bigint): string {
        const bbn = ~(1n << bits);
        return bbn.toString();
    }

    computeBVMaxUnSigned(bits: bigint): string {
        const bbn = (1n << bits) | ~(1n << bits);
        return bbn.toString();
    }

    generateSMT2AssemblyInfo(): SMT2FileInfo {
        const subtypeasserts = this.subtypeRelation.map((tc) => tc.value ? `(assert (SubtypeOf@ ${tc.ttype} ${tc.atype}))` : `(assert (not (SubtypeOf@ ${tc.ttype} ${tc.atype})))`).sort();
        const indexasserts = this.hasIndexRelation.map((hi) => hi.value ? `(assert (HasIndex@ ${hi.idxtag} ${hi.atype}))` : `(assert (not (HasIndex@ ${hi.idxtag} ${hi.atype})))`).sort();
        const propertyasserts = this.hasPropertyRelation.map((hp) => hp.value ? `(assert (HasProperty@ ${hp.pnametag} ${hp.atype}))` : `(assert (not (HasProperty@ ${hp.pnametag} ${hp.atype})))`).sort();

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `(assert (= (TypeTagRank@ ${ktt}) ${i}))`);

        let integral_type_alias: string[] = [
            `(define-sort BInt () (_ BitVec ${this.vopts.ISize}))`,
            `(define-sort BNat () (_ BitVec ${this.vopts.ISize}))`,
            (this.vopts.BigXMode === "Int" ? "(define-sort BBigInt () Int)" : `(define-sort BBigInt () (_ BitVec ${2 * this.vopts.ISize}))`),
            (this.vopts.BigXMode === "Int" ? "(define-sort BBigNat () Int)" : `(define-sort BBigNat () (_ BitVec ${2 * this.vopts.ISize}))`)
        ];
        let integral_constants: string[] = [
            `(declare-const BInt@zero BInt) (assert (= BInt@zero (_ bv0 ${this.vopts.ISize})))`,
            `(declare-const BInt@one BInt) (assert (= BInt@one (_ bv1 ${this.vopts.ISize})))`,
            `(declare-const BInt@min BInt) (assert (= BInt@min (_ bv${this.computeBVMinSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`,
            `(declare-const BInt@max BInt) (assert (= BInt@max (_ bv${this.computeBVMaxSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`,

            `(declare-const BNat@zero BNat) (assert (= BNat@zero (_ bv0 ${this.vopts.ISize})))`,
            `(declare-const BNat@one BNat) (assert (= BNat@one (_ bv1 ${this.vopts.ISize})))`,
            `(declare-const BNat@min BNat) (assert (= BNat@min BNat@zero))`,
            `(declare-const BNat@max BNat) (assert (= BNat@max (_ bv${this.computeBVMaxUnSigned(BigInt(this.vopts.ISize))} ${this.vopts.ISize})))`
        ];
        if(this.vopts.BigXMode === "Int") {
            integral_constants.push(`(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))`);
            integral_constants.push(`(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))`);

            integral_constants.push(`(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))`);
            integral_constants.push(`(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))`);
        }
        else {
            integral_constants.push(`(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero (_ bv0 ${2 * this.vopts.ISize})))`);
            integral_constants.push(`(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one (_ bv1 ${2 * this.vopts.ISize})))`);

            integral_constants.push(`(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero (_ bv0 ${2 * this.vopts.ISize})))`);
            integral_constants.push(`(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one (_ bv1 ${2 * this.vopts.ISize})))`);
        }

        let float_type_alias: string[] = [];
        let float_constants: string[] = [];
        if(this.vopts.FPOpt === "Real") {
            float_type_alias.push("(define-sort BFloat () Float)", "(define-sort BDecimal () Float)", "(define-sort BRational () Float)");

            float_constants.push(`(declare-const BFloat@zero BFloat) (assert (= BFloat@zero 0.0))`);
            float_constants.push(`(declare-const BFloat@one BFloat) (assert (= BFloat@one 1.0))`);
            float_constants.push(`(declare-const BFloat@pi BFloat) (assert (= BFloat@pi 3.141592653589793))`);
            float_constants.push(`(declare-const BFloat@e BFloat) (assert (= BFloat@e 2.718281828459045))`);

            float_constants.push(`(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero 0.0))`);
            float_constants.push(`(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one 1.0))`);
            float_constants.push(`(declare-const BDecimal@pi BDecimal) (assert (= BDecimal@pi 3.141592653589793))`);
            float_constants.push(`(declare-const BDecimal@e BDecimal) (assert (= BDecimal@e 2.718281828459045))`);

            float_constants.push(`(declare-const BRational@zero BRational) (assert (= BRational@zero 0.0))`);
            float_constants.push(`(declare-const BRational@one BRational) (assert (= BRational@one 1.0))`);
        }
        else {
            float_type_alias.push("(define-sort BFloat () UFloat)", "(define-sort BDecimal () UFloat)", "(define-sort BRational () UFloat)");

            float_constants.push(`(declare-const BFloat@zero BFloat) (assert (= BFloat@zero (BFloatCons_UF "0.0")))`);
            float_constants.push(`(declare-const BFloat@one BFloat) (assert (= BFloat@one (BFloatCons_UF "1.0")))`);
            float_constants.push(`(declare-const BFloat@pi BFloat) (assert (= BFloat@pi (BFloatCons_UF "3.141592653589793")))`);
            float_constants.push(`(declare-const BFloat@e BFloat) (assert (= BFloat@e (BFloatCons_UF "2.718281828459045")))`);

            float_constants.push(`(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero (BDecimalCons_UF "0.0")))`);
            float_constants.push(`(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one (BDecimalCons_UF "1.0")))`);
            float_constants.push(`(declare-const BDecimal@pi BDecimal) (assert (= BDecimal@pi (BDecimalCons_UF "3.141592653589793")))`);
            float_constants.push(`(declare-const BDecimal@e BDecimal) (assert (= BDecimal@e (BDecimalCons_UF "2.718281828459045")))`);

            float_constants.push(`(declare-const BRational@zero BRational) (assert (= BRational@zero (BRationalCons_UF "0/1")))`);
            float_constants.push(`(declare-const BRational@one BRational) (assert (= BRational@one (BRationalCons_UF "1/1")))`);
        }

        const keytupleinfo = this.tupleDecls
            .filter((tt) => tt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const termtupleinfo = this.tupleDecls
            .filter((tt) => !tt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const keyrecordinfo = this.recordDecls
            .filter((rt) => rt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const termrecordinfo = this.recordDecls
            .filter((rt) => !rt.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const keytypeinfo = this.entityDecls
            .filter((et) => et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const termtypeinfo = this.entityDecls
            .filter((et) => !et.iskeytype)
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((kt) => {
                return {
                    decl: `(${kt.smtname} 0)`,
                    consf: `(${kt.consf.cname} ${kt.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`,
                    boxf: `(${kt.boxf} (arg ${kt.smtname}))`
                };
            });

        const etypeinfo = this.ephemeralDecls
            .sort((t1, t2) => t1.smtname.localeCompare(t2.smtname))
            .map((et) => {
                return {
                    decl: `(${et.smtname} 0)`,
                    consf: `(${et.consf.cname} ${et.consf.cargs.map((ke) => `(${ke.fname} ${ke.ftype.name})`)})`
                };
            });

        const rtypeinfo = this.resultTypes
            .sort((t1, t2) => (t1.hasFlag !== t2.hasFlag) ? (t1.hasFlag ? 1 : -1) : t1.rtname.localeCompare(t2.rtname))
            .map((rt) => {
                if (rt.hasFlag) {
                    return {
                        decl: `(${rt.rtname} 0)`,
                        consf: `(${rt.rtname}@cons ($GuardResult_${rt.rtname}@result ${rt.ctype.name}) ($GuardResult_${rt.rtname}@flag Bool))`
                    };
                }
                else {
                    return {
                        decl: `(${rt.rtname} 0)`,
                        consf: `( (${rt.rtname}@success ($Result_${rt.rtname}@success_value ${rt.ctype.name})) (${rt.rtname}@error ($Result_${rt.rtname}@error_value ErrorID)) )`
                    };
                }
            });

        const maskinfo = [...this.maskSizes]
            .sort()
            .map((msize) => {
                let entries: string[] = [];
                for(let i = 0; i < msize; ++i) {
                    entries.push(`($Mask_${msize}@${i} Bool)`);
                }

                return {
                    decl: `($Mask_${msize} 0)`,
                    consf: `($Mask_${msize}@cons ${entries.join(" ")})`
                };
            });

        const gdecls = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => `(declare-const ${c.gkey} ${c.ctype.name})`);

        const ufdecls = this.uninterpfunctions
            .sort((uf1, uf2) => uf1.fname.localeCompare(uf2.fname))
            .map((uf) => `(declare-fun ${uf.fname} (${uf.args.map((arg) => arg.name)}) ${uf.result})`);

        const gdefs = this.constantDecls
            .sort((c1, c2) => c1.gkey.localeCompare(c2.gkey))
            .map((c) => `(assert (= ${c.gkey} ${c.consf}))`);

        return {
            TYPE_TAG_DECLS: this.typeTags.sort(),
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes.sort(),
            INDEX_TAG_DECLS: this.indexTags.sort(),
            PROPERTY_TAG_DECLS: this.propertyTags.sort(),
            SUBTYPE_DECLS: subtypeasserts,
            TUPLE_HAS_INDEX_DECLS: indexasserts,
            RECORD_HAS_PROPERTY_DECLS: propertyasserts,
            KEY_TYPE_TAG_RANK: keytypeorder,
            BINTEGRAL_TYPE_ALIAS: integral_type_alias,
            BINTEGRAL_CONSTANTS: integral_constants,
            BFLOATPOINT_TYPE_ALIAS: float_type_alias,
            BFLOATPOINT_CONSTANTS: float_constants,
            STRING_TYPE_ALIAS: (this.vopts.StringOpt === "UNICODE" ? "(define-sort BString () (Seq (_ BitVec 32)))" : "(define-sort BString () String)"),
            KEY_TUPLE_INFO: { decls: keytupleinfo.map((kti) => kti.decl), constructors: keytupleinfo.map((kti) => kti.consf), boxing: keytupleinfo.map((kti) => kti.boxf) },
            KEY_RECORD_INFO: { decls: keyrecordinfo.map((kti) => kti.decl), constructors: keyrecordinfo.map((kti) => kti.consf), boxing: keyrecordinfo.map((kti) => kti.boxf) },
            KEY_TYPE_INFO: { decls: keytypeinfo.map((kti) => kti.decl), constructors: keytypeinfo.map((kti) => kti.consf), boxing: keytypeinfo.map((kti) => kti.boxf) },
            TUPLE_INFO: { decls: termtupleinfo.map((kti) => kti.decl), constructors: termtupleinfo.map((kti) => kti.consf), boxing: termtupleinfo.map((kti) => kti.boxf) },
            RECORD_INFO: { decls: termrecordinfo.map((kti) => kti.decl), constructors: termrecordinfo.map((kti) => kti.consf), boxing: termrecordinfo.map((kti) => kti.boxf) },
            TYPE_INFO: { decls: termtypeinfo.map((kti) => kti.decl), constructors: termtypeinfo.map((kti) => kti.consf), boxing: termtypeinfo.map((kti) => kti.boxf) },
            EPHEMERAL_DECLS: { decls: etypeinfo.map((kti) => kti.decl), constructors: etypeinfo.map((kti) => kti.consf) },
            RESULT_INFO: { decls: rtypeinfo.map((kti) => kti.decl), constructors: rtypeinfo.map((kti) => kti.consf) },
            MASK_INFO: { decls: maskinfo.map((mi) => mi.decl), constructors: maskinfo.map((mi) => mi.consf) },
            GLOBAL_DECLS: gdecls,
            UF_DECLS: ufdecls,
            FUNCTION_DECLS: this.functions.map((f) => f.emitSMT2()),
            GLOBAL_DEFINITIONS: gdefs
        };
    }
}

export {
    SMTEntityDecl, SMTTupleDecl, SMTRecordDecl, SMTEphemeralListDecl,
    SMTConstantDecl,
    SMTFunction, SMTFunctionUninterpreted,
    SMTAssembly,
    SMT2FileInfo
};
