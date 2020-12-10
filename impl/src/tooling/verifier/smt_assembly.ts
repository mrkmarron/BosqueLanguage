//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { BSQRegex } from "../../ast/bsqregex";
import { SMTAxiom, SMTErrorAxiom, SMTExp, SMTType, VerifierLevel } from "./smt_exp";

type SMT2FileInfo = {
    TYPE_TAG_DECLS: string[],
    ABSTRACT_TYPE_TAG_DECLS: string[],
    INDEX_TAG_DECLS: string[],
    PROPERTY_TAG_DECLS: string[],
    SUBTYPE_DECLS: string[],
    TUPLE_HAS_INDEX_DECLS: string[],
    RECORD_HAS_PROPERTY_DECLS: string[],
    KEY_TYPE_TAG_RANK: string[],
    FP_TYPE_ALIAS: string[],
    STRING_TYPE_ALIAS: string,
    KEY_TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    KEY_TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TUPLE_INFO: { decls: string[], constructors: string[], boxing: string[] },
    RECORD_INFO: { decls: string[], constructors: string[], boxing: string[] },
    TYPE_INFO: { decls: string[], constructors: string[], boxing: string[] }
    EPHEMERAL_DECLS: { decls: string[], constructors: string[] },
    RESULT_INFO: { decls: string[], constructors: string[] },
    GLOBAL_DECLS
    UF_DECLS
    AXIOM_DECLS
    FUNCTION_DECLS
    GLOBAL_DEFINITIONS
    FREE_CONSTRUCTOR_FUNCTIONS
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
}

class SMTFunctionUninterpreted {
    readonly fname: string;
    readonly args: SMTType[];
    readonly result: SMTType;

    //
    //TODO: we want to put in info on pcode functions and axioms here
    //

    constructor(fname: string, args: SMTType[], result: SMTType) {
        this.fname = fname;
        this.args = args;
        this.result = result;
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
}

class SMTTupleDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;
}

class SMTRecordDecl {
    readonly iskeytype: boolean;
    readonly isapitype: boolean;
    
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;
}

class SMTEphemeralListDecl {
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
}

class SMTConstantDecl {
    readonly gkey: string;
    readonly ctype: string;

    readonly consf: string;    
}

class SMTAssembly {
    readonly level: VerifierLevel;
    
    entityDecls: SMTEntityDecl[] = [];
    tupleDecls: SMTTupleDecl[] = [];
    recordDecls: SMTRecordDecl[] = [];
    ephemeralDecls: SMTEphemeralListDecl[] = [];

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
    
    generatedKeyLessFunctions: SMTFunction[] = [];

    uninterpfunctions: SMTFunctionUninterpreted[] = [];
    axioms: SMTAxiom[] = [];
    errorproprs: SMTErrorAxiom[] = [];

    resultTypes: { hasFlag: boolean, rtname: string, ctype: SMTType }[];
    functions: SMTFunction[] = [];

    freeConstructorFunctions: SMTFunction[] = [];

    constructor(level: VerifierLevel) {
        this.level = level;
    }

    generateSMT2AssemblyInfo(): SMT2FileInfo {
        const TYPE_TAG_DECLS = [
            ...this.entityDecls.map((ed) => ed.typetag),
            ...this.tupleDecls.map((ed) => ed.typetag),
            ...this.recordDecls.map((ed) => ed.typetag)
        ].sort();

        const subtypeasserts = this.subtypeRelation.map((tc) => tc.value ? `(assert (SubtypeOf@ ${tc.ttype} ${tc.atype}))` : `(assert (not (SubtypeOf@ ${tc.ttype} ${tc.atype})))`).sort();
        const indexasserts = this.hasIndexRelation.map((hi) => hi.value ? `(assert (HasIndex@ ${hi.idxtag} ${hi.atype}))` : `(assert (not (HasIndex@ ${hi.idxtag} ${hi.atype})))`).sort();
        const propertyasserts = this.hasPropertyRelation.map((hp) => hp.value ? `(assert (HasProperty@ ${hp.pnametag} ${hp.atype}))` : `(assert (not (HasProperty@ ${hp.pnametag} ${hp.atype})))`).sort();

        const keytypeorder: string[] = [...this.keytypeTags].sort().map((ktt, i) => `(assert (= (TypeTagRank@ ${ktt}) ${i}))`);

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
                        consf: `(${rt.rtname}@cons ($GuardResult_${rt.rtname}@result ${rt.ctype.name}) ($GuardResult_${rt.rtname}@flag Bool))`,
                    };
                }
                else {
                    return {
                        decl: `(${rt.rtname} 0)`,
                        consf: `( (${rt.rtname}@success ($Result_${rt.rtname}@success_value ${rt.ctype.name})) (${rt.rtname}@error ($Result_${rt.rtname}@error_value ErrorID)) )`
                    };
                }
            });

        return {
            TYPE_TAG_DECLS,
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes,
            INDEX_TAG_DECLS: this.indexTags,
            PROPERTY_TAG_DECLS: this.propertyTags,
            SUBTYPE_DECLS: subtypeasserts,
            TUPLE_HAS_INDEX_DECLS: indexasserts,
            RECORD_HAS_PROPERTY_DECLS: propertyasserts,
            KEY_TYPE_TAG_RANK: keytypeorder,
            FP_TYPE_ALIAS: (this.level === "Strong" ? ["(define-sort BFloat () UFloat)", "(define-sort BDecimal () UFloat)", "(define-sort BRational () UFloat)"] : ["(define-sort BFloat () Float)", "(define-sort BDecimal () Float)", "(define-sort BRational () Float)"]),
            STRING_TYPE_ALIAS: (this.level === "Strong" ? "(define-sort BString () (Seq (_ BitVec 64)))" : "(define-sort BString () String)"),
            KEY_TUPLE_INFO: { decls: keytupleinfo.map((kti) => kti.decl), constructors: keytupleinfo.map((kti) => kti.consf), boxing: keytupleinfo.map((kti) => kti.boxf) },
            KEY_RECORD_INFO: { decls: keyrecordinfo.map((kti) => kti.decl), constructors: keyrecordinfo.map((kti) => kti.consf), boxing: keyrecordinfo.map((kti) => kti.boxf) },
            KEY_TYPE_INFO: { decls: keytypeinfo.map((kti) => kti.decl), constructors: keytypeinfo.map((kti) => kti.consf), boxing: keytypeinfo.map((kti) => kti.boxf) },
            TUPLE_INFO: { decls: termtupleinfo.map((kti) => kti.decl), constructors: termtupleinfo.map((kti) => kti.consf), boxing: termtupleinfo.map((kti) => kti.boxf) },
            RECORD_INFO: { decls: termrecordinfo.map((kti) => kti.decl), constructors: termrecordinfo.map((kti) => kti.consf), boxing: termrecordinfo.map((kti) => kti.boxf) },
            TYPE_INFO: { decls: termtypeinfo.map((kti) => kti.decl), constructors: termtypeinfo.map((kti) => kti.consf), boxing: termtypeinfo.map((kti) => kti.boxf) },
            EPHEMERAL_DECLS: { decls: etypeinfo.map((kti) => kti.decl), constructors: etypeinfo.map((kti) => kti.consf) },
            RESULT_INFO: { decls: rtypeinfo.map((kti) => kti.decl), constructors: rtypeinfo.map((kti) => kti.consf) }
            GLOBAL_DECLS
    UF_DECLS
    AXIOM_DECLS
    FUNCTION_DECLS
    GLOBAL_DEFINITIONS
    FREE_CONSTRUCTOR_FUNCTIONS
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
