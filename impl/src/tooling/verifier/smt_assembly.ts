//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { BSQRegex } from "../../ast/bsqregex";
import { SMTAxiom, SMTErrorAxiom, SMTExp, SMTType } from "./smt_exp";

type SMT2FileInfo = {
    TYPE_TAG_DECLS: string[],
    ABSTRACT_TYPE_TAG_DECLS: string[],
    INDEX_TAG_DECLS: string[],
    PROPERTY_TAG_DECLS: string[],
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
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;

    readonly invfunc: string | undefined;
}

class SMTTupleDecl {
    readonly smtname: string;
    readonly typetag: string;

    readonly consf: { cname: string, cargs: { fname: string, ftype: SMTType }[] };
    readonly boxf: string;
    readonly ubf: string;
}

class SMTRecordDecl {
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
    entityDecls: SMTEntityDecl[] = [];
    tupleDecls: SMTTupleDecl[] = [];
    recordDecls: SMTRecordDecl[] = [];
    ephemeralDecls: SMTEphemeralListDecl[] = [];

    abstractTypes: string[] = [];
    indexTags: string[] = [];
    propertyTags: string[] = [];

    subtypeRelation: { ttype: string, atype: string }[] = [];
    hasIndexRelation: { ttype: string, atype: string }[] = [];
    hasPropertyRelation: { ttype: string, atype: string }[] = [];

    literalRegexs: BSQRegex[] = [];
    validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    constantDecls: SMTConstantDecl[] = [];
    
    generatedKeyLessFunctions: SMTFunction[] = [];

    uninterpfunctions: SMTFunctionUninterpreted[] = [];
    axioms: SMTAxiom[] = [];
    errorproprs: SMTErrorAxiom[] = [];

    functions: SMTFunction[] = [];

    freeConstructorFunctions: SMTFunction[] = [];

    constructor() {
    }

    generateSMT2AssemblyInfo(): SMT2FileInfo {
        const TYPE_TAG_DECLS = [
            ...this.entityDecls.map((ed) => ed.typetag),
            ...this.tupleDecls.map((ed) => ed.typetag),
            ...this.recordDecls.map((ed) => ed.typetag)
        ];

        return {
            TYPE_TAG_DECLS,
            ABSTRACT_TYPE_TAG_DECLS: this.abstractTypes,
            INDEX_TAG_DECLS: this.indexTags,
            PROPERTY_TAG_DECLS: this.propertyTags
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
