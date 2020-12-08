//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../../ast/parser";
import { SMTExp, SMTType } from "./smt_exp";

class SMTErrorCode {
    readonly code: string;
    readonly srcFile: string;
    readonly sinfo: SourceInfo;

    constructor(code: string, srcFile: string, sinfo: SourceInfo) {
        this.code = code;
        this.srcFile = srcFile;
        this.sinfo = sinfo; 
    }
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

class SMTAssembly {
    readonly uninterpTypeConstructors: Map<string, SMTType> = new Map<string, SMTType>();

    readonly uninterpfunctions: SMTFunctionUninterpreted[] = [];
    readonly functions: SMTFunction[] = [];

    constructor() {
    }
}

export {
    SMTErrorCode,
    SMTAssembly, SMTFunction, SMTFunctionUninterpreted
};
