//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../../ast/parser";
import { MIRAssembly } from "../../compiler/mir_assembly";

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

class SMTAssembly {
    readonly masm: MIRAssembly;

    readonly errorDefinitions: Map<string, SMTErrorCode> = new Map<string, SMTErrorCode>();
    readonly uninterpTypeConstructors: Set<string> = new Set<string>();

    constructor(masm: MIRAssembly) {
        this.masm = masm;
    }
}

export {
    SMTErrorCode,
    SMTAssembly
};
