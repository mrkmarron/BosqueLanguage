//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType } from "../../compiler/mir_assembly";
import { isInlinableType } from "./cpputils";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;
    }

    typeToCPPTypeForCallArguments(tt: MIRType): string {
        if (isInlinableType(tt)) {
            if (tt.trkey === "NSCore::Bool") {
                return "bool";
            }
            else {
                return "int64_t";
            }
        }
        else {
            return "const Value&";
        }
    }

    typeToCPPType(tt: MIRType): string {
        if (isInlinableType(tt)) {
            if (tt.trkey === "NSCore::Bool") {
                return "bool";
            }
            else {
                return "int64_t";
            }
        }
        else {
            return "Value";
        }
    }
}

export {
    CPPTypeEmitter
};
