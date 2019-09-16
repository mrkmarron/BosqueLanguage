//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRResolvedTypeKey } from "../compiler/mir_ops";
import { MIRAssembly, MIRType } from "../compiler/mir_assembly";

class AOTTypeGenerator {
    private assembly: MIRAssembly;
    private typesigMap: Map<MIRResolvedTypeKey, string> = new Map<MIRResolvedTypeKey, string>();
    private typedeclMap: Map<MIRResolvedTypeKey, string> = new Map<MIRResolvedTypeKey, string>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;
    }

    registerMIRType(type: MIRType) {
        if (type.trkey === "NSCore::None") {
            this.typesigMap.set(type.trkey, "shared_ptr<BSQ::Value>");
        }
        else if (type.trkey === "NSCore::Bool") {
            this.typesigMap.set(type.trkey, "bool");
        }
        else if (type.trkey === "NSCore::Int") {
            this.typesigMap.set(type.trkey, "int64_t");
        }
        else if (type.trkey === "NSCore::String") {
            this.typesigMap.set(type.trkey, "std::shared_ptr<std::string>");
        }
        else if (type.trkey === "NSCore::Float") {
            this.typesigMap.set(type.trkey, "double");
        }
        else if (type.trkey === "NSCore::Regex") {
            this.typesigMap.set(type.trkey, "std::shared_ptr<std::regex>");
        }
        else {
            
        }
    }
}
