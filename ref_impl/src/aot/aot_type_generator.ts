//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRResolvedTypeKey } from "../compiler/mir_ops";
import { MIRAssembly, MIRType, MIRTypeOption, MIREntityType, MIRTupleType, MIRRecordType, MIREntityTypeDecl } from "../compiler/mir_assembly";
import { NOT_IMPLEMENTED, sanitizeForCpp } from "./utils";

class AOTTypeGenerator {
    private assembly: MIRAssembly;
    private typesigMap: Map<MIRResolvedTypeKey, string> = new Map<MIRResolvedTypeKey, string>();
    //private typedeclMap: Map<MIRResolvedTypeKey, string> = new Map<MIRResolvedTypeKey, string>();

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;
    readonly someType: MIRType;
    readonly anyType: MIRType;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.noneType = this.assembly.typeMap.get("NSCore::None") as MIRType;
        this.registerMIRType(this.noneType);

        this.boolType = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.registerMIRType(this.boolType);

        this.intType = this.assembly.typeMap.get("NSCore::Int") as MIRType;
        this.registerMIRType(this.intType);

        this.stringType = this.assembly.typeMap.get("NSCore::String") as MIRType;
        this.registerMIRType(this.stringType);

        this.someType = this.assembly.typeMap.get("NSCore::Some") as MIRType;
        this.registerMIRType(this.someType);

        this.anyType = this.assembly.typeMap.get("NSCore::Any") as MIRType;
        this.registerMIRType(this.anyType);
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
            NOT_IMPLEMENTED<never>("registerMIRType -- non-primitive");
        }
    }

    isTypeExact(type: MIRType | MIRTypeOption): boolean {
        if (type instanceof MIRType) {
            return type.options.length === 1 && this.isTypeExact(type.options[0]);
        }

        if (type instanceof MIREntityType) {
            const tdecl = this.assembly.entityDecls.get(type.ekey) as MIREntityTypeDecl;
            return [...tdecl.terms].every((etype) => this.isTypeExact(etype[1]));
        }
        else if (type instanceof MIRTupleType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else if (type instanceof MIRRecordType) {
            return !type.isOpen && type.entries.every((entry) => !entry.isOptional && this.isTypeExact(entry.type));
        }
        else {
            return false;
        }
    }

    static getExactTypeFrom(from: MIRType | MIRTypeOption): MIRTypeOption {
        return (from instanceof MIRType) ? from.options[0] : from;
    }

    typeToCppType(type: MIRType): string {
        return sanitizeForCpp(type.trkey);
    }
}

export {
    AOTTypeGenerator
};
