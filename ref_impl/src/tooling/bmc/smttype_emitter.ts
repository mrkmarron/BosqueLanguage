//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType } from "../../compiler/mir_assembly";
import { sanitizeStringForSMT } from "./smtutils";

class SMTTypeEmitter {
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

    static isPrimitiveType(tt: MIRType): boolean {
        if (tt.options.length !== 1) {
            return false;
        }

        const uname = tt.options[0].trkey;
        return (uname === "NSCore::Bool" || uname === "NSCore::Int" || uname === "NSCore::String");
    }

    static isFixedTupleType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRTupleType)) {
            return false;
        }

        const tup = tt.options[0] as MIRTupleType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    static isFixedRecordType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRRecordType)) {
            return false;
        }

        const tup = tt.options[0] as MIRRecordType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    static isUEntityType(tt: MIRType): boolean {
        return !SMTTypeEmitter.isPrimitiveType(tt) && (tt.options.length === 1 && tt.options[0] instanceof MIREntityType);
    }

    generateSMTEntity(entity: MIREntityTypeDecl): { fwddecl: string, boxeddecl: string, fulldecl: string } | undefined {
        if (entity.tkey === "NSCore::None" || entity.tkey === "NSCore::Bool" || entity.tkey === "NSCore::Int" || entity.tkey === "NSCore::String") {
            return undefined;
        }

        const fargs = entity.fields.map((fd) => {
            return `(${sanitizeForSMT(entity.tkey)}@${fd.fname} ${this.typeToSMTType(this.assembly.typeMap.get(fd.declaredType) as MIRType)})`;
        });

        return {
            fwddecl: `(${sanitizeForSMT(entity.tkey)} 0)`,
            boxeddecl: `(bsq_term_${sanitizeForSMT(entity.tkey)} (bsq_term_value_${sanitizeForSMT(entity.tkey)} ${sanitizeForSMT(entity.tkey)}))`,
            fulldecl: `( (cons$${sanitizeForSMT(entity.tkey)} ${fargs.join(" ")}) )`
        };
    }
}

export {
    SMTTypeEmitter
};
