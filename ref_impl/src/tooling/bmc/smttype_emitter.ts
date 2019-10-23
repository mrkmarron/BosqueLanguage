//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl } from "../../compiler/mir_assembly";
import { isInlinableType, isUniqueEntityType, getUniqueEntityType, sanitizeForSMT } from "./smtutils";

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

    typeToSMTType(tt: MIRType): string {
        if (isInlinableType(tt)) {
            if (tt.trkey === "NSCore::Bool") {
                return "Bool";
            }
            else {
                return "Int";
            }
        }
        else if (isUniqueEntityType(tt)) {
            return sanitizeForSMT(getUniqueEntityType(tt).ekey);
        }
        else {
            return "BTerm";
        }
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
