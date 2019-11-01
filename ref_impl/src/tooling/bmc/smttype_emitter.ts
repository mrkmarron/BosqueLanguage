//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType } from "../../compiler/mir_assembly";
import { sanitizeStringForSMT } from "./smtutils";

import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

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

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isPrimitiveType(tt: MIRType): boolean {
        if (tt.options.length !== 1) {
            return false;
        }

        const uname = tt.options[0].trkey;
        return (uname === "NSCore::Bool" || uname === "NSCore::Int" || uname === "NSCore::String");
    }

    isFixedTupleType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRTupleType)) {
            return false;
        }

        const tup = tt.options[0] as MIRTupleType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    isFixedRecordType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRRecordType)) {
            return false;
        }

        const tup = tt.options[0] as MIRRecordType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    isUEntityType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIREntityType)) {
            return false;
        }

        const et = tt.options[0] as MIREntityType;
        const tdecl = this.assembly.entityDecls.get(et.ekey) as MIREntityTypeDecl;

        return this.doDefaultEmitOnEntity(tdecl);
    }

    doDefaultEmitOnEntity(et: MIREntityTypeDecl): boolean {
        if (et.tkey === "NSCore::None" || et.tkey === "NSCore::Bool" || et.tkey === "NSCore::Int" || et.tkey === "NSCore::String" || et.tkey === "NSCore::Regex") {
            return false;
        }

        if (et.tkey.startsWith("NSCore::StringOf<") || et.tkey.startsWith("NSCore::ValidatedString<") || et.tkey.startsWith("NSCore::PODBuffer<")) {
            return false;
        }

        if (et.provides.includes("NSCore::Enum") || et.provides.includes("NSCore::IdKey")) {
            return false;
        }

        return true;
    }

    static getPrimitiveType(tt: MIRType): MIREntityType {
        return tt.options[0] as MIREntityType;
    }

    static getFixedTupleType(tt: MIRType): MIRTupleType {
        return tt.options[0] as MIRTupleType;
    }

    static getFixedRecordType(tt: MIRType): MIRRecordType {
        return tt.options[0] as MIRRecordType;
    }

    static getUEntityType(tt: MIRType): MIREntityType {
        return tt.options[0] as MIREntityType;
    }

    static fixedRecordPropertyName(frec: MIRRecordType): string {
        return sanitizeStringForSMT(`{${frec.entries.map((entry) => entry.name).join("$")}}`);
    }

    typeToSMTCategory(ttype: MIRType): string {
        if (this.isPrimitiveType(ttype)) {
            if (ttype.trkey === "NSCore::Bool") {
                return "Bool";
            }
            else if (ttype.trkey === "NSCore::Int") {
                return "Int";
            }
            else {
                return "String";
            }
        }
        else if (this.isFixedTupleType(ttype)) {
            return "bsqtuple_" + (ttype.options[0] as MIRTupleType).entries.length;
        }
        else if (this.isFixedRecordType(ttype)) {
            return "bsqrecord_" + SMTTypeEmitter.fixedRecordPropertyName(ttype.options[0] as MIRRecordType);
        }
        else if (this.isUEntityType(ttype)) {
            return "bsqentity_" + sanitizeStringForSMT(ttype.trkey);
        }
        else {
            return "BTerm";
        }
    }

    generateFixedTupleConstructor(ttype: MIRType): string {
        return `bsqtuple_${(ttype.options[0] as MIRTupleType).entries.length}@cons`;
    }

    generateFixedTupleAccessor(ttype: MIRType, idx: number): string {
        return `bsqtuple_${(ttype.options[0] as MIRTupleType).entries.length}@${idx}`;
    }

    generateFixedRecordConstructor(ttype: MIRType): string {
        return `bsqrecord_${SMTTypeEmitter.fixedRecordPropertyName(ttype.options[0] as MIRRecordType)}@cons`;
    }

    generateFixedRecordAccessor(ttype: MIRType, p: string): string {
        return `bsqrecord_${SMTTypeEmitter.fixedRecordPropertyName(ttype.options[0] as MIRRecordType)}@${SMTTypeEmitter.getFixedRecordType(ttype).entries.findIndex((entry) => entry.name === p)}`;
    }

    generateSMTEntity(entity: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (!this.doDefaultEmitOnEntity(entity)) {
            return undefined;
        }

        const fargs = entity.fields.map((fd) => {
            return `(${sanitizeStringForSMT(entity.tkey)}@${fd.fname} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });

        return {
            fwddecl: `(${sanitizeStringForSMT(entity.tkey)} 0)`,
            fulldecl: `( (cons$${sanitizeStringForSMT(entity.tkey)} ${fargs.join(" ")}) )`
        };
    }
}

export {
    SMTTypeEmitter
};
