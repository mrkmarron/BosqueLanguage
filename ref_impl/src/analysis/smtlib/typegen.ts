//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRAssembly, MIRType, MIRTypeOption, MIREntityType, MIREntityTypeDecl, MIRTupleType, MIRRecordType } from "../../compiler/mir_assembly";
import { smtsanizite, BuiltinTypes, BuiltinTypeEmit } from "./builtins";

class SMTTypeGenerator {
    readonly assembly: MIRAssembly;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;
    readonly anyType: MIRType;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.noneType = this.assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = this.assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = this.assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = this.assembly.typeMap.get("NSCore::String") as MIRType;
        this.anyType = this.assembly.typeMap.get("NSCore::Any") as MIRType;
    }

    isTypeExact(type: MIRType | MIRTypeOption): boolean {
        if (type instanceof MIRType) {
            return type.options.length === 1 && this.isTypeExact(type.options[0]);
        }

        if (type instanceof MIREntityType) {
            const tdecl = this.assembly.entityDecls.get(type.ekey) as MIREntityTypeDecl;
            if (!tdecl.isCollectionEntityType && !tdecl.isMapEntityType) {
                return true;
            }
            else {
                return [...tdecl.terms].every((etype) => this.isTypeExact(etype[1]));
            }
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

    typeToSMT2Type(type: MIRType | MIRTypeOption): string {
        if (!this.isTypeExact(type)) {
            return "BTerm";
        }
        else {
            const topt = (type instanceof MIRType) ? type.options[0] : type;
            if (topt instanceof MIREntityType) {
                const tdecl = this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                if (tdecl.ns === "NSCore" && (tdecl.name === "Bool" || tdecl.name === "Int" || tdecl.name === "String")) {
                    return tdecl.name;
                }
                else {
                    return "T" + smtsanizite(topt.trkey);
                }
            }
            else if (topt instanceof MIRTupleType) {
                const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
                return `Tbsq_tuple$_${entryinfos.join("$")}_$`;
            }
            else {
                assert(topt instanceof MIRRecordType);

                const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
                return `Tbsq_record$_${entryinfos.join("")}_$`;
            }
        }
    }

    typeToSMT2Constructor(type: MIRType | MIRTypeOption): string {
        assert(this.isTypeExact(type));

        const topt = (type instanceof MIRType) ? type.options[0] : type;
        if (topt instanceof MIREntityType) {
            return smtsanizite(topt.trkey);
        }
        else if (topt instanceof MIRTupleType) {
            const entryinfos = topt.entries.map((e) => this.typeToSMT2Type(e.type));
            return `bsq_tuple$_${entryinfos.join("$")}_$`;
        }
        else {
            assert(topt instanceof MIRRecordType);

            const entryinfos = (topt as MIRRecordType).entries.map((e) => `${this.propertyToSMT2Name(e.name)}@${this.typeToSMT2Type(e.type)}`);
            return `bsq_tuple$_${entryinfos.join("")}_$`;
        }
    }

    propertyToSMT2Name(pname: string): string {
        return pname;
    }

    generateTypeDecl(type: MIRType, typedecls: string[], consdecls: [string, string?][]) {
        if (this.isTypeExact(type)) {
            const topt = type.options[0];
            if (topt instanceof MIREntityType) {
                const edecl = this.assembly.entityDecls.get(topt.ekey) as MIREntityTypeDecl;
                if (edecl.ns === "NSCore" && (edecl.name === "None" || edecl.name === "Bool" || edecl.name === "Int" || edecl.name === "String")) {
                    //don't need to do anything as these are special cases
                }
                else if (edecl.isCollectionEntityType || edecl.isMapEntityType) {
                    typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);
                    consdecls.push((BuiltinTypes.get(edecl.name) as BuiltinTypeEmit)(this.typeToSMT2Constructor(topt), this.typeToSMT2Type(edecl.terms.get("T") as MIRType)));
                }
                else {
                    typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                    const tpfx = this.typeToSMT2Constructor(topt);
                    const entries: string[] = [];
                    for (let i = 0; i < edecl.fields.length; ++i) {
                        const ftype = this.assembly.typeMap.get(edecl.fields[i].declaredType) as MIRType;
                        entries.push(`(${tpfx}@${edecl.fields[i].name} ${this.typeToSMT2Type(ftype)})`);
                    }

                    consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
                }
            }
            else if (topt instanceof MIRTupleType ) {
                typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                const tpfx = this.typeToSMT2Constructor(topt);
                const entries: string[] = [];
                for (let i = 0; i < topt.entries.length; ++i) {
                    entries.push(`(${tpfx}@${i} ${this.typeToSMT2Type(topt.entries[i].type)})`);
                }

                consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
            }
            else if (topt instanceof MIRRecordType) {
                typedecls.push(`(${this.typeToSMT2Type(topt)} 0)`);

                const tpfx = this.typeToSMT2Constructor(topt);
                const entries: string[] = [];
                for (let i = 0; i < topt.entries.length; ++i) {
                    entries.push(`(${tpfx}@${topt.entries[i].name} ${this.typeToSMT2Type(topt.entries[i].type)})`);
                }

                consdecls.push([`((${tpfx} ${entries.join(" ")}))`]);
            }
            else {
                //don't need to do anything
            }
        }
    }
}

export {
    SMTTypeGenerator
};
