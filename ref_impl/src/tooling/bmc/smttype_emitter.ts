//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRTypeOption } from "../../compiler/mir_assembly";

import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";
import { SMTExp, SMTValue } from "./smt_exp";

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    typeboxings: { fkey: string, from: MIRTypeOption, into: MIRType }[] = [];
    typeunboxings: { fkey: string, from: MIRType, into: MIRTypeOption }[] = [];

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;
    }

    mangleStringForSMT(name: string): string {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }

        return this.mangledNameMap.get(name) as string;
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

    generateFixedRecordPropertyName(frec: MIRRecordType): string {
        if (frec.entries.length === 0) {
            return "empty";
        }
        else {
            return this.mangleStringForSMT(`{${frec.entries.map((entry) => entry.name).join(", ")}}`);
        }
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
            return "bsqrecord_" + this.generateFixedRecordPropertyName(ttype.options[0] as MIRRecordType);
        }
        else if (this.isUEntityType(ttype)) {
            return this.mangleStringForSMT(ttype.trkey);
        }
        else {
            return "BTerm";
        }
    }

    registerTypeBoxing(from: MIRTypeOption, into: MIRType): string {
        const tbi = this.typeboxings.findIndex((tb) => tb.from.trkey === from.trkey && tb.into.trkey === into.trkey);
        if (tbi !== -1) {
            return this.typeboxings[tbi].fkey;
        }

        const fkey = "BOX@" + this.mangleStringForSMT(`${from.trkey}_${into.trkey}`);
        this.typeboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    boxIfNeeded(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.isPrimitiveType(from)) {
            if (this.isPrimitiveType(into)) {
                return exp;
            }

            if (from.trkey === "NSCore::Bool") {
                return new SMTValue(`(bsqterm_bool ${exp.emit()})`);
            }
            else if (from.trkey === "NSCore::Int") {
                return new SMTValue(`(bsqterm_int ${exp.emit()})`);
            }
            else {
                return new SMTValue(`(bsqterm_string ${exp.emit()})`);
            }
        }
        else if (this.isFixedTupleType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else if (this.isFixedRecordType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else if (this.isUEntityType(from)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`) : exp;
        }
        else {
            return exp;
        }
    }

    registerTypeUnBoxing(from: MIRType, into: MIRTypeOption): string {
        const tbi = this.typeunboxings.findIndex((tb) => tb.from.trkey === from.trkey && tb.into.trkey === into.trkey);
        if (tbi !== -1) {
            return this.typeunboxings[tbi].fkey;
        }

        const fkey = "UNBOX@" + this.mangleStringForSMT(`${from.trkey}_${into.trkey}`);
        this.typeunboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    unboxIfNeeded(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.isPrimitiveType(into)) {
            if (this.isPrimitiveType(from)) {
                return exp;
            }

            if (into.trkey === "NSCore::Bool") {
                return new SMTValue(`(bsqterm_bool_value ${exp.emit()})`);
            }
            else if (into.trkey === "NSCore::Int") {
                return new SMTValue(`(bsqterm_int_value ${exp.emit()})`);
            }
            else {
                return new SMTValue(`(bsqterm_string_value ${exp.emit()})`);
            }
        }
        else if (this.isFixedTupleType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else if (this.isFixedRecordType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else if (this.isUEntityType(into)) {
            return (from.trkey !== into.trkey) ? new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`) : exp;
        }
        else {
            return exp;
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.isPrimitiveType(from) !== this.isPrimitiveType(into)) {
            return this.isPrimitiveType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (this.isFixedTupleType(from) !== this.isFixedTupleType(into)) {
            return this.isFixedTupleType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (this.isFixedRecordType(from) !== this.isFixedRecordType(into)) {
            return this.isFixedRecordType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else if (this.isUEntityType(from) !== this.isUEntityType(into)) {
            return this.isUEntityType(from) ? this.boxIfNeeded(exp, from, into) : this.unboxIfNeeded(exp, from, into);
        }
        else {
            return exp;
        }
    }

    generateFixedTupleConstructor(ttype: MIRType): string {
        return `bsqtuple_${(ttype.options[0] as MIRTupleType).entries.length}@cons`;
    }

    generateFixedTupleAccessor(ttype: MIRType, idx: number): string {
        return `bsqtuple_${(ttype.options[0] as MIRTupleType).entries.length}@${idx}`;
    }

    generateFixedRecordConstructor(ttype: MIRType): string {
        return `bsqrecord_${this.generateFixedRecordPropertyName(ttype.options[0] as MIRRecordType)}@cons`;
    }

    generateFixedRecordAccessor(ttype: MIRType, p: string): string {
        return `bsqrecord_${this.generateFixedRecordPropertyName(ttype.options[0] as MIRRecordType)}@${SMTTypeEmitter.getFixedRecordType(ttype).entries.findIndex((entry) => entry.name === p)}`;
    }

    generateSMTEntity(entity: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (!this.doDefaultEmitOnEntity(entity)) {
            return undefined;
        }

        const fargs = entity.fields.map((fd) => {
            return `(${this.mangleStringForSMT(entity.tkey)}@${fd.name} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });

        return {
            fwddecl: `(${this.mangleStringForSMT(entity.tkey)} 0)`,
            fulldecl: `( (cons$${this.mangleStringForSMT(entity.tkey)} ${fargs.join(" ")}) )`
        };
    }

    generateEntityConstructor(ekey: MIRNominalTypeKey): string {
        return `cons$${this.mangleStringForSMT(ekey)}`;
    }

    generateEntityAccessor(ekey: MIRNominalTypeKey, f: string): string {
        return `${this.mangleStringForSMT(ekey)}@${f}`;
    }
}

export {
    SMTTypeEmitter
};
