//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRTypeOption } from "../../compiler/mir_assembly";

import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTLet } from "./smt_exp";

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    private tempconvctr = 0;
    private mangledNameMap: Map<string, string> = new Map<string, string>();

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

    isNoneable(tt: MIRType): boolean {
        return tt.options.some((opt) => opt.trkey === "NSCore::None");
    }

    isTupleType(tt: MIRType): boolean {
        return tt.options.every((opt) => opt instanceof MIRTupleType);
    }

    isRecordType(tt: MIRType): boolean {
        return tt.options.every((opt) => opt instanceof MIRRecordType);
    }

    isUEntityType(tt: MIRType): boolean {
        const ropts = tt.options.filter((opt) => opt.trkey === "NSCore::None");

        if (ropts.length !== 1 || !(ropts[0] instanceof MIREntityType)) {
            return false;
        }

        const et = ropts[0] as MIREntityType;
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

    static getTupleTypeMaxLength(tt: MIRType): number {
        return Math.max(...tt.options.filter((opt) => opt instanceof MIRTupleType).map((opt) => (opt as MIRTupleType).entries.length));
    }

    static getRecordTypeMaxPropertySet(tt: MIRType): string[] {
        let popts = new Set<string>();
        tt.options.filter((opt) => opt instanceof MIRRecordType).forEach((opt) => (opt as MIRRecordType).entries.forEach((entry) => popts.add(entry.name)));
        return [...popts].sort();
    }

    static getUEntityType(tt: MIRType): MIREntityType {
        return tt.options.find((opt) => opt instanceof MIREntityType) as MIREntityType;
    }

    generateRecordTypePropertyName(tt: MIRType): string {
        const pnames = SMTTypeEmitter.getRecordTypeMaxPropertySet(tt);
        if (pnames.length === 0) {
            return "empty";
        }
        else {
            return this.mangleStringForSMT(`{${pnames.join(", ")}}`);
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
        else if (this.isTupleType(ttype)) {
            return "bsqtuple_" + SMTTypeEmitter.getTupleTypeMaxLength(ttype);
        }
        else if (this.isRecordType(ttype)) {
            return "bsqrecord_" + this.generateRecordTypePropertyName(ttype);
        }
        else if (this.isUEntityType(ttype)) {
            return this.mangleStringForSMT(SMTTypeEmitter.getUEntityType(ttype).ekey);
        }
        else {
            return "BTerm";
        }
    }

    box(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.isPrimitiveType(from)) {
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
        else if (this.isTupleType(from)) {
            return new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`);
        }
        else if (this.isRecordType(from)) {
            return new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`);
        }
        else if (this.isUEntityType(from)) {
            return new SMTValue(`(${this.registerTypeBoxing(from.options[0], into)} ${exp.emit()})`);
        }
        else {
            return exp;
        }
    }

    unbox(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.isPrimitiveType(into)) {
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
        else if (this.isTupleType(into)) {
            return new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`);
        }
        else if (this.isRecordType(into)) {
            return new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`);
        }
        else if (this.isUEntityType(into)) {
            return new SMTValue(`(${this.registerTypeUnBoxing(from, into.options[0])} ${exp.emit()})`);
        }
        else {
            return exp;
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.typeToSMTCategory(from) === this.typeToSMTCategory(into)) {
            return exp;
        }

        if (this.isPrimitiveType(from)) {
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
        else if (this.isTupleType(from)) {
            const fromsize = SMTTypeEmitter.getTupleTypeMaxLength(from);
            if (this.isTupleType(into)) {
                const intosize = SMTTypeEmitter.getTupleTypeMaxLength(into);
                const intocons = this.generateTupleConstructor(into);
                if (intosize === 0) {
                    return new SMTValue(intocons);
                }
                else {
                    let args: string[] = [];
                    for (let i = 0; i < fromsize; ++i) {
                        args.push(this.generateTupleAccessor(from, i));
                    }
                    for (let i = fromsize; i < intosize; ++i) {
                        args.push("bsqtuple_entry@empty");
                    }
                    return new SMTValue(`(${intocons} ${args.join(" ")})`);
                }
            }
            else {
                if (fromsize === 0) {
                    return new SMTValue(`(bsqterm_tuple bsqtuple_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqtuple_array_empty";
                    for (let i = 0; i < fromsize; ++i) {
                        tuparray = `(store ${tuparray} ${i} (${this.generateTupleAccessor(from, i)} ${temp}))`;
                    }
                    return new SMTLet(temp, exp, new SMTValue(`bsqterm_tuple ${tuparray}`));
                }
            }
        }
        else if (this.isRecordType(from)) {

        }
        else if (this.isUEntityType(from)) {
            
        }
        else {

        }

        if (this.isPrimitiveType(from) !== this.isPrimitiveType(into)) {
            return this.isPrimitiveType(from) ? this.box(exp, from, into) : this.unbox(exp, from, into);
        }
        else if (this.isTupleType(from) !== this.isTupleType(into)) {
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

    generateTupleConstructor(ttype: MIRType): string {
        return `bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(ttype)}@cons`;
    }

    generateTupleAccessor(ttype: MIRType, idx: number): string {
        return `bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(ttype)}@${idx}`;
    }

    generateRecordConstructor(ttype: MIRType): string {
        return `bsqrecord_${this.generateRecordTypePropertyName(ttype)}@cons`;
    }

    generateRecordAccessor(ttype: MIRType, p: string): string {
        return `bsqrecord_${this.generateRecordTypePropertyName(ttype)}@${p}`;
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
