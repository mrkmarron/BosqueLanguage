//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType } from "../../compiler/mir_assembly";

import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTLet, SMTCond } from "./smt_exp";

import * as assert from "assert";

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
        const ropts = tt.options.filter((opt) => opt.trkey !== "NSCore::None");

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

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.typeToSMTCategory(from) === this.typeToSMTCategory(into)) {
            return exp;
        }

        if (from.trkey === "NSCore::None") {
            if (this.isUEntityType(into)) {
                return new SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey));
            }
            else {
                return new SMTValue("bsqterm_none_const");
            }
        }
        else if (this.isPrimitiveType(from)) {
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
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args: string[] = [];
                    for (let i = 0; i < Math.min(intosize, fromsize); ++i) {
                        args.push(`(${this.generateTupleAccessor(from, i)} ${temp})`);
                    }
                    for (let i = Math.min(intosize, fromsize); i < intosize; ++i) {
                        args.push("bsqtuple_entry@empty");
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(${intocons} ${args.join(" ")})`));
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
                    return new SMTLet(temp, exp, new SMTValue(`(bsqterm_tuple ${tuparray})`));
                }
            }
        }
        else if (this.isRecordType(from)) {
            const fromset = SMTTypeEmitter.getRecordTypeMaxPropertySet(from);
            if (this.isTupleType(into)) {
                const intoset = SMTTypeEmitter.getRecordTypeMaxPropertySet(into);
                const intocons = this.generateRecordConstructor(into);
                if (intoset.length === 0) {
                    return new SMTValue(intocons);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args: string[] = [];
                    for (let i = 0; i < intoset.length; ++i) {
                        const p = intoset[i];
                        if (fromset.includes(p)) {
                            args.push(`(${this.generateRecordAccessor(from, p)} ${temp})`);
                        }
                        else {
                            args.push("bsqrecord_entry@empty");
                        }
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(${intocons} ${args.join(" ")})`));
                }
            }
            else {
                if (fromset.length === 0) {
                    return new SMTValue(`(bsqterm_record bsqrecord_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqrecord_array_empty";
                    for (let i = 0; i < fromset.length; ++i) {
                        tuparray = `(store ${tuparray} ${i} (${this.generateRecordAccessor(from, fromset[i])} ${temp}))`;
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(bsqterm_record ${tuparray})`));
                }
            }
        }
        else if (this.isUEntityType(from)) {
            const fromtype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(from).ekey) as MIREntityTypeDecl;

            let temp = `@tmpconv_${this.tempconvctr++}`;
            let entarray = "bsqentity_array_empty";
            for (let i = 0; i < fromtype.fields.length; ++i) {
                const fd = fromtype.fields[i];
                entarray = `(store ${entarray} ${fd.name} (${this.generateEntityAccessor(fromtype.tkey, fd.name)} ${temp}))`;
            }

            const nonnone = new SMTLet(temp, exp, new SMTValue(`(bsqterm_entity "${fromtype.tkey}" ${entarray})`));
            if (!this.assembly.subtypeOf(this.noneType, into)) {
                return nonnone;
            }
            else {
                const isnonetest = new SMTValue(`(is-${this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(from).ekey)} ${exp})`);
                return new SMTCond(isnonetest, new SMTValue("bsqterm_none_const"), nonnone);
            }
        }
        else {
            assert(this.typeToSMTCategory(from) === "BTerm", "must be a BTerm mapped type");

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
                const intosize = SMTTypeEmitter.getTupleTypeMaxLength(into);
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let args: string[] = [];
                for (let i = 0; i < intosize; ++i) {
                    args.push(`(select ${temp} ${i})`);
                }
                return new SMTLet(temp, new SMTValue(`(bsqterm_tuple_entries ${exp.emit()})`), new SMTValue(`(${this.generateTupleConstructor(into)} ${args.join(" ")})`));
            }
            else if (this.isRecordType(into)) {
                const intoset = SMTTypeEmitter.getRecordTypeMaxPropertySet(into);
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let args: string[] = [];
                for (let i = 0; i < intoset.length; ++i) {
                    args.push(`(select ${temp} ${intoset[i]})`);
                }
                return new SMTLet(temp, new SMTValue(`(bsqterm_record_entries ${exp.emit()})`), new SMTValue(`(${this.generateRecordConstructor(into)} ${args.join(" ")})`));
            }
            else if (this.isUEntityType(into)) {
                const fromtype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(from).ekey) as MIREntityTypeDecl;

                let temp = `@tmpconv_${this.tempconvctr++}`;
                let args: string[] = [];
                for (let i = 0; i < fromtype.fields.length; ++i) {
                   args.push(`(select ${temp} ${fromtype.fields[i].name})`);
                }
                const nonnone = new SMTLet(temp, new SMTValue(`(bsqterm_object_entries ${exp.emit()})`), new SMTValue(`(${this.generateEntityConstructor(fromtype.tkey)} ${args.join(" ")})`));

                if (!this.assembly.subtypeOf(this.noneType, from)) {
                    return nonnone;
                }
                else {
                    const isnonetest = new SMTValue(`(= ${exp} bsqterm_none_const)`);
                    return new SMTCond(isnonetest, new SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey)), nonnone);
                }
            }
            else {
                return exp;
            }
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

        const ename = this.mangleStringForSMT(entity.tkey);
        const fargs = entity.fields.map((fd) => {
            return `(${ename}@${fd.name} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });

        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityNoneConstructor(entity.tkey)}) (cons@${ename} (${ename}@$type String) ${fargs.join(" ")}) )`
        };
    }

    generateEntityNoneConstructor(ekey: MIRNominalTypeKey): string {
        return `cons@${this.mangleStringForSMT(ekey)}$none`;
    }

    generateEntityConstructor(ekey: MIRNominalTypeKey): string {
        return `cons@${this.mangleStringForSMT(ekey)}`;
    }

    generateEntityAccessor(ekey: MIRNominalTypeKey, f: string): string {
        return `${this.mangleStringForSMT(ekey)}@${f}`;
    }
}

export {
    SMTTypeEmitter
};
