//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType } from "../../compiler/mir_assembly";

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

    conceptSubtypeRelation: Map<string, string[]> = new Map<string, string[]>();

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

    isSimpleBoolType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Bool";
    }

    isSimpleIntType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Int";
    }

    isSimpleStringType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::String";
    }

    isTupleType(tt: MIRType): boolean {
        return tt.options.every((opt) => opt instanceof MIRTupleType);
    }

    isKnownLayoutTupleType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRTupleType)) {
            return false;
        }

        const tup = tt.options[0] as MIRTupleType;
        return !tup.entries.some((entry) => entry.isOptional);
    }

    isRecordType(tt: MIRType): boolean {
        return tt.options.every((opt) => opt instanceof MIRRecordType);
    }

    isKnownLayoutRecordType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRRecordType)) {
            return false;
        }

        const tup = tt.options[0] as MIRRecordType;
        return !tup.entries.some((entry) => entry.isOptional);
    }

    isUEntityType(tt: MIRType): boolean {
        const ropts = tt.options.filter((opt) => opt.trkey !== "NSCore::None");

        if (ropts.length !== 1 || !(ropts[0] instanceof MIREntityType)) {
            return false;
        }

        const et = ropts[0] as MIREntityType;
        const tdecl = this.assembly.entityDecls.get(et.ekey) as MIREntityTypeDecl;

        return !this.isSpecialRepType(tdecl);
    }

    isCollectionType(tt: MIRType): boolean {
        return (tt.trkey.startsWith("NSCore::List<") || tt.trkey.startsWith("NSCore::Set<") || tt.trkey.startsWith("NSCore::Map<"));
    }

    isKeyListType(tt: MIRType): boolean {
        return tt.trkey === "NSCore::KeyList";
    }

    isSpecialCollectionRepType(et: MIREntityTypeDecl): boolean {
        return (et.tkey.startsWith("NSCore::List<") || et.tkey.startsWith("NSCore::Set<") || et.tkey.startsWith("NSCore::Map<"));
    }

    isListType(tt: MIRType): boolean {
        return tt.trkey.startsWith("NSCore::List<");
    }

    isSetType(tt: MIRType): boolean {
        return tt.trkey.startsWith("NSCore::Set<");
    }

    isMapType(tt: MIRType): boolean {
        return tt.trkey.startsWith("NSCore::Map<");
    }

    isSpecialRepType(et: MIREntityTypeDecl): boolean {
        if (et.tkey === "NSCore::None" || et.tkey === "NSCore::Bool" || et.tkey === "NSCore::Int" || et.tkey === "NSCore::String" || et.tkey === "NSCore::GUID" || et.tkey === "NSCore::Regex") {
            return true;
        }

        if (et.tkey.startsWith("NSCore::StringOf<") || et.tkey.startsWith("NSCore::PODBuffer<")) {
            return true;
        }

        if (et.tkey === "NSCore::KeyList") {
            return true;
        }

        if (et.provides.includes("NSCore::Enum") || et.provides.includes("NSCore::IdKey")) {
            return true;
        }

        return false;
    }

    static getTupleTypeMaxLength(tt: MIRType): number {
        return Math.max(...tt.options.filter((opt) => opt instanceof MIRTupleType).map((opt) => (opt as MIRTupleType).entries.length));
    }

    static getKnownLayoutTupleType(tt: MIRType): MIRTupleType {
        return tt.options[0] as MIRTupleType;
    }

    static getRecordTypeMaxPropertySet(tt: MIRType): string[] {
        let popts = new Set<string>();
        tt.options.filter((opt) => opt instanceof MIRRecordType).forEach((opt) => (opt as MIRRecordType).entries.forEach((entry) => popts.add(entry.name)));
        return [...popts].sort();
    }

    static getKnownLayoutRecordType(tt: MIRType): MIRRecordType {
        return tt.options[0] as MIRRecordType;
    }

    static getUEntityType(tt: MIRType): MIREntityType {
        return tt.options.filter((opt) => opt.trkey !== "NSCore::None")[0] as MIREntityType;
    }

    initializeConceptSubtypeRelation(): void {
        this.assembly.typeMap.forEach((tt) => {
           if(tt instanceof MIRConceptType) {
               const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, tt));
               const keyarray = est.map((et) => et.trkey).sort();

               this.conceptSubtypeRelation.set(tt.trkey, keyarray);
           } 
        });
    }

    getSubtypesArrayCount(tt: MIRConceptType): number {
        return (this.conceptSubtypeRelation.get(tt.trkey) as string[]).length;
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
        if (this.isSimpleBoolType(ttype)) {
            return "Bool";
        }
        else if (this.isSimpleIntType(ttype)) {
            return "Int";
        }
        else if (this.isSimpleStringType(ttype)) {
            return "String";
        }
        else if (this.isTupleType(ttype)) {
            return "bsqtuple_" + SMTTypeEmitter.getTupleTypeMaxLength(ttype);
        }
        else if (this.isRecordType(ttype)) {
            return "bsqrecord_" + this.generateRecordTypePropertyName(ttype);
        }
        else if (this.isUEntityType(ttype)) {
            if (this.isCollectionType(ttype)) {
                if (this.isListType(ttype)) {
                    return "bsqlist";
                }
                else {
                    return "bsqkvcontainer";
                }
            }
            else if (this.isKeyListType(ttype)) {
                return "bsqkeylist";
            }
            else {
                return this.mangleStringForSMT(SMTTypeEmitter.getUEntityType(ttype).ekey);
            }
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
        else if (this.isSimpleBoolType(from)) {
            return new SMTValue(`(bsqterm_bool ${exp.emit()})`);
        }
        else if (this.isSimpleIntType(from)) {
            return new SMTValue(`(bsqterm_int ${exp.emit()})`);
        }
        else if (this.isSimpleStringType(from)) {
            return new SMTValue(`(bsqterm_string ${exp.emit()})`);
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
                    return new SMTValue(`(bsqterm_tuple 0 bsqtuple_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqtuple_array_empty";
                    for (let i = 0; i < fromsize; ++i) {
                        tuparray = `(store ${tuparray} ${i} (${this.generateTupleAccessor(from, i)} ${temp}))`;
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(bsqterm_tuple ${fromsize} ${tuparray})`));
                }
            }
        }
        else if (this.isRecordType(from)) {
            const fromset = SMTTypeEmitter.getRecordTypeMaxPropertySet(from);
            if (this.isRecordType(into)) {
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
                            args.push("bsqrecord_entry@clear");
                        }
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(${intocons} ${args.join(" ")})`));
                }
            }
            else {
                if (fromset.length === 0) {
                    return new SMTValue(`(bsqterm_record 0 bsqrecord_prop_array_empty bsqrecord_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqrecord_array_empty";
                    let proparray = "bsqrecord_prop_array_empty"
                    for (let i = 0; i < fromset.length; ++i) {
                        tuparray = `(store ${tuparray} "${fromset[i]}" (${this.generateRecordAccessor(from, fromset[i])} ${temp}))`;
                        proparray = `(store ${proparray} ${i} "${fromset[i]}")`;
                    }
                    return new SMTLet(temp, exp, new SMTValue(`(bsqterm_record ${fromset.length} ${proparray} ${tuparray})`));
                }
            }
        }
        else if (this.isUEntityType(from)) {
            const fromtype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(from).ekey) as MIREntityTypeDecl;

            if(this.isCollectionType(from)) {
                let nonnone: SMTExp | undefined = undefined;
                if(this.isListType(from)) {
                    nonnone = new SMTValue(`(bsqterm_list ${exp})`);
                }
                else {
                    nonnone = new SMTValue(`(bsqterm_kvcontainer ${exp})`);
                }

                if (!this.assembly.subtypeOf(this.noneType, into)) {
                    return nonnone as SMTExp;
                }
                else {
                    const isnonetest = new SMTValue(`(is-${this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(from).ekey)} ${exp})`);
                    return new SMTCond(isnonetest, new SMTValue("bsqterm_none_const"), nonnone as SMTExp);
                }
            }
            else {
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let entarray = "bsqentity_array_empty";
                for (let i = 0; i < fromtype.fields.length; ++i) {
                    const fd = fromtype.fields[i];
                    const access = `(${this.generateEntityAccessor(fromtype.tkey, fd.name)} ${temp})`;
                    entarray = `(store ${entarray} "${fd.name}" ${this.coerce(new SMTValue(access), this.getMIRType(fd.declaredType), this.anyType).emit()})`;
                }

                const nonnone = new SMTLet(temp, exp, new SMTValue(`(bsqterm_object "${fromtype.tkey}" ${entarray})`));
                if (!this.assembly.subtypeOf(this.noneType, into)) {
                    return nonnone;
                }
                else {
                    const isnonetest = new SMTValue(`(is-${this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(from).ekey)} ${exp})`);
                    return new SMTCond(isnonetest, new SMTValue("bsqterm_none_const"), nonnone);
                }
            }
        }
        else {
            assert(this.typeToSMTCategory(from) === "BTerm", "must be a BTerm mapped type");

            if (this.isSimpleBoolType(into)) {
                return new SMTValue(`(bsqterm_bool_value ${exp.emit()})`);
            }
            else if (this.isSimpleIntType(into)) {
                return new SMTValue(`(bsqterm_int_value ${exp.emit()})`);
            }
            else if (this.isSimpleStringType(into)) {
                return new SMTValue(`(bsqterm_string_value ${exp.emit()})`);
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
                    args.push(`(select ${temp} "${intoset[i]}")`);
                }
                return new SMTLet(temp, new SMTValue(`(bsqterm_record_entries ${exp.emit()})`), new SMTValue(`(${this.generateRecordConstructor(into)} ${args.join(" ")})`));
            }
            else if (this.isUEntityType(into)) {
                const intotype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(into).ekey) as MIREntityTypeDecl;

                if(this.isCollectionType(into)) {
                    let nonnone: SMTExp | undefined = undefined;
                    if(this.isListType(into)) {
                        nonnone = new SMTValue(`(bsqterm_list_entry ${exp})`);
                    }
                    else {
                        nonnone = new SMTValue(`(bsqterm_bsqkvcontainer_entry ${exp})`);
                    }

                    if (!this.assembly.subtypeOf(this.noneType, into)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new SMTValue(`(= ${exp} bsqterm_none_const)`);
                        return new SMTCond(isnonetest, new SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey)), nonnone);
                    }
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args: string[] = [];
                    for (let i = 0; i < intotype.fields.length; ++i) {
                        args.push(this.coerce(new SMTValue(`(select ${temp} "${intotype.fields[i].name}")`), this.anyType, this.getMIRType(intotype.fields[i].declaredType)).emit());
                    }
                    const nonnone = new SMTLet(temp, new SMTValue(`(bsqterm_object_entries ${exp.emit()})`), new SMTValue(`(${this.generateEntityConstructor(intotype.tkey)} ${args.join(" ")})`));

                    if (!this.assembly.subtypeOf(this.noneType, from)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new SMTValue(`(= ${exp} bsqterm_none_const)`);
                        return new SMTCond(isnonetest, new SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey)), nonnone);
                    }
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
        if (this.isSpecialRepType(entity) || this.isSpecialCollectionRepType(entity)) {
            return undefined;
        }

        const ename = this.mangleStringForSMT(entity.tkey);
        const fargs = entity.fields.map((fd) => {
            return `(${ename}@${fd.name} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });

        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityNoneConstructor(entity.tkey)}) (cons@${ename} ${fargs.join(" ")}) )`
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
