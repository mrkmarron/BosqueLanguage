//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType, MIREpemeralListType } from "../../compiler/mir_assembly";

import { MIRResolvedTypeKey, MIRNominalTypeKey, MIRFieldKey } from "../../compiler/mir_ops";
import { SMTExp, SMTValue, SMTLet, SMTCond } from "./smt_exp";

import * as assert from "assert";

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    readonly keyType: MIRType;

    readonly enumtype: MIRType;
    readonly idkeytype: MIRType;
    readonly guididkeytype: MIRType;
    readonly eventtimeidkeytype: MIRType;
    readonly datahashidkeytype: MIRType;
    readonly cryptohashidkeytype: MIRType;    

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    conceptSubtypeRelation: Map<MIRNominalTypeKey, MIRNominalTypeKey[]> = new Map<MIRNominalTypeKey, MIRNominalTypeKey[]>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;

        this.keyType = assembly.typeMap.get("NSCore::KeyType") as MIRType;
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

    typecheckIsName(tt: MIRType, oftype: RegExp, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && oftype.test(tt.options[0].trkey);
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && oftype.test(opt.trkey));
        }
    }

    typecheckEntityAndProvidesName(tt: MIRType, oftype: MIRType, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && this.assembly.subtypeOf(tt, oftype);
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && this.assembly.subtypeOf(MIRType.createSingle(opt), oftype));
        }
    }

    typecheckTuple(tt: MIRType, match?: "known" | "tuple"): boolean {
        match = match || "tuple";
        if(match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType) && !(tt.options[0] as MIRTupleType).entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof MIRTupleType);
        }
    }

    typecheckRecord(tt: MIRType, match?: "known" | "record"): boolean {
        match = match || "record";
        if(match === "known") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType) && !(tt.options[0] as MIRRecordType).entries.some((entry) => entry.isOptional);
        }
        else {
            return tt.options.every((opt) => opt instanceof MIRRecordType);
        }
    }

    typecheckUEntity(tt: MIRType, match?: "exact" | "may"): boolean {
        match = match || "exact";
        if(match === "exact") {
            return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType) && tt.options[0].trkey !== "NSCore::None";
        }
        else {
            return tt.options.some((opt) => (opt instanceof MIREntityType) && opt.trkey !== "NSCore::None");
        }
    }

    typecheckEphemeral(tt: MIRType): boolean {
        return tt.options.length === 1 && tt.options[0] instanceof MIREpemeralListType;
    }
    
    typecheckIsNoneable(tt: MIRType): boolean {
        return tt.options.some((opt) => (opt instanceof MIREntityType) && opt.trkey === "NSCore::None");
    }

    getSMTTypeFor(tt: MIRType): string {
        if (this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "Bool";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "Int";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/)) {
            return "String";
        }
        else if (this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "BKeyValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/)) {
            return "BKeyValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::EventTime$/)) {
            return "BKeyValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "BKeyValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.guididkeytype)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.eventtimeidkeytype)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.datahashidkeytype)) {
            return "BKeyValue";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.cryptohashidkeytype)) {
            return "BKeyValue";
        }
        else {
            if(tt.options.every((opt) => this.assembly.subtypeOf(MIRType.createSingle(opt), this.keyType))) {
                return "BKeyValue";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/)) {
                return "BTerm";
            }
            else if (this.typecheckIsName(tt, /^NSCore::ISOTime$/)) {
                return "BTerm";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "BTerm";
            }
            else if (this.typecheckTuple(tt)) {
                return "BTerm";
            }
            else if (this.typecheckRecord(tt)) {
                return "BTerm";
            }
            else if (this.typecheckIsName(tt, /^NSCore::MapEntry<.*>$/)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else if (this.typecheckIsName(tt, /^NSCore::Result<.*>$/)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else if (this.typecheckIsName(tt, /^NSCore::Tagged<.*>$/)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else if(this.typecheckUEntity(tt)) {
                return this.mangleStringForSMT(tt.trkey)
            }
            else if(this.typecheckEphemeral(tt)) {
                return this.mangleStringForSMT(tt.trkey);
            }
            else {
                return "BTerm";
            }
        }
    }

    private coerceFromAtomicKey(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        const intotype = this.getSMTTypeFor(into);

        if (from.trkey === "NSCore::None") {
            return (intotype === "BKeyValue") ? new SMTValue("bsqkey_none") : new SMTValue(`bsqterm_none`);
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/)) {
            return (intotype === "BKeyValue") ? new SMTValue(`(bsqkey_bool ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_bool ${exp.emit()}))`);
        }
        else if (this.typecheckIsName(from, /^NSCore::Int$/)) {
            return (intotype === "BKeyValue") ? new SMTValue(`(bsqkey_int ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_int ${exp.emit()}))`);
        }
        else if (this.typecheckIsName(from, /^NSCore::String$/)) {
            return (intotype === "BKeyValue") ? new SMTValue(`(bsqkey_string ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_string ${exp.emit()}))`);
        }
        else {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
    }

    private coerceFromOptionsKey(exp: SMTExp, into: MIRType): SMTExp {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return new SMTValue(`(bsqkey_bool_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
            return new SMTValue(`(bsqkey_int_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::String$/)) {
            return new SMTValue(`(bsqkey_string_value ${exp.emit()})`);
        }
        else {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
    }

    private coerceIntoAtomicKey(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        const fromtype = this.getSMTTypeFor(from);
        if (into.trkey === "NSCore::None") {
            return (fromtype === "BKeyValue") ? new SMTValue("bsqkey_none") : new SMTValue(`bsqterm_none`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_bool ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_bool ${exp.emit()}))`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
            return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_int ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_int ${exp.emit()}))`);
        }
        else if (this.typecheckIsName(into, /^NSCore::String$/)) {
            return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_string ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_string ${exp.emit()}))`);
        }
        else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.cryptohashidkeytype)) {
            return new SMTValue(`(bsqterm_key ${exp.emit()})`);
        }
    }

    private coerceIntoOptionsKey(exp: SMTExp, from: MIRType): SMTExp {
       
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        if (this.getSMTTypeFor(from) === this.getSMTTypeFor(into)) {
            return exp;
        }

        if (from.trkey === "NSCore::None") {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/) || this.typecheckIsName(from, /^NSCore::Int$/) || this.typecheckIsName(from, /^NSCore::String$/)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckIsName(from, /^NSCore::StringOf<.*>$/) || this.typecheckIsName(from, /^NSCore::GUID$/) || this.typecheckIsName(from, /^NSCore::EventTime$/)
            || this.typecheckIsName(from, /^NSCore::DataHash$/) || this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype) || this.typecheckEntityAndProvidesName(from, this.idkeytype) || this.typecheckEntityAndProvidesName(from, this.guididkeytype)
            || this.typecheckEntityAndProvidesName(from, this.eventtimeidkeytype) || this.typecheckEntityAndProvidesName(from, this.datahashidkeytype) || this.typecheckEntityAndProvidesName(from, this.cryptohashidkeytype)) {
            return this.coerceFromAtomicKey(exp, from, into);
        }
        else {
            if(from.options.every((opt) => this.assembly.subtypeOf(MIRType.createSingle(opt), this.keyType))) {
                return this.coerceFromOptionsKey(exp, into);
            }
            else if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(from, /^NSCore::ISOTime$/) || this.typecheckIsName(from, /^NSCore::Regex$/)
                || this.typecheckTuple(from) || this.typecheckRecord(from)) {
                return exp;
            }
            else if (this.typecheckIsName(from, /^NSCore::MapEntry<.*>$/)) {
                    //do object construct here!!!!
                return new SMTExp()
            }
            else if (this.typecheckIsName(from, /^NSCore::Result<.*>$/)) {
                    //do object construct here!!!!
                return new SMTExp()
            }
            else if (this.typecheckIsName(from, /^NSCore::Tagged<.*>$/)) {
                    //do object construct here!!!!
                return new SMTExp()
            }
            else if (this.typecheckUEntity(from)) {
                    //do object construct here!!!!
                return new SMTExp()
            }
            else {
                const fromtype = this.getSMTTypeFor(from);
                if (into.trkey === "NSCore::None") {
                    return (fromtype === "BKeyValue") ? new SMTValue("bsqkey_none") : new SMTValue(`bsqterm_none`);
                }
                else if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
                    return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_bool ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_bool ${exp.emit()}))`);
                }
                else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
                    return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_int ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_int ${exp.emit()}))`);
                }
                else if (this.typecheckIsName(into, /^NSCore::String$/)) {
                    return (fromtype === "BKeyValue") ? new SMTValue(`(bsqkey_string ${exp.emit()})`) : new SMTValue(`(bsqterm_key (bsqkey_string ${exp.emit()}))`);
                }
                else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else if (this.typecheckEntityAndProvidesName(into, this.cryptohashidkeytype)) {
                    return new SMTValue(`(bsqterm_key ${exp.emit()})`);
                }
                else {
                    if(into.options.every((opt) => this.assembly.subtypeOf(MIRType.createSingle(opt), this.keyType))) {
                        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
                            return new SMTValue(`(bsqkey_bool_value ${exp.emit()})`);
                        }
                        else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
                            return new SMTValue(`(bsqkey_int_value ${exp.emit()})`);
                        }
                        else if (this.typecheckIsName(into, /^NSCore::String$/)) {
                            return new SMTValue(`(bsqkey_string_value ${exp.emit()})`);
                        }
                        else {
                            new SMTValue(`(bsqterm_key ${exp.emit()})`);
                        }
                    }
                    else if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/)) {
                        return exp;
                    }
                    else if (this.typecheckIsName(into, /^NSCore::ISOTime$/)) {
                        return exp;
                    }
                    else if (this.typecheckIsName(into, /^NSCore::Regex$/)) {
                        return exp;
                    }
                    else if (this.typecheckTuple(into)) {
                        return exp;
                    }
                    else if (this.typecheckRecord(into)) {
                        return exp;
                    }
                    else if (this.typecheckIsName(into, /^NSCore::MapEntry<.*>$/)) {
                        return exp;
                    }
                    else if (this.typecheckIsName(into, /^NSCore::Result<.*>$/)) {
                        return exp;
                    }
                    else if (this.typecheckIsName(into, /^NSCore::Tagged<.*>$/)) {
                        return exp;
                    }
                    else if(this.typecheckUEntity(into)) {
                        return exp;
                    }
                    else {
                        return exp;
                    }
                }
            }
        }
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
        this.assembly.conceptDecls.forEach((tt) => {
            const cctype = this.getMIRType(tt.tkey);
            const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, cctype));
            const keyarray = est.map((et) => et.trkey).sort();

            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
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
        if (this.isSpecialRepType(entity) || this.isSpecialCollectionRepType(entity) || this.isSpecialKeyListRepType(entity)) {
            return undefined;
        }

        const ename = this.mangleStringForSMT(entity.tkey);
        const fargs = entity.fields.map((fd) => {
           return `(${ename}@${this.mangleStringForSMT(fd.fkey)} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });

        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityNoneConstructor(entity.tkey)}) (cons@${ename} ${fargs.join(" ")}) )`
        };
    }

    generateEntityNoneConstructor(ekey: MIRNominalTypeKey): string {
        if (ekey.startsWith("NSCore::List<")) {
            return "cons@bsqlist$none";
        }
        else if (ekey.startsWith("NSCore::Set<")) {
            return "cons@bsqkvcontainer$none";
        }
        else if (ekey.startsWith("NSCore::Map<")) {
            return "cons@bsqkvcontainer$none";
        }
        else if (ekey === "NSCore::KeyList") {
            return "cons@bsqkeylist$none";
        }
        else {
            return `cons@${this.mangleStringForSMT(ekey)}$none`;
        }
    }

    generateEntityConstructor(ekey: MIRNominalTypeKey): string {
        if (ekey.startsWith("NSCore::List<")) {
            return "cons@bsqlist";
        }
        else if (ekey.startsWith("NSCore::Set<")) {
            return "cons@bsqkvcontainer";
        }
        else if (ekey.startsWith("NSCore::Map<")) {
            return "cons@bsqkvcontainer";
        }
        else if (ekey === "NSCore::KeyList") {
            return "cons@bsqkeylist";
        }
        else {
            return `cons@${this.mangleStringForSMT(ekey)}`;
        }
    }

    generateEntityAccessor(ekey: MIRNominalTypeKey, f: MIRFieldKey): string {
        return `${this.mangleStringForSMT(ekey)}@${this.mangleStringForSMT(f)}`;
    }

    generateCheckSubtype(ekey: MIRNominalTypeKey, oftype: MIRConceptType): string {
        const lookups = oftype.ckeys.map((ckey) => {
            return `(select MIRConceptSubtypeArray__${this.mangleStringForSMT(ckey)} ${ekey})`;
        });

        if(lookups.length === 1) {
            return lookups[0];
        }
        else {
            return lookups.join(" ");
        }
    }
}

export {
    SMTTypeEmitter
};
