//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType, MIREpemeralListType, MIRRecordTypeEntry } from "../../compiler/mir_assembly";

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
    readonly validatorType: MIRType;

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

    typecheckAllKeys(tt: MIRType): boolean {
        return tt.options.every((opt) => this.assembly.subtypeOf(MIRType.createSingle(opt), this.keyType));
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
            return "bsq_stringof";
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/)) {
            return "bsq_guid";
        }
        else if (this.typecheckIsName(tt, /^NSCore::EventTime$/)) {
            return "bsq_eventtime";
        }
        else if (this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "bsq_datahash";
        }
        else if (this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "bsq_cryptohash";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "bsq_enum";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "bsq_idkey";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.guididkeytype)) {
            return "bsq_idkey_guid";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.eventtimeidkeytype)) {
            return "bsq_idkey_eventtime";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.datahashidkeytype)) {
            return "bsq_idkey_datahash";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.cryptohashidkeytype)) {
            return "bsq_idkey_cryptohash";
        }
        else {
            if(this.typecheckAllKeys(tt)) {
                return "BKeyValue";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/)) {
                return "bsq_buffer";
            }
            else if (this.typecheckIsName(tt, /^NSCore::ISOTime$/)) {
                return "bsq_isotime";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "bsq_regex";
            }
            else if (this.typecheckTuple(tt)) {
                return "bsq_tuple";
            }
            else if (this.typecheckRecord(tt)) {
                return "bsq_record";
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
        else {
            let ctoval = "[NOT SET]";

            if (this.typecheckIsName(from, /^NSCore::Bool$/)) {
                ctoval = `(bsqkey_bool ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::Int$/)) {
                ctoval = `(bsqkey_int ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::String$/)) {
                ctoval = `(bsqkey_string ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::StringOf<.*>$/)) {
                ctoval = `(bsq_stringof ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::GUID$/)) {
                ctoval = `(bsq_guid ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::EventTime$/)) {
                ctoval = `(bsq_eventtime ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::DataHash$/)) {
                ctoval = `(bsq_datahash ${exp.emit()})`;
            }
            else if (this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
                ctoval = `(bsq_cryptohash ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.enumtype)) {
                ctoval = `(bsq_enum ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.idkeytype)) {
                ctoval = `(bsq_idkey ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.guididkeytype)) {
                ctoval = `(bsq_idkey_guid ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.eventtimeidkeytype)) {
                ctoval = `(bsq_idkey_eventtime ${exp.emit()})`;
            }
            else if (this.typecheckEntityAndProvidesName(from, this.datahashidkeytype)) {
                ctoval = `(bsq_idkey_datahash ${exp.emit()})`;
            }
            else {
                ctoval = `(bsq_idkey_cryptohash ${exp.emit()})`;
            }

            return (intotype === "BKeyValue") ? new SMTValue(ctoval) : new SMTValue(`(bsqterm_key ${ctoval})`);
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
        else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
            return new SMTValue(`(bsqkey_stringof_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
            return new SMTValue(`(bsqkey_guid_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
            return new SMTValue(`(bsqkey_eventtime_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return new SMTValue( `(bsqkey_datahash_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
            return new SMTValue(`(bsqkey_cryptohash_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return new SMTValue(`(bsqkey_enum_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
            return new SMTValue(`(bsqkey_idkey_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
            return new SMTValue(`(bsqkey_idkey_guid_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
            return new SMTValue(`(bsqkey_idkey_eventtime_value ${exp.emit()})`);
        }
        else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
            return new SMTValue(`(bsqkey_idkey_datahash_value ${exp.emit()})`);
        }
        else {
            return new SMTValue(`(bsqkey_idkey_cryptohash_value ${exp.emit()})`);
        }
    }

    private coerceFromAtomicTerm(exp: SMTExp, from: MIRType): SMTExp {
        if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/)) {
            return new SMTValue(`(bsqterm_buffer ${exp.emit()})`);
        }
        else if (this.typecheckIsName(from, /^NSCore::ISOTime$/)) {
            return new SMTValue(`(bsqterm_isotime ${exp.emit()})`);
        }
        else if (this.typecheckIsName(from, /^NSCore::Regex$/)) {
            return new SMTValue(`(bsqterm_regex ${exp.emit()})`);
        }
        else if (this.typecheckTuple(from)) {
            return new SMTValue(`(bsqterm_tuple ${exp.emit()})`);
        }
        else if (this.typecheckRecord(from)) {
            return new SMTValue(`(bsqterm_record ${exp.emit()})`);
        }
        else if (this.typecheckIsName(from, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(from, /^NSCore::Result<.*>$/) || this.typecheckIsName(from, /^NSCore::Tagged<.*>$/)) {
            return new SMTValue(`(bsqterm_object "${this.mangleStringForSMT(from.trkey)}" (bsqterm_object_${this.mangleStringForSMT(from.trkey)}@cons ${exp.emit()}))`);
        }
        else {
            return new SMTValue(`(bsqterm_object "${this.mangleStringForSMT(from.trkey)}" (bsqterm_object_${this.mangleStringForSMT(from.trkey)}@cons ${exp.emit()}))`);
        }
    }

    private coerceIntoAtomicKey(exp: SMTExp, into: MIRType): SMTExp {
        if (into.trkey === "NSCore::None") {
            return new SMTValue("bsqkey_none");
        }
        else {
            const cfrom = `(bsqterm_key_value ${exp.emit()})`;

            if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
                return new SMTValue(`(bsqkey_bool_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::Int$/)) {
                return new SMTValue(`(bsqkey_int_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::String$/)) {
                return new SMTValue(`(bsqkey_string_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/)) {
                return new SMTValue(`(bsq_stringof_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::GUID$/)) {
                return new SMTValue(`(bsq_guid_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
                return new SMTValue(`(bsq_eventtime_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
                return new SMTValue(`(bsq_datahash_value ${cfrom})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
                return new SMTValue(`(bsq_cryptohash_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
                return new SMTValue(`(bsq_enum_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.idkeytype)) {
                return new SMTValue(`(bsq_idkey_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.guididkeytype)) {
                return new SMTValue(`(bsq_idkey_guid_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
                return new SMTValue(`(bsq_idkey_eventtime_value ${cfrom})`);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
                return new SMTValue(`(bsq_idkey_datahash_value ${cfrom})`);
            }
            else {
                return new SMTValue(`(bsq_idkey_cryptohash_value ${cfrom})`);
            }
        }
    }

    private coerceIntoAtomicTerm(exp: SMTExp, into: MIRType): SMTExp {
        if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/)) {
            return new SMTValue(`(bsqterm_buffer_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::ISOTime$/)) {
            return new SMTValue(`(bsqterm_isotime_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::Regex$/)) {
            return new SMTValue(`(bsqterm_regex_value ${exp.emit()})`);
        }
        else if (this.typecheckTuple(into)) {
            return new SMTValue(`(bsqterm_tuple_value ${exp.emit()})`);
        }
        else if (this.typecheckRecord(into)) {
            return new SMTValue(`(bsqterm_record_value ${exp.emit()})`);
        }
        else if (this.typecheckIsName(into, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(into, /^NSCore::Result<.*>$/) || this.typecheckIsName(into, /^NSCore::Tagged<.*>$/)) {
            return new SMTValue(`(bsqterm_object_${this.mangleStringForSMT(into.trkey)}_value (bsqterm_object_value ${exp.emit()}))`);
        }
        else {
            return new SMTValue(`(bsqterm_object_${this.mangleStringForSMT(into.trkey)}_value (bsqterm_object_value ${exp.emit()}))`);
        }
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
        else if (this.typecheckAllKeys(from)) {
            const intotype = this.getSMTTypeFor(into);
            if(intotype === "BTerm") {
                return new SMTValue(`(bsqterm_key ${exp})`);
            }
            else {
                return this.coerceFromOptionsKey(exp, into);
            }
        }
        else if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(from, /^NSCore::ISOTime$/) || this.typecheckIsName(from, /^NSCore::Regex$/)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else if (this.typecheckTuple(from) || this.typecheckRecord(from)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else if (this.typecheckIsName(from, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(from, /^NSCore::Result<.*>$/) || this.typecheckIsName(from, /^NSCore::Tagged<.*>$/)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else if (this.typecheckUEntity(from)) {
            return this.coerceFromAtomicTerm(exp, from);
        }
        else {
            //now from must be Bterm so we are projecting down
            assert(this.getSMTTypeFor(into) === "BTerm");

            if (into.trkey === "NSCore::None") {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckIsName(into, /^NSCore::Bool$/) || this.typecheckIsName(into, /^NSCore::Int$/) || this.typecheckIsName(into, /^NSCore::String$/)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckIsName(into, /^NSCore::StringOf<.*>$/) || this.typecheckIsName(into, /^NSCore::GUID$/) || this.typecheckIsName(into, /^NSCore::EventTime$/)
                || this.typecheckIsName(into, /^NSCore::DataHash$/) || this.typecheckIsName(into, /^NSCore::CryptoHash$/)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckEntityAndProvidesName(into, this.enumtype) || this.typecheckEntityAndProvidesName(into, this.idkeytype) || this.typecheckEntityAndProvidesName(into, this.guididkeytype)
                || this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype) || this.typecheckEntityAndProvidesName(into, this.datahashidkeytype) || this.typecheckEntityAndProvidesName(into, this.cryptohashidkeytype)) {
                return this.coerceIntoAtomicKey(exp, into);
            }
            else if (this.typecheckAllKeys(into)) {
                return new SMTValue(`(bsqterm_key_value ${exp})`);
            }
            else if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(into, /^NSCore::ISOTime$/) || this.typecheckIsName(into, /^NSCore::Regex$/)) {
                return this.coerceIntoAtomicTerm(exp, into);
            }
            else if (this.typecheckTuple(into) || this.typecheckRecord(into)) {
                return this.coerceIntoAtomicTerm(exp, into);
            }
            else if (this.typecheckIsName(into, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(into, /^NSCore::Result<.*>$/) || this.typecheckIsName(into, /^NSCore::Tagged<.*>$/)) {
                return this.coerceIntoAtomicTerm(exp, into);
            }
            else {
                assert(this.typecheckUEntity(into));

                return this.coerceIntoAtomicTerm(exp, into);
            }
        }
    }

    getKeyProjectedTypeFrom(ktype: MIRType): MIRType {
        if(this.typecheckAllKeys(ktype)) {
            return ktype;
        }
        else {
            assert(false);
            return ktype;
        }
    }

    getKeyFrom(arg: string, atype: MIRType): string {
        if(this.typecheckAllKeys(atype)) {
            return arg;
        }
        else {
            assert(false);
            return "[NOT IMPLEMENTED]";
        }
    }

    tupleHasIndex(tt: MIRType, idx: number): "yes" | "no" | "maybe" {
        if(tt.options.every((opt) => opt instanceof MIRTupleType && opt.entries.length < idx && !opt.entries[idx].isOptional)) {
            return "yes";
        }
        else if(tt.options.every((opt) => opt instanceof MIRTupleType && opt.entries.length >= idx)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    getMaxTupleLength(tt: MIRType): number {
        const lens = tt.options.map((opt) => (opt as MIRTupleType).entries.length);
        return Math.max(...lens);
    }

    recordHasField(tt: MIRType, pname: string): "yes" | "no" | "maybe" {
        if(tt.options.every((opt) => opt instanceof MIRRecordType && opt.entries.find((entry) => entry.name === pname) !== undefined && !(opt.entries.find((entry) => entry.name === pname) as MIRRecordTypeEntry).isOptional)) {
            return "yes";
        }
        else if(tt.options.every((opt) => opt instanceof MIRRecordType && opt.entries.find((entry) => entry.name === pname) === undefined)) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    getMaxPropertySet(tt: MIRType): string[] {
        let props = new Set<string>();
        tt.options.forEach((opt) => (opt as MIRRecordType).entries.forEach((entry) => props.add(entry.name)));

        return [...props].sort();
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

    generateEntityConstructor(ekey: MIRNominalTypeKey): string {
        return `${this.mangleStringForSMT(ekey)}@cons`;
    }

    generateEntityAccessor(ekey: MIRNominalTypeKey, f: MIRFieldKey): string {
        return `${this.mangleStringForSMT(ekey)}@${this.mangleStringForSMT(f)}`;
    }

    generateEmptyHasArrayFor(ekey: MIRNominalTypeKey): string {
        return this.mangleStringForSMT(`${ekey}_collection_has_array_empty`);
    }

    generateEmptyKeyArrayFor(ekey: MIRNominalTypeKey): string {
        return this.mangleStringForSMT(`${ekey}_collection_key_array_empty`);
    }

    generateEmptyDataArrayFor(ekey: MIRNominalTypeKey): string {
        return this.mangleStringForSMT(`${ekey}_collection_data_array_empty`);
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

    generateCheckSubtype(ekey: MIRNominalTypeKey, oftype: MIRConceptType): string {
        const lookups = oftype.ckeys.map((ckey) => {
            return `(select MIRConceptSubtypeArray__${this.mangleStringForSMT(ckey)} ${ekey})`;
        });

        if(lookups.length === 1) {
            return lookups[0];
        }
        else {
            return `(or ${lookups.join(" ")})`;
        }
    }
}

export {
    SMTTypeEmitter
};
