//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType, MIREpemeralListType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey, MIRNominalTypeKey } from "../../compiler/mir_ops";

import * as assert from "assert";

class CPPTypeEmitter {
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

    scopectr: number = 0;

    conceptSubtypeRelation: Map<MIRNominalTypeKey, MIRNominalTypeKey[]> = new Map<MIRNominalTypeKey, MIRNominalTypeKey[]>();

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;
    }

    mangleStringForCpp(name: string): string {
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

    getCPPTypeFor(tt: MIRType, declspec: "base" | "parameter" | "return" | "storage"): string {
        if (this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "bool";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "IntValue";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/)) {
            return "BSQString" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "BSQStringOf" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/)) {
            return "BSQGUID" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckIsName(tt, /^NSCore::EventTime$/)) {
            return "BSQEventTime";
        }
        else if (this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "BSQDataHash";
        }
        else if (this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "BSQCryptoHash" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype)) {
            return "BSQEnum";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype)) {
            return "BSQIdKey" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.guididkeytype)) {
            return "BSQGUIDIdKey" + (declspec !== "base" ? "*" : "");
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.eventtimeidkeytype)) {
            return "BSQEventTimeIdKey";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.datahashidkeytype)) {
            return "BSQDataHashIdKey";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.cryptohashidkeytype)) {
            return "BSQCryptoHashIdKey" + (declspec !== "base" ? "*" : "");
        }
        else {
            if (this.typecheckAllKeys(tt)) {
                return "KeyValue";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/)) {
                return "BSQBuffer" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckIsName(tt, /^NSCore::ISOTime$/)) {
                return "BSQISOTime" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "BSQRegex" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckTuple(tt)) {
                return "BSQTuple" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckRecord(tt)) {
                return "BSQRecord" + (declspec !== "base" ? "*" : "");
            }
            else if (this.typecheckIsName(tt, /^NSCore::MapEntry<.*>$/)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else if (this.typecheckIsName(tt, /^NSCore::Result<.*>$/)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else if (this.typecheckIsName(tt, /^NSCore::Tagged<.*>$/)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else if(this.typecheckUEntity(tt)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else if(this.typecheckEphemeral(tt)) {
                return this.mangleStringForCpp(tt.trkey);
            }
            else {
                return "Value";
            }
        }
    }

    private coerceFromAtomicKey(exp: string, from: MIRType): string {
        const scope = this.mangleStringForCpp("$scope$");
        if (from.trkey === "NSCore::None") {
            return "BSQ_VALUE_NONE";
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/)) {
            return `BSQ_BOX_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::EventTime$/)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQEventTime, ${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::DataHash$/)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQDataHash, ${exp})`;
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQEnum, ${exp})`;
        }
        else if (this.typecheckEntityAndProvidesName(from, this.eventtimeidkeytype)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQEventTimeIdKey, ${exp})`;
        }
        else if (this.typecheckEntityAndProvidesName(from, this.datahashidkeytype)) {
            return `BSQ_NEW_ADD_SCOPE(${scope}, BSQDataHashIdKey, ${exp})`;
        }
        else {
            return exp;
        }
    }

    private coerceFromOptionsKey(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return `BSQ_GET_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEventTime)`;
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHash)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEnum)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEventTimeIdKey)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHashIdKey)`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${this.getCPPTypeFor(into, "base")}, ${exp})`;
        }
    }

    private coerceIntoAtomicKey(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Bool$/)) {
            return `BSQ_GET_VALUE_BOOL(${exp})`;
        }
        else if (this.typecheckIsName(into, /^NSCore::EventTime$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEventTime)`;
        }
        else if (this.typecheckIsName(into, /^NSCore::DataHash$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHash)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.enumtype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEnum)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.eventtimeidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQEventTimeIdKey)`;
        }
        else if (this.typecheckEntityAndProvidesName(into, this.datahashidkeytype)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, BSQDataHashIdKey)`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${this.getCPPTypeFor(into, "base")}, ${exp})`;
        }
    }

    private coerceIntoAtomicTerm(exp: string, into: MIRType): string {
        if (this.typecheckIsName(into, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(into, /^NSCore::ISOTime$/) || this.typecheckIsName(into, /^NSCore::Regex$/)) {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
        else if (this.typecheckTuple(into)) {
            return `BSQ_GET_VALUE_PTR(${exp}, BSQTuple)`;
        }
        else if (this.typecheckRecord(into)) {
            return `BSQ_GET_VALUE_PTR(${exp}, BSQRecord)`;
        }
        else if (this.typecheckIsName(into, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(into, /^NSCore::Result<.*>$/) || this.typecheckIsName(into, /^NSCore::Tagged<.*>$/)) {
            return `*BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
        else {
            return `BSQ_GET_VALUE_PTR(${exp}, ${this.getCPPTypeFor(into, "base")})`;
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
        if (this.getCPPTypeFor(from, "base") === this.getCPPTypeFor(into, "base")) {
            return exp;
        }

        if (from.trkey === "NSCore::None") {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckIsName(from, /^NSCore::Bool$/) || this.typecheckIsName(from, /^NSCore::Int$/) || this.typecheckIsName(from, /^NSCore::String$/)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckIsName(from, /^NSCore::StringOf<.*>$/) || this.typecheckIsName(from, /^NSCore::GUID$/) || this.typecheckIsName(from, /^NSCore::EventTime$/)
            || this.typecheckIsName(from, /^NSCore::DataHash$/) || this.typecheckIsName(from, /^NSCore::CryptoHash$/)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckEntityAndProvidesName(from, this.enumtype) || this.typecheckEntityAndProvidesName(from, this.idkeytype) || this.typecheckEntityAndProvidesName(from, this.guididkeytype)
            || this.typecheckEntityAndProvidesName(from, this.eventtimeidkeytype) || this.typecheckEntityAndProvidesName(from, this.datahashidkeytype) || this.typecheckEntityAndProvidesName(from, this.cryptohashidkeytype)) {
            return this.coerceFromAtomicKey(exp, from);
        }
        else if (this.typecheckAllKeys(from)) {
            const intotype = this.getCPPTypeFor(into, "base");
            if(intotype === "Value") {
                return exp;
            }
            else {
                return this.coerceFromOptionsKey(exp, into);
            }
        }
        else if (this.typecheckIsName(from, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(from, /^NSCore::ISOTime$/) || this.typecheckIsName(from, /^NSCore::Regex$/)
            || this.typecheckTuple(from) || this.typecheckRecord(from)) {
            return exp;
        }
        else if (this.typecheckIsName(from, /^NSCore::MapEntry<.*>$/)) {
            xxxx;
            return `BSQ_NEW_ADD_SCOPE(${this.mangleStringForCpp("$scope$")}, ${this.mangleStringForCpp(from.trkey)}, ${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::Result<.*>$/)) {
            xxxx;
            return `BSQ_NEW_ADD_SCOPE(${this.mangleStringForCpp("$scope$")}, ${this.mangleStringForCpp(from.trkey)}, ${exp})`;
        }
        else if (this.typecheckIsName(from, /^NSCore::Tagged<.*>$/)) {
            xxxx;
            return `BSQ_NEW_ADD_SCOPE(${this.mangleStringForCpp("$scope$")}, ${this.mangleStringForCpp(from.trkey)}, ${exp})`;
        }
        else if (this.typecheckUEntity(from)) {
            return exp;
        }
        else {
           //now from must be Bterm so we are projecting down
           assert(this.getCPPTypeFor(into, "base") === "Value");

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
               return `((KeyValue)${exp})`;
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

    maybeRefableCountableType(tt: MIRType): "no" | "int" | "direct" | "checked" | "special" {
        if (this.typecheckIsName(tt, /^NSCore::None$/) || this.typecheckIsName(tt, /^NSCore::Bool$/)) {
            return "no";
        }
        else if (this.typecheckIsName(tt, /^NSCore::Int$/)) {
            return "int";
        }
        else if (this.typecheckIsName(tt, /^NSCore::String$/) || this.typecheckIsName(tt, /^NSCore::StringOf<.*>$/)) {
            return "direct";
        }
        else if (this.typecheckIsName(tt, /^NSCore::GUID$/) || this.typecheckIsName(tt, /^NSCore::CryptoHash$/)) {
            return "direct";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.idkeytype) || this.typecheckEntityAndProvidesName(tt, this.guididkeytype) || this.typecheckEntityAndProvidesName(tt, this.cryptohashidkeytype)) {
            return "direct";
        }
        else if (this.typecheckIsName(tt, /^NSCore::EventTime$/) || this.typecheckIsName(tt, /^NSCore::DataHash$/)) {
            return "no";
        }
        else if (this.typecheckEntityAndProvidesName(tt, this.enumtype) || this.typecheckEntityAndProvidesName(tt, this.eventtimeidkeytype) || this.typecheckEntityAndProvidesName(tt, this.datahashidkeytype)) {
            return "no";
        }
        else {
            if (this.typecheckAllKeys(tt)) {
                return "checked";
            }
            else if (this.typecheckIsName(tt, /^NSCore::Buffer<.*>$/) || this.typecheckIsName(tt, /^NSCore::ISOTime$/) || this.typecheckIsName(tt, /^NSCore::Regex$/)) {
                return "direct";
            }
            else if (this.typecheckTuple(tt) || this.typecheckRecord(tt)) {
                return "direct";
            }
            else if (this.typecheckIsName(tt, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(tt, /^NSCore::Result<.*>$/) || this.typecheckIsName(tt, /^NSCore::Tagged<.*>$/)) {
               return "special";
            }
            else if(this.typecheckUEntity(tt)) {
                return "direct";
            }
            else if(this.typecheckEphemeral(tt)) {
                return "special";
            }
            else {
                return "checked";
            }
        }
    }

    typeToCPPDefaultValue(ttype: MIRType): string {
        if ( this.typecheckIsName(ttype, /^NSCore::Bool$/)) {
            return "false"
        }
        else if (this.typecheckIsName(ttype, /^NSCore::Int$/)) {
            return "BSQ_VALUE_0";
        }
        else if (this.typecheckIsName(ttype, /^NSCore::EventTime$/) || this.typecheckIsName(ttype, /^NSCore::DataHash$/)) {
            return `${this.getCPPTypeFor(ttype, "storage")}{}`;
        }
        else if (this.typecheckEntityAndProvidesName(ttype, this.enumtype) || this.typecheckEntityAndProvidesName(ttype, this.eventtimeidkeytype) || this.typecheckEntityAndProvidesName(ttype, this.datahashidkeytype)) {
            return `${this.getCPPTypeFor(ttype, "storage")}{}`;
        }
        else if (this.typecheckIsName(ttype, /^NSCore::MapEntry<.*>$/) || this.typecheckIsName(ttype, /^NSCore::Result<.*>$/) || this.typecheckIsName(ttype, /^NSCore::Tagged<.*>$/)) {
            return `${this.getCPPTypeFor(ttype, "storage")}{}`;
         }
        else {
            return "nullptr";
        }
    }

    initializeConceptSubtypeRelation(): void {
        this.assembly.conceptDecls.forEach((tt) => {
            const cctype = this.getMIRType(tt.tkey);
            const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, cctype));
            const keyarray = est.map((et) => et.trkey).sort();

            this.conceptSubtypeRelation.set(tt.tkey, keyarray);
        });
    }

    getSubtypesArrayCount(ckey: MIRNominalTypeKey): number {
        return (this.conceptSubtypeRelation.get(ckey) as string[]).length;
    }

    generateConstructorArgInc(argtype: MIRType, arg: string): string {
        if (!this.maybeRefableCountableType(argtype)) {
            return arg;
        }

        xxxx;

        else {
            return `BSQRef::checkedIncrementOf<${this.typeToCPPType(argtype, "parameter")}>(${arg})`;
        }
    }

    generateCPPEntity(entity: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (this.isSpecialRepType(entity) || this.isSpecialCollectionRepType(entity) || this.isSpecialKeyListRepType(entity)) {
            return undefined;
        }

        const constructor_args = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "parameter")} ${fd.name}`;
        });

        const constructor_initializer = entity.fields.map((fd) => {
            return `${this.mangleStringForCpp(fd.fkey)}(${fd.name})`;
        });

        const destructor_list = entity.fields.map((fd) => {
            const ftype = this.getMIRType(fd.declaredType);
            if (!this.maybeRefableCountableType(ftype)) {
                return undefined;
            }

            if(this.isTupleType(ftype)) {
                if(this.isKnownLayoutTupleType(ftype)) {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
                else {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
            }
            else if(this.isRecordType(ftype)) {
                if(this.isKnownLayoutRecordType(ftype)) {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
                else {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
            }
            else if (this.isUEntityType(ftype)) {
                if (this.assembly.subtypeOf(this.noneType, ftype)) {
                    return `BSQRef::checkedDecrementNoneable(this->${this.mangleStringForCpp(fd.fkey)});`;
                }
                else {
                    return `BSQRef::checkedDecrementFast(this->${this.mangleStringForCpp(fd.fkey)});`;
                }
            }
            else {
                return `BSQRef::checkedDecrement(this->${this.mangleStringForCpp(fd.fkey)});`;
            }
        })
        .filter((fd) => fd !== undefined);

        const fields = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "decl")} ${this.mangleStringForCpp(fd.fkey)};`;
        });

        const vfield_accessors = entity.fields.map((fd) => {
            if (fd.enclosingDecl === entity.tkey) {
                return "NA";
            }
            else {
                const fn = `this->${this.mangleStringForCpp(fd.fkey)}`;
                return `${this.typeToCPPType(this.getMIRType(fd.declaredType) , "return")} get$${this.mangleStringForCpp(fd.fkey)}() { return ${fn}; };`;
            }
        });

        const vcalls = [...entity.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
            if (rcall.enclosingDecl === entity.tkey) {
                return "NA";
            }
            else {
                const resulttype = this.getMIRType(rcall.resultType);
                const rtype = this.typeToCPPType(resulttype, "return");

                const vargs = rcall.params.slice(1).map((fp) => `${this.typeToCPPType(this.getMIRType(fp.type), "parameter")} ${fp.name}`);
                const cargs = rcall.params.map((fp) => fp.name);

                if (this.maybeRefableCountableType(resulttype)) {
                    if (this.isTupleType(resulttype)) {
                        const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(resulttype);

                        for (let i = 0; i < maxlen; ++i) {
                            vargs.push(`BSQRef** $callerslot$${i}`);
                            cargs.push(`$callerslot$${i}`);
                        }
                    }
                    else if (this.isRecordType(resulttype)) {
                        const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(resulttype);

                        for (let i = 0; i < allprops.length; ++i) {
                            vargs.push(`BSQRef** $callerslot$${allprops[i]}`);
                            cargs.push(`$callerslot$${allprops[i]}`);
                        }
                    }
                    else {
                        vargs.push("BSQRef** $callerslot$");
                        cargs.push("$callerslot$");
                    }
                }

                return `${rtype} ${this.mangleStringForCpp(callp[0])}(${vargs.join(", ")})\n`
                    + "    {\n"
                    + `        return ${this.mangleStringForCpp(callp[1])}(${cargs.join(", ")});\n`
                    + "    }\n";
            }
        });

        this.scopectr = 0;
        const faccess = entity.fields.map((f) => this.coerce(`this->${this.mangleStringForCpp(f.fkey)}`, this.getMIRType(f.declaredType), this.anyType));
        const fjoins = faccess.length !== 0 ? faccess.map((fa) => `Runtime::diagnostic_format(${fa})`).join(" + std::u32string(U\", \") + ") : "U\" \"";
        const display = "std::u32string display() const\n"
        + "    {\n"
        + (this.scopectr !== 0 ? `        BSQRefScope<${this.scopectr}> ${this.mangleStringForCpp("$scope$")};\n` : "")
        + `        return std::u32string(U"${entity.tkey}{ ") + ${fjoins} + std::u32string(U" }");\n`
        + "    }";

        return {
            fwddecl: `class ${this.mangleStringForCpp(entity.tkey)};`,
            fulldecl: `class ${this.mangleStringForCpp(entity.tkey)} : public BSQObject\n`
            + "{\n"
            + "public:\n"
            + `    ${fields.join("\n    ")}\n\n`
            + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) : BSQObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)})${constructor_initializer.length !== 0 ? ", " : ""}${constructor_initializer.join(", ")} { ; }\n`
            + `    virtual ~${this.mangleStringForCpp(entity.tkey)}() { ${destructor_list.join(" ")} }\n\n`
            + `    ${display}\n\n`
            + `    ${vfield_accessors.filter((vacf) => vacf !== "NA").join("\n    ")}\n\n`
            + `    ${vcalls.filter((vc) => vc !== "NA").join("\n    ")}\n`
            + "};"
        };
    }
}

export {
    CPPTypeEmitter
};
