//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIREntityType, MIREphemeralListType, MIRRecordType, MIRTupleType, MIRType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTCall, SMTConst, SMTExp, SMTType, VerifierLevel } from "./smt_exp";

import * as assert from "assert";

class SMTTypeEmitter {
    readonly assembly: MIRAssembly;
    private mangledNameMap: Map<string, string> = new Map<string, string>();

    private level: VerifierLevel;

    constructor(assembly: MIRAssembly, level: VerifierLevel, mangledNameMap?: Map<string, string>) {
        this.assembly = assembly;
        this.mangledNameMap = mangledNameMap || new Map<string, string>();

        this.level = level;
    }

    mangle(name: string): string {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }

        return this.mangledNameMap.get(name) as string;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    isType(tt: MIRType, tkey: string): boolean {
        return tt.trkey === tkey;
    }

    isUniqueTupleType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRTupleType) && !(tt.options[0] as MIRTupleType).entries.some((entry) => entry.isOptional);
    }

    isUniqueRecordType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIRRecordType) && !(tt.options[0] as MIRRecordType).entries.some((entry) => entry.isOptional);
    }

    isUniqueEntityType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREntityType);
    }

    isUniqueEphemeralType(tt: MIRType): boolean {
        return tt.options.length === 1 && (tt.options[0] instanceof MIREphemeralListType);
    }

    getSMTTypeFor(tt: MIRType): SMTType {
        if (this.isType(tt, "NSCore::None")) {
            return new SMTType("bsq_none");
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return new SMTType("Bool");
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return new SMTType("Int");
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return this.level === "Strong" ? new SMTType("UFloat") : new SMTType("Real");
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return this.level === "Strong" ? new SMTType("UFloat") : new SMTType("Real");
        }
        else if (this.isType(tt, "NSCore::String")) {
            return this.level === "Strong" ? new SMTType("(Seq (_ BitVec 64))") : new SMTType("String");
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            return new SMTType("bsq_regex");
        }
        else if(this.isUniqueTupleType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.isUniqueRecordType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.isUniqueEntityType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if (this.isUniqueEphemeralType(tt)) {
            return new SMTType(this.mangle(tt.trkey));
        }
        else if(this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType"))) {
            return new SMTType("BKey");
        }
        else {
            return new SMTType("BTerm");
        }
    }

    getSMTTypeTag(tt: MIRType): string {
        assert(!(this.isType(tt, "NSCore::None") || this.isType(tt, "NSCore::Bool") || this.isType(tt, "NSCore::Int") || this.isType(tt, "NSCore::Nat")
            || this.isType(tt, "NSCore::BigInt") || this.isType(tt, "NSCore::BigNat") || this.isType(tt, "NSCore::Float") || this.isType(tt, "NSCore::Decimal")
            || this.isType(tt, "NSCore::String") || this.isType(tt, "NSCore::Regex")), "Special types should be tagged in special ways");


        if (this.isType(tt, "NSCore::None")) {
            return "TypeTag_None";
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return "TypeTag_Bool";
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return "TypeTag_Int";
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return "TypeTag_Nat";
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return "TypeTag_BigInt";
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return "TypeTag_BigNat";
        }
        else if (this.isType(tt, "NSCore::Float")) {
            return "TypeTag_Float";
        }
        else if (this.isType(tt, "NSCore::Decimal")) {
            return "TypeTag_Decimal"
        }
        else if (this.isType(tt, "NSCore::String")) {
            return "TypeTag_String";
        }
        else if (this.isType(tt, "NSCore::Regex")) {
            return "TypeTag_Regex";
        }
        else if (this.isUniqueTupleType(tt)) {
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
        else if (this.isUniqueRecordType(tt)) {
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
        else {
            assert(this.isUniqueEntityType(tt), "Should not be other options")
            return `TypeTag_${this.mangle(tt.trkey)}`;
        }
    }

    getSMTConstructorName(tt: MIRType): { cons: string, box: string, bfield: string } {
        assert(!(this.isType(tt, "NSCore::None") || this.isType(tt, "NSCore::Bool") || this.isType(tt, "NSCore::Int") || this.isType(tt, "NSCore::Nat")
            || this.isType(tt, "NSCore::BigInt") || this.isType(tt, "NSCore::BigNat") || this.isType(tt, "NSCore::Float") || this.isType(tt, "NSCore::Decimal")
            || this.isType(tt, "NSCore::String") || this.isType(tt, "NSCore::Regex")), "Special types should be constructed in special ways");


        const kfix = this.assembly.subtypeOf(tt, this.getMIRType("NSCore::KeyType")) ? "bsqkey_" : "bsqobject_"
        if (this.isUniqueTupleType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else if (this.isUniqueRecordType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else if (this.isUniqueEntityType(tt)) {
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
        else {
            assert(this.isUniqueEphemeralType(tt), "should not be other options")
            return { cons: `${this.mangle(tt.trkey)}@cons`, box: `${this.mangle(tt.trkey)}@box`, bfield: `${kfix}${this.mangle(tt.trkey)}_value` };
        }
    }

    private coerceFromAtomicToKey(exp: SMTExp, from: MIRType): { typetag: string, cexp: SMTExp } {
        assert(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType")));

        if (from.trkey === "NSCore::None") {
            return { typetag: "TypeTag_None", cexp: new SMTConst("BKey@none") };
        }
        else {
            let objval: SMTExp | undefined = undefined;
            let typetag = "[NOT SET]";

            if (this.isType(from, "NSCore::Bool")) {
                objval = new SMTCall("bsqkey_bool@cons", [exp]);
                typetag = "TypeTag_Bool";
            }
            else if (this.isType(from, "NSCore::Int")) {
                objval = new SMTCall("bsqkey_int@cons", [exp]);
                typetag = "TypeTag_Int";
            }
            else if (this.isType(from, "NSCore::Nat")) {
                objval = new SMTCall("bsqkey_nat@cons", [exp]);
                typetag = "TypeTag_Nat";
            }
            else if (this.isType(from, "NSCore::BigInt")) {
                objval = new SMTCall("bsqkey_bigint@cons", [exp]);
                typetag = "TypeTag_BigInt";
            }
            else if (this.isType(from, "NSCore::BigNat")) {
                objval = new SMTCall("bsqkey_bignat@cons", [exp]);
                typetag = "TypeTag_BigNat";
            }
            else if (this.isType(from, "NSCore::String")) {
                objval = new SMTCall("bsqkey_string@cons", [exp]);
                typetag = "TypeTag_String";
            }
            else if (this.isUniqueTupleType(from)) {
                objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else if (this.isUniqueRecordType(from)) {
                objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }
            else {
                assert(this.isUniqueEntityType(from));

                objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                typetag = this.getSMTTypeTag(from);
            }

            return { typetag: typetag, cexp: new SMTCall("BKey@cons", [new SMTConst(typetag), objval as SMTExp]) };
        }
    }

    private coerceFromAtomicToTerm(exp: SMTExp, from: MIRType): { typetag: string, cexp: SMTExp } {
        if (from.trkey === "NSCore::None") {
            return { typetag: "TypeTag_None", cexp: new SMTConst(`BTerm@none`) };
        }
        else {
            if(this.assembly.subtypeOf(from, this.getMIRType("NSCore::KeyType"))) {
                const bkey = this.coerceFromAtomicToKey(exp, from);
                return { typetag: bkey.typetag, cexp: new SMTCall("BTerm@cons", [new SMTConst(bkey.typetag), new SMTCall("bsqobject_key@cons", [bkey.cexp])]) }; 
            }
            else {
                let objval: SMTExp | undefined = undefined;
                let typetag = "[NOT SET]";

                if (this.isType(from, "NSCore::Regex")) {
                    objval = new SMTCall("bsq_regex@cons", [exp]);
                    typetag = "TypeTag_Regex";
                }
                else if (this.isUniqueTupleType(from)) {
                    objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else if (this.isUniqueRecordType(from)) {
                    objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }
                else {
                    assert(this.isUniqueEntityType(from));

                    objval = new SMTCall(this.getSMTConstructorName(from).box, [exp]);
                    typetag = this.getSMTTypeTag(from);
                }

                return { typetag: typetag, cexp: new SMTCall("BTerm@cons", [new SMTConst(typetag), objval as SMTExp]) };
            }
        }
    }

    private coerceKeyIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            const oexp = new SMTCall("BKey_value", [exp]);

            if (this.isType(into, "NSCore::Bool")) {
                return new SMTCall("bsqkey_bool_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Int")) {
                return new SMTCall("bsqkey_int_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::Nat")) {
                return new SMTCall("bsqkey_nat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigInt")) {
                return new SMTCall("bsqkey_bigint_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::BigNat")) {
                return new SMTCall("bsqkey_bignat_value", [oexp]);
            }
            else if (this.isType(into, "NSCore::String")) {
                return new SMTCall("bsqkey_string_value", [oexp]);
            }
            else if (this.isUniqueTupleType(into)) {
                return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else if (this.isUniqueRecordType(into)) {
                return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
            }
            else {
                assert(this.isUniqueEntityType(into));

                return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
            }
        }
    }

    private coerceTermIntoAtomic(exp: SMTExp, into: MIRType): SMTExp {
        if (this.isType(into, "NSCore::None")) {
            return new SMTConst("bsq_none@literal");
        }
        else {
            if(this.assembly.subtypeOf(into, this.getMIRType("NSCore::KeyType"))) {
                return this.coerceKeyIntoAtomic(new SMTCall("BTerm_value", [exp]), into)
            }
            else {
                const oexp = new SMTCall("BTerm_value", [exp]);

                if (this.isType(into, "NSCore::Regex")) {
                    return new SMTCall("bsq_regex@cons", [oexp]);
                }
                else if (this.isUniqueTupleType(into)) {
                    return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else if (this.isUniqueRecordType(into)) {
                    return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
                }
                else {
                    assert(this.isUniqueEntityType(into));

                    return new SMTCall(this.getSMTConstructorName(into).bfield, [oexp]);
                }
            }
        }
    }

    coerce(exp: SMTExp, from: MIRType, into: MIRType): SMTExp {
        const smtfrom = this.getSMTTypeFor(from);
        const smtinto = this.getSMTTypeFor(into);

        if (smtfrom.name === smtinto.name) {
            return exp;
        }
        else if (smtinto.name === "BKey") {
            if(smtfrom.name === "BTerm") {
                return new SMTCall("BTerm_value", [exp]);
            }
            else {
                return this.coerceFromAtomicToKey(exp, from).cexp;
            }
        }
        else if (smtinto.name === "BTerm") {
            if(smtfrom.name === "BKey") {
                return new SMTCall("BTerm@cons", [new SMTCall("BKey_type", [exp]), new SMTCall("bsqobject_key@cons", [exp])]);
            }
            else {
                return this.coerceFromAtomicToTerm(exp, from).cexp;
            }
        }
        else {
            if (smtfrom.name === "BKey") {
                return this.coerceKeyIntoAtomic(exp, into);
            }
            else {
                assert(smtfrom.name === "BTerm");

                return this.coerceTermIntoAtomic(exp, into);
            }
        }
    }

    isSpecialReprEntity(tt: MIRType): boolean {
        if (this.isType(tt, "NSCore::None")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::Bool")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::Int")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::Nat")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::BigInt")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::BigNat")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::String")) {
            return true;
        }
        else if (this.isType(tt, "NSCore::String")) {
            return true;
        }
        else {
            return false;
        }
    }
}

export {
    SMTTypeEmitter
};
