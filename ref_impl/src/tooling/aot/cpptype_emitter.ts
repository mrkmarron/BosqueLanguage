//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRTypeOption } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    scopectr: number = 0;

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

    isPrimitiveType(tt: MIRType): boolean {
        if (tt.options.length !== 1) {
            return false;
        }

        const uname = tt.options[0].trkey;
        return (uname === "NSCore::Bool" || uname === "NSCore::Int" ||  uname === "NSCore::String");
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
        return this.mangleStringForCpp(`{${frec.entries.map((entry) => entry.name).join(", ")}}`);
    }

    maybeRefableCountableType(tt: MIRType): boolean {
        const allinlineable = tt.options.every((opt) => {
            const uname = opt.trkey;
            return (uname === "NSCore::None" || uname === "NSCore::Bool" || uname === "NSCore::Int");
        });

        if (allinlineable) {
            return false;
        }

        if (this.isFixedTupleType(tt) || this.isFixedRecordType(tt)) {
            return false;
        }

        return true;
    }

    typeToCPPType(ttype: MIRType, declspec: "base" | "parameter" | "return" | "decl"): string {
        if (this.isPrimitiveType(ttype)) {
            if (ttype.trkey === "NSCore::Bool") {
                return "bool";
            }
            else if (ttype.trkey === "NSCore::Int") {
                return "int64_t";
            }
            else {
                return "BSQString" + (declspec !== "base" ? "*" : "");
            }
        }
        else if (this.isFixedTupleType(ttype)) {
            return `BSQTupleFixed<${(ttype.options[0] as MIRTupleType).entries.length}>`;
        }
        else if (this.isFixedRecordType(ttype)) {
            return `BSQRecordFixed<FixedRecordPropertyListEnum::${this.generateFixedRecordPropertyName(ttype.options[0] as MIRRecordType)}, ${(ttype.options[0] as MIRTupleType).entries.length}>`;
        }
        else if (this.isUEntityType(ttype)) {
            return this.mangleStringForCpp(ttype.trkey) + (declspec !== "base" ? "*" : "");
        }
        else {
            return "Value";
        }
    }

    registerTypeBoxing(from: MIRTypeOption, into: MIRType): string {
        const tbi = this.typeboxings.findIndex((tb) => tb.from.trkey === from.trkey && tb.into.trkey === into.trkey);
        if (tbi !== -1) {
            return this.typeboxings[tbi].fkey;
        }

        const fkey = "BOX_" + this.mangleStringForCpp(`${from.trkey}_${into.trkey}`);
        this.typeboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    boxIfNeeded(exp: string, from: MIRType, into: MIRType): string {
        if (this.isPrimitiveType(from)) {
            if (this.isPrimitiveType(into)) {
                return exp;
            }

            if (from.trkey === "NSCore::Bool") {
                return `BSQ_BOX_VALUE_BOOL(${exp})`;
            }
            else if (from.trkey === "NSCore::Int") {
                return `BSQ_BOX_VALUE_INT(${exp})`;
            }
            else {
                return exp;
            }
        }
        else if (this.isFixedTupleType(from)) {
            return (from.trkey !== into.trkey) ? `Runtime::${this.registerTypeBoxing(from.options[0], into)}($scope$.getCallerSlot<${this.scopectr++}>(), ${exp})` : exp;
        }
        else if (this.isFixedRecordType(from)) {
            return (from.trkey !== into.trkey) ? `Runtime::${this.registerTypeBoxing(from.options[0], into)}($scope$.getCallerSlot<${this.scopectr++}>(), ${exp})` : exp;
        }
        else if (this.isUEntityType(from)) {
            return exp;
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

        const fkey = "UNBOX_" + this.mangleStringForCpp(`${from.trkey}_${into.trkey}`);
        this.typeunboxings.push({ fkey: fkey, from: from, into: into });

        return fkey;
    }

    unboxIfNeeded(exp: string, from: MIRType, into: MIRType): string {
        if (this.isPrimitiveType(into)) {
            if (this.isPrimitiveType(from)) {
                return exp;
            }

            if (into.trkey === "NSCore::Bool") {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else if (into.trkey === "NSCore::Int") {
                return `BSQ_GET_VALUE_INT(${exp})`;
            }
            else {
                return `BSQ_GET_VALUE_PTR(${exp}, BSQString)`;
            }
        }
        else if (this.isFixedTupleType(into)) {
            return (from.trkey !== into.trkey) ? `Runtime::${this.registerTypeUnBoxing(from, into.options[0])}(exp)` : exp;
        }
        else if (this.isFixedRecordType(into)) {
            return (from.trkey !== into.trkey) ? `Runtime::${this.registerTypeUnBoxing(from, into.options[0])}(exp)` : exp;
        }
        else if (this.isUEntityType(into)) {
            return (from.trkey !== into.trkey) ? `BSQ_GET_VALUE_PTR(${exp}, ${this.typeToCPPType(into, "base")})` : exp;
        }
        else {
            return exp;
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
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

    generateFixedTupleAccessor(idx: number): string {
        return `.atFixed<${idx}>()`;
    }

    generateFixedRecordAccessor(ttype: MIRType, p: string): string {
        return `.atFixed<${CPPTypeEmitter.getFixedRecordType(ttype).entries.findIndex((entry) => entry.name === p)}>()`;
    }

    generateConstructorArgInc(argtype: MIRType, arg: string): string {
        if (!this.maybeRefableCountableType(argtype)) {
            return arg;
        }

        if (!this.assembly.subtypeOf(this.boolType, argtype) && !this.assembly.subtypeOf(this.intType, argtype)) {
            if (this.assembly.subtypeOf(this.noneType, argtype)) {
                return `BSQRef::checkedIncrementNoneable(${arg})`;
            }
            else {
                return `BSQRef::checkedIncrementFast${this.typeToCPPType(argtype, "parameter")}(${arg})`;
            }
        }
        else {
            return `BSQRef::checkedIncrement(${arg})`;
        }
    }

    generateCPPEntity(entity: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (!this.doDefaultEmitOnEntity(entity)) {
            return undefined;
        }

        const constructor_args = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "parameter")} ${fd.name}`;
        });

        const constructor_initializer = entity.fields.map((fd) => {
            return `${fd.name}(${fd.name})`;
        });

        const destructor_list = entity.fields.map((fd) => {
            const ftype = this.getMIRType(fd.declaredType);
            if (!this.maybeRefableCountableType(ftype)) {
                return undefined;
            }

            if (!this.assembly.subtypeOf(this.boolType, ftype) && !this.assembly.subtypeOf(this.intType, ftype)) {
                if (this.assembly.subtypeOf(this.noneType, ftype)) {
                    return `BSQRef::checkedDecrementNoneable(this->${fd.name});`;
                }
                else {
                    return `BSQRef::checkedDecrementFast(this->${fd.name});`;
                }
            }
            else {
                return `BSQRef::checkedDecrement(this->${fd.name});`;
            }
        })
        .filter((fd) => fd !== undefined);

        const fields = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "decl")} ${fd.name};`;
        });

        const vfield_accessors = entity.fields.map((fd) => {
            if (!fd.attributes.includes("virtual") && !fd.attributes.includes("override")) {
                return "NA";
            }
            else {
                const fn = `this->${fd.name}`;
                const fdv = this.coerce(fn, this.getMIRType(fd.declaredType), this.anyType);
                return `Value get$${fd.name}() const { return ${fdv}; };`;
            }
        });

        const vcalls = [...entity.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
            if (!rcall.attributes.includes("override")) {
                return "NA";
            }
            else {
                const resulttype = this.getMIRType(rcall.resultType);
                const rtype = this.typeToCPPType(resulttype, "return");

                const vargs = rcall.params.slice(1).map((fp) => `${this.typeToCPPType(this.getMIRType(fp.type), "parameter")} ${fp.name}`);
                const cargs = rcall.params.map((fp) => fp.name);
                if (this.maybeRefableCountableType(resulttype)) {
                    vargs.push("BSQRef** $callerslot$");
                    cargs.push("$callerslot$");
                }

                return `${rtype} ${this.mangleStringForCpp(callp[0])}(${vargs.join(", ")})\n`
                    + "    {\n"
                    + `        return ${this.mangleStringForCpp(callp[1])}(${cargs.join(", ")});\n`
                    + "    }\n";
            }
        });

        const faccess = entity.fields.map((f) => this.coerce(`this->${f.name}`, this.getMIRType(f.declaredType), this.anyType));
        const fjoins = faccess.length !== 0 ? faccess.map((fa) => `Runtime::diagnostic_format(${fa})`).join(" + \", \" + ") : "\" \"";
        const display = "std::string display() const\n"
        + "    {\n"
        + `        return std::string("${entity.tkey}{ ") + ${fjoins} + std::string(" }");\n`
        + "    }";

        return {
            fwddecl: `class ${this.mangleStringForCpp(entity.tkey)};`,
            fulldecl: `class ${this.mangleStringForCpp(entity.tkey)} : public BSQObject\n`
            + "{\n"
            + "public:\n"
            + `    ${fields.join("\n    ")}\n\n`
            + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) : BSQObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)})${constructor_initializer.length !== 0 ? ", " : ""}${constructor_initializer.join(", ")} { ; }\n`
            + `    virtual ~${this.mangleStringForCpp(entity.tkey)}() { ${destructor_list.join("; ")} }\n\n`
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
