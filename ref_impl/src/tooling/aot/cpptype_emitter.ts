//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType, MIRConceptType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

import * as assert from "assert";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    private mangledNameMap: Map<string, string> = new Map<string, string>();

    scopectr: number = 0;

    conceptSubtypeRelation: Map<string, string[]> = new Map<string, string[]>();

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

    isSimpleBoolType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Bool";
    }

    isSimpleIntType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Int";
    }

    isSimpleStringType(tt: MIRType): boolean {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::String";
    }
    
    isKnownLayoutTupleType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRTupleType)) {
            return false;
        }

        const tup = tt.options[0] as MIRTupleType;
        return !tup.entries.some((entry) => entry.isOptional);
    }

    isTupleType(tt: MIRType): boolean {
        return tt.options.every((opt) => opt instanceof MIRTupleType);
    }

    isKnownLayoutRecordType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRRecordType)) {
            return false;
        }

        const tup = tt.options[0] as MIRRecordType;
        return !tup.entries.some((entry) => entry.isOptional);
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
        if (et.tkey === "NSCore::None" || et.tkey === "NSCore::Bool" || et.tkey === "NSCore::Int" || et.tkey === "NSCore::String" || et.tkey === "NSCore::GUID" || et.tkey === "NSCore::Regex") {
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

    static getKnownLayoutTupleType(tt: MIRType): MIRTupleType {
        return tt.options[0] as MIRTupleType;
    }

    static getTupleTypeMaxLength(tt: MIRType): number {
        return Math.max(...tt.options.filter((opt) => opt instanceof MIRTupleType).map((opt) => (opt as MIRTupleType).entries.length));
    }

    static getKnownLayoutRecordType(tt: MIRType): MIRRecordType {
        return tt.options[0] as MIRRecordType;
    }

    static getRecordTypeMaxPropertySet(tt: MIRType): string[] {
        let popts = new Set<string>();
        tt.options.filter((opt) => opt instanceof MIRRecordType).forEach((opt) => (opt as MIRRecordType).entries.forEach((entry) => popts.add(entry.name)));
        return [...popts].sort();
    }

    getKnownPropertyRecordArrayName(tt: MIRType): string {
        const name = `{ ${CPPTypeEmitter.getRecordTypeMaxPropertySet(tt).join(", ")} }`;
        return `KnownPropertySet_${this.mangleStringForCpp(name)}`;
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

    maybeRefableCountableType(tt: MIRType): boolean {
        if(tt.options.every((opt) => {
            const uname = opt.trkey;
            return (uname === "NSCore::None" || uname === "NSCore::Bool");
        })) {
            return false;
        }

        if (tt.options.length === 1 && tt.options[0] instanceof MIREntityType && (this.assembly.entityDecls.get((tt.options[0] as MIREntityType).ekey) as MIREntityTypeDecl).provides.includes("NSCore::Enum")) {
            return false;
        }

        return true;
    }

    typeToCPPType(ttype: MIRType, declspec: "base" | "parameter" | "return" | "decl"): string {
        if (this.isSimpleBoolType(ttype)) {
            return "bool"
        }
        else if (this.isSimpleIntType(ttype)) {
            return "BSQInt";
        }
        else if (this.isSimpleStringType(ttype)) {
            return "BSQString" + (declspec !== "base" ? "*" : "");
        }
        else if (this.isTupleType(ttype)) {
            return `BSQTupleFixed<${CPPTypeEmitter.getTupleTypeMaxLength(ttype)}>` + (declspec === "parameter" ? "&" : "");
        }
        else if (this.isRecordType(ttype)) {
            if (this.isKnownLayoutRecordType(ttype)) {
                return `BSQRecordKnown<${CPPTypeEmitter.getRecordTypeMaxPropertySet(ttype).length}>` + (declspec === "parameter" ? "&" : "");
            }
            else {
                return `BSQRecordFixed<${CPPTypeEmitter.getRecordTypeMaxPropertySet(ttype).length}>` + (declspec === "parameter" ? "&" : "");
            }
        }
        else if (this.isUEntityType(ttype)) {
            return this.mangleStringForCpp(CPPTypeEmitter.getUEntityType(ttype).ekey) + (declspec !== "base" ? "*" : "");
        }
        else {
            return "Value";
        }
    }

    coerce(exp: string, from: MIRType, into: MIRType): string {
        if (this.typeToCPPType(from, "base") === this.typeToCPPType(into, "base")) {
            return exp;
        }

        if (from.trkey === "NSCore::None") {
            return "BSQ_VALUE_NONE";
        }
        else if (this.isSimpleBoolType(from)) {
            return `BSQ_BOX_VALUE_BOOL(${exp})`;
        }
        else if (this.isSimpleIntType(from)) {
            return exp;
        }
        else if (this.isSimpleStringType(from)) {
            return exp;
        }
        else if (this.isTupleType(from)) {
            assert(!(this.isKnownLayoutTupleType(from) && this.isKnownLayoutTupleType(into)), "Shoud be a type error or handled by equality case");

            const fromsize = CPPTypeEmitter.getTupleTypeMaxLength(from);
            if (this.isKnownLayoutTupleType(from)) {
                if (this.isTupleType(into)) {
                    const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                    return `StructuralCoercionOps::convertTupleKnownToFixed<${intosize}, ${fromsize}>(${exp})`;
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQTuple>(StructuralCoercionOps::boxTupleKnown<${fromsize}>(${exp}))`;
                }
            }
            else if (this.isKnownLayoutTupleType(into)) {
                const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                return `StructuralCoercionOps::convertTupleFixedToKnown<${intosize}, ${fromsize}>(${exp})`;
            }
            else {
               if (this.isTupleType(into)) {
                    const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                    if (intosize < fromsize) {
                        return `StructuralCoercionOps::projectTupleDownFixed<${intosize}, ${fromsize}>(${exp})`;
                    }
                    else {
                        return `StructuralCoercionOps::projectTupleUpFixed<${intosize}, ${fromsize}>(${exp})`;
                    }
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQTuple>(StructuralCoercionOps::boxTupleFixed<${fromsize}>(${exp}))`;
                }
            }
        }
        else if (this.isRecordType(from)) {
            assert(!(this.isKnownLayoutRecordType(from) && this.isKnownLayoutRecordType(into)), "Shoud be a type error or handled by equality case");

            const fromset = CPPTypeEmitter.getRecordTypeMaxPropertySet(from);
            if (this.isKnownLayoutRecordType(from)) {
                if (this.isRecordType(into)) {
                    const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                    return `StructuralCoercionOps::convertRecordKnownToFixed<${intoset.length}, ${fromset.length}>(${exp}, ${this.getKnownPropertyRecordArrayName(from)})`;
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQRecord>(StructuralCoercionOps::boxRecordKnown<${fromset.length}>(${exp}, ${this.getKnownPropertyRecordArrayName(from)}))`;
                }
            }
            else if (this.isKnownLayoutRecordType(into)) {
                const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                return `StructuralCoercionOps::convertRecordFixedToKnown<${intoset.length}, ${fromset.length}>(${exp})`;
            }
            else {
               if (this.isRecordType(into)) {
                    const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                    if (intoset.length < fromset.length) {
                        return `StructuralCoercionOps::projectRecordDownFixed<${intoset.length}, ${fromset.length}>(${exp})`;
                    }
                    else {
                        return `StructuralCoercionOps::projectRecordUpFixed<${intoset.length}, ${fromset.length}>(${exp})`;
                    }
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQRecord>(StructuralCoercionOps::boxRecordFixed<${fromset.length}>(${exp}))`;
                }
            }
        }
        else if (this.isUEntityType(from)) {
            return exp;
        }
        else {
            assert(this.typeToCPPType(from, "base") === "Value", "must be a Value mapped type");

            if (this.isSimpleBoolType(into)) {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else if (this.isSimpleIntType(into)) {
                return exp;
            }
            else if (this.isSimpleStringType(into)) {
                return `BSQ_GET_VALUE_PTR(${exp}, BSQString)`;
            }
            else if (this.isTupleType(into)) {
                const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                if (this.isKnownLayoutTupleType(into)) {
                    return `StructuralCoercionOps::unboxTupleKnown<${intosize}>(BSQ_GET_VALUE_PTR(${exp}, BSQTuple))`;
                }
                else {
                    return `StructuralCoercionOps::unboxTupleFixed<${intosize}>(BSQ_GET_VALUE_PTR(${exp}, BSQTuple))`;
                }
            }
            else if (this.isRecordType(into)) {
                const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                if (this.isKnownLayoutRecordType(into)) {
                    return `StructuralCoercionOps::unboxRecordKnown<${intoset.length}>(BSQ_GET_VALUE_PTR(${exp}, BSQRecord))`;
                }
                else {
                    return `StructuralCoercionOps::unboxRecordFixed<${intoset.length}>(BSQ_GET_VALUE_PTR(${exp}, BSQRecord))`;
                }
            }
            else if (this.isUEntityType(into)) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${this.typeToCPPType(into, "base")})`;
            }
            else {
                return exp;
            }
        }
    }

    generateFixedTupleAccessor(idx: number): string {
        return `.atFixed<${idx}>()`;
    }

    generateKnownRecordAccessor(ttype: MIRType, p: string): string {
        return `.atPropertyIndex<${CPPTypeEmitter.getKnownLayoutRecordType(ttype).entries.findIndex((entry) => entry.name === p)}>()`;
    }

    generateFixedRecordAccessor(p: string): string {
        return `.atFixed<MIRPropertyEnum::${p}>()`;
    }

    generateConstructorArgInc(argtype: MIRType, arg: string): string {
        if (!this.maybeRefableCountableType(argtype)) {
            return arg;
        }

        if(this.isTupleType(argtype)) {
            if(this.isKnownLayoutTupleType(argtype)) {
                return `${arg}.copyWithRefInc()`;
            }
            else {
                return `${arg}.copyWithRefInc()`;
            }
        }
        else if(this.isRecordType(argtype)) {
            if(this.isKnownLayoutRecordType(argtype)) {
                return `${arg}.copyWithRefInc()`;
            }
            else {
                return `${arg}.copyWithRefInc()`;
            }
        }
        else if (this.isUEntityType(argtype)) {
            if (this.assembly.subtypeOf(this.noneType, argtype)) {
                return `BSQRef::checkedIncrementNoneable<${this.typeToCPPType(argtype, "base")}>(${arg})`;
            }
            else {
                return `BSQRef::checkedIncrementFast<${this.typeToCPPType(argtype, "base")}>(${arg})`;
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

            if(this.isTupleType(ftype)) {
                if(this.isKnownLayoutTupleType(ftype)) {
                    return `this->${ftype}.allRefDec()`;
                }
                else {
                    return `this->${ftype}.allRefDec()`;
                }
            }
            else if(this.isRecordType(ftype)) {
                if(this.isKnownLayoutRecordType(ftype)) {
                    return `this->${ftype}.allRefDec()`;
                }
                else {
                    return `this->${ftype}.allRefDec()`;
                }
            }
            else if (this.isUEntityType(ftype)) {
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
        const faccess = entity.fields.map((f) => this.coerce(`this->${f.name}`, this.getMIRType(f.declaredType), this.anyType));
        const fjoins = faccess.length !== 0 ? faccess.map((fa) => `Runtime::diagnostic_format(${fa})`).join(" + \", \" + ") : "\" \"";
        const display = "std::string display() const\n"
        + "    {\n"
        + (this.scopectr !== 0 ? `        BSQRefScope<${this.scopectr}> ${this.mangleStringForCpp("$scope$")};\n` : "")
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
