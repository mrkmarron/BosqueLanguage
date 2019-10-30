//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRConceptTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType } from "../../compiler/mir_assembly";
import { sanitizeStringForCpp } from "./cpputils";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";

class CPPTypeEmitter {
    readonly assembly: MIRAssembly;

    readonly anyType: MIRType;

    readonly noneType: MIRType;
    readonly boolType: MIRType;
    readonly intType: MIRType;
    readonly stringType: MIRType;

    constructor(assembly: MIRAssembly) {
        this.assembly = assembly;

        this.anyType = assembly.typeMap.get("NSCore::Any") as MIRType;

        this.noneType = assembly.typeMap.get("NSCore::None") as MIRType;
        this.boolType = assembly.typeMap.get("NSCore::Bool") as MIRType;
        this.intType = assembly.typeMap.get("NSCore::Int") as MIRType;
        this.stringType = assembly.typeMap.get("NSCore::String") as MIRType;
    }

    getMIRType(tkey: MIRResolvedTypeKey): MIRType {
        return this.assembly.typeMap.get(tkey) as MIRType;
    }

    static isPrimitiveType(tt: MIRType): boolean {
        if (tt.options.length !== 1) {
            return false;
        }

        const uname = tt.options[0].trkey;
        return (uname === "NSCore::Bool" || uname === "NSCore::Int" ||  uname === "NSCore::String");
    }

    static isFixedTupleType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRTupleType)) {
            return false;
        }

        const tup = tt.options[0] as MIRTupleType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    static isFixedRecordType(tt: MIRType): boolean {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof MIRRecordType)) {
            return false;
        }

        const tup = tt.options[0] as MIRRecordType;
        return !tup.isOpen && !tup.entries.some((entry) => entry.isOptional);
    }

    static isUEntityType(tt: MIRType): boolean {
        return (tt.trkey !== "NSCore::None") && !CPPTypeEmitter.isPrimitiveType(tt) && (tt.options.length === 1 && tt.options[0] instanceof MIREntityType);
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

    static isRefableReturnType(tt: MIRType): boolean {
        if (tt.options.length !== 1) {
            return true;
        }

        const uname = tt.options[0].trkey;
        if (uname === "NSCore::None" || uname === "NSCore::Bool" ||  uname === "NSCore::Int") {
            return false;
        }

        if (CPPTypeEmitter.isFixedTupleType(tt) || CPPTypeEmitter.isFixedRecordType(tt)) {
            return false;
        }

        return true;
    }

    typeToCPPType(ttype: MIRType, declspec: "base" | "parameter" | "return" | "local"): string {
        if (CPPTypeEmitter.isPrimitiveType(ttype)) {
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
        else if (CPPTypeEmitter.isFixedTupleType(ttype)) {
            return `BSQTupleFixed<${(ttype.options[0] as MIRTupleType).entries.length}>` + (declspec === "parameter" ? "&" : "");
        }
        else if (CPPTypeEmitter.isFixedRecordType(ttype)) {
            return `BSQRecordFixed<MIRRecordTypeEnum::${sanitizeStringForCpp(ttype.trkey)}, ${(ttype.options[0] as MIRTupleType).entries.length}>` + (declspec === "parameter" ? "&" : "");
        }
        else if (CPPTypeEmitter.isUEntityType(ttype)) {
            return sanitizeStringForCpp(ttype.trkey) + (declspec !== "base" ? "*" : "");
        }
        else {
            return "Value";
        }
    }

    generateFixedTupleAccessor(idx: number): string {
        return `.atFixed<${idx}>()`;
    }

    generateFixedRecordAccessor(ttype: MIRType, p: string): string {
        return `.atFixed<${CPPTypeEmitter.getFixedRecordType(ttype).entries.findIndex((entry) => entry.name === p)}>()`;
    }

    generateCPPEntity(entity: MIREntityTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (entity.tkey === "NSCore::None" || entity.tkey === "NSCore::Bool" || entity.tkey === "NSCore::Int" || entity.tkey === "NSCore::String") {
            return undefined;
        }

        const constructor_args = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.assembly.typeMap.get(fd.declaredType) as MIRType)} ${fd.fname}`;
        });

        const constructor_initializer = entity.fields.map((fd) => {
            return isInlinableType(this.assembly.typeMap.get(fd.declaredType) as MIRType) ? `${fd.fname}(${fd.fname})` : `${fd.fname}(std::move(${fd.fname}))`;
        });

        const fields = entity.fields.map((fd) => {
            return `const ${this.typeToCPPType(this.assembly.typeMap.get(fd.declaredType) as MIRType)} ${fd.fname};`;
        });

        const vfield_accessors = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.assembly.typeMap.get(fd.declaredType) as MIRType)} get$${fd.fname}() const { return this->${fd.fname}; };`;
        });

        const vcalls = [...entity.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
            const rtype = this.typeToCPPType(this.assembly.typeMap.get(rcall.resultType) as MIRType);
            const vargs = rcall.params.map((fp) => `${this.typeToCPPType(this.assembly.typeMap.get(fp.type) as MIRType)} ${fp.name}`).join(", ");
            const cargs = rcall.params.map((fp) => fp.name).join(", ");
            return `${rtype} ${sanitizeForCpp(callp[0])}(${vargs}) const
            {
                return this->${sanitizeForCpp(callp[1])}(${cargs});
            }`;
        });

        return {
            fwddecl: `class ${sanitizeForCpp(entity.tkey)};`,
            fulldecl: `class ${sanitizeForCpp(entity.tkey)} : public RefCountBase, ${entity.provides.map((pkey) => `public virtual ${sanitizeForCpp(pkey)}`).join(", ")}
            {
            public:
                ${sanitizeForCpp(entity.tkey)}(${constructor_args.join(", ")})${constructor_initializer.length !== 0 ? (" : " + constructor_initializer.join(", ")) : ""} { ; }
                virtual ~${sanitizeForCpp(entity.tkey)}() = default;

                ${fields.join("\t\t\t\t\n")}

                ${vfield_accessors.join("\t\t\t\t\n")}

                ${vcalls.join("\t\t\t\t\n")}
            };`
        };
    }

    generateCPPConcept(concept: MIRConceptTypeDecl): { fwddecl: string, fulldecl: string } | undefined {
        if (concept.tkey === "NSCore::Any" || concept.tkey === "NSCore::Some" || concept.tkey === "NSCore::Truthy" || concept.tkey === "NSCore::Parsable"
            || concept.tkey === "NSCore::Tuple" || concept.tkey === "NSCore::Record" || concept.tkey === "NSCore::Object") {
            return undefined;
        }

        const vfield_accessors = concept.fields.map((fd) => {
            return `virtual ${this.typeToCPPType(this.assembly.typeMap.get(fd.declaredType) as MIRType)} get$${fd.fname}() const override { return this->${fd.fname}; };`;
        });

        const vcalls = [...concept.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
            const rtype = this.typeToCPPType(this.assembly.typeMap.get(rcall.resultType) as MIRType);
            const vargs = rcall.params.map((fp) => `${this.typeToCPPType(this.assembly.typeMap.get(fp.type) as MIRType)} ${fp.name}`).join(", ");
            return `virtual ${rtype} ${sanitizeForCpp(callp[0])}(${vargs}) const = 0;`;
        });

        return {
            fwddecl: `class ${sanitizeForCpp(concept.tkey)};`,
            fulldecl: `class ${sanitizeForCpp(concept.tkey)} : ${concept.provides.map((pkey) => `public virtual ${sanitizeForCpp(pkey)}`).join(", ")}
            {
            public:
                ${sanitizeForCpp(concept.tkey)}() { ; }
                virtual ~${sanitizeForCpp(concept.tkey)}() = default;

                ${vfield_accessors.join("\t\t\t\t\n")}

                ${vcalls.join("\t\t\t\t\n")}
            };`
        };
    }
}

export {
    CPPTypeEmitter
};
