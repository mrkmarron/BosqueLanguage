//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRConceptTypeDecl, MIRInvokeDecl } from "../../compiler/mir_assembly";
import { isInlinableType, sanitizeForCpp, isUniqueEntityType } from "./cpputils";

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

    typeToCPPTypeForCallArguments(tt: MIRType): string {
        if (isInlinableType(tt)) {
            if (tt.trkey === "NSCore::Bool") {
                return "bool";
            }
            else {
                return "int64_t";
            }
        }
        else if (isUniqueEntityType(tt)) {
            return `const ValueOf<${sanitizeForCpp(tt.trkey)}>&`;
        }
        else {
            return "const Value&";
        }
    }

    typeToCPPType(tt: MIRType): string {
        if (isInlinableType(tt)) {
            if (tt.trkey === "NSCore::Bool") {
                return "bool";
            }
            else {
                return "int64_t";
            }
        }
        else if (isUniqueEntityType(tt)) {
            return `ValueOf<${sanitizeForCpp(tt.trkey)}>`;
        }
        else {
            return "Value";
        }
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
            const vargs = rcall.params.map((fp) => `${this.typeToCPPTypeForCallArguments(this.assembly.typeMap.get(fp.type) as MIRType)} ${fp.name}`).join(", ");
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
            const vargs = rcall.params.map((fp) => `${this.typeToCPPTypeForCallArguments(this.assembly.typeMap.get(fp.type) as MIRType)} ${fp.name}`).join(", ");
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
