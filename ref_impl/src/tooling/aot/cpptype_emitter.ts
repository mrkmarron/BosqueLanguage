//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRAssembly, MIRType, MIREntityTypeDecl, MIRInvokeDecl, MIRTupleType, MIRRecordType, MIREntityType } from "../../compiler/mir_assembly";
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
            return `BSQTupleFixed<${(ttype.options[0] as MIRTupleType).entries.length}>` + (declspec === "parameter" ? "&" : "");
        }
        else if (this.isFixedRecordType(ttype)) {
            return `BSQRecordFixed<MIRRecordTypeEnum::${sanitizeStringForCpp(ttype.trkey)}, ${(ttype.options[0] as MIRTupleType).entries.length}>` + (declspec === "parameter" ? "&" : "");
        }
        else if (this.isUEntityType(ttype)) {
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
        if (!this.doDefaultEmitOnEntity(entity)) {
            return undefined;
        }

        const constructor_args = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "parameter")} ${fd.fname}`;
        });

        const constructor_initializer = entity.fields.map((fd) => {
            return `${fd.fname}(${fd.fname})`;
        });

        const destructor_list = entity.fields.map((fd) => {
            const ftype = this.getMIRType(fd.declaredType);
            if (!this.maybeRefableCountableType(ftype)) {
                return undefined;
            }

            if (!this.assembly.subtypeOf(this.boolType, ftype) && !this.assembly.subtypeOf(this.intType, ftype)) {
                if (this.assembly.subtypeOf(this.noneType, ftype)) {
                    return `BSQRef::checkedDecrementNoneable(this->${fd.fname});`;
                }
                else {
                    return `BSQRef::checkedDecrementFast(this->${fd.fname});`;
                }
            }
            else {
                return `BSQRef::checkedDecrement(this->${fd.fname});`;
            }
        })
        .filter((fd) => fd !== undefined);

        const fields = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "decl")} ${fd.fname};`;
        });

        const vfield_accessors = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "return")} get$${fd.fname}() const { return this->${fd.fname}; };`;
        });

        const vcalls = [...entity.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1])) as MIRInvokeDecl;
            const rtype = this.typeToCPPType(this.getMIRType(rcall.resultType), "return");
            const vargs = rcall.params.map((fp) => `${this.typeToCPPType(this.getMIRType(fp.type), "parameter")} ${fp.name}`).join(", ");
            const cargs = rcall.params.map((fp) => fp.name).join(", ");
            return `${rtype} ${sanitizeStringForCpp(callp[0])}(${vargs}) const
            {
                return this->${sanitizeStringForCpp(callp[1])}(${cargs});
            }`;
        });

        return {
            fwddecl: `class ${sanitizeStringForCpp(entity.tkey)};`,
            fulldecl: `class ${sanitizeStringForCpp(entity.tkey)} : public BSQObject
            {
            public:
                ${sanitizeStringForCpp(entity.tkey)}(${constructor_args.join(", ")})${constructor_initializer.length !== 0 ? (" : " + constructor_initializer.join(", ")) : ""} { ; }
                virtual ~${sanitizeStringForCpp(entity.tkey)}() { ${destructor_list.join("; ")} };

                ${fields.join("\t\t\t\t\n")}

                ${vfield_accessors.join("\t\t\t\t\n")}

                ${vcalls.join("\t\t\t\t\n")}
            };`
        };
    }
}

export {
    CPPTypeEmitter
};
