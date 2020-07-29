//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl } from "./assembly";
import { Expression } from "./body";

class ResolvedAtomType {
    readonly idStr: string;

    constructor(rstr: string) {
        this.idStr = rstr;
    }
}

class ResolvedConceptAtomTypeEntry {
    readonly idStr: string;
    readonly concept: ConceptTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(idstr: string, concept: ConceptTypeDecl, binds: Map<string, ResolvedType>) {
        this.idStr = idstr;
        this.concept = concept;
        this.binds = binds;
    }

    static create(concept: ConceptTypeDecl, binds: Map<string, ResolvedType>): ResolvedConceptAtomTypeEntry {
        let name = concept.ns + "::" + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + ">";
        }

        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}

class ResolvedConceptAtomType extends ResolvedAtomType {
    readonly conceptTypes: ResolvedConceptAtomTypeEntry[];

    constructor(rstr: string, concepts: ResolvedConceptAtomTypeEntry[]) {
        super(rstr);
        this.conceptTypes = concepts;
    }

    static create(concepts: ResolvedConceptAtomTypeEntry[]): ResolvedConceptAtomType {
        const sortedConcepts = concepts.sort((a, b) => a.idStr.localeCompare(b.idStr));
        const rstr = sortedConcepts.map((cpt) => cpt.idStr).join("&");

        return new ResolvedConceptAtomType(rstr, sortedConcepts);
    }
}

class ResolvedEntityAtomType extends ResolvedAtomType {
    readonly object: EntityTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(rstr: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(rstr);
        this.object = object;
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = object.ns + "::" + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).idStr).join(", ") + ">";
        }

        return new ResolvedEntityAtomType(name, object, binds);
    }
}

class ResolvedLiteralAtomType extends ResolvedAtomType {
    readonly oftype: ResolvedEntityAtomType;
    readonly typevalue: boolean | number | {enumtype: ResolvedType, enumvalue: string} | undefined;

    constructor(rstr: string, oftype: ResolvedEntityAtomType, ofvalue: boolean | number | {enumtype: ResolvedType, enumvalue: string} | undefined) {
        super(rstr);
        this.oftype = oftype;
        this.typevalue = ofvalue;
    }

    static create(oftype: ResolvedEntityAtomType, ofvalue: boolean | number | {enumtype: ResolvedType, enumvalue: string} | undefined): ResolvedLiteralAtomType {
        return new ResolvedLiteralAtomType(``, oftype, ofvalue);
    }
}

class ResolvedTupleAtomTypeEntry {
    readonly type: ResolvedType;
    readonly isOptional: boolean;

    constructor(type: ResolvedType, isOpt: boolean) {
        this.isOptional = isOpt;
        this.type = type;
    }
}

class ResolvedTupleAtomType extends ResolvedAtomType {
    readonly isvalue: boolean;
    readonly isvirtual: boolean;
    readonly types: ResolvedTupleAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, isvirtual: boolean, types: ResolvedTupleAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.isvirtual = isvirtual;
        this.types = types;
    }

    static create(isvalue: boolean, entries: ResolvedTupleAtomTypeEntry[]): ResolvedTupleAtomType {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        return new ResolvedTupleAtomType((isvalue ? "#[" : "@[") + cvalue + "]", isvalue, entries.some((entry) => entry.isOptional), entries);
    }
}

class ResolvedRecordAtomTypeEntry {
    readonly name: string;
    readonly type: ResolvedType;
    readonly isOptional: boolean;

    constructor(name: string, type: ResolvedType, isOpt: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
}

class ResolvedRecordAtomType extends ResolvedAtomType {
    readonly isvalue: boolean;
    readonly isvirtual: boolean;
    readonly entries: ResolvedRecordAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, isvirtual: boolean, entries: ResolvedRecordAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.isvirtual = isvirtual;
        this.entries = entries;
    }

    static create(isvalue: boolean, entries: ResolvedRecordAtomTypeEntry[]): ResolvedRecordAtomType {
        let simplifiedEntries: ResolvedRecordAtomTypeEntry[] = [...entries];
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));
        let cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");

        return new ResolvedRecordAtomType((isvalue ? "#{" : "@{") + cvalue + "}", isvalue, simplifiedEntries.some((entry) => entry.isOptional) , simplifiedEntries);
    }
}

class ResolvedEphemeralListType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(rstr: string, types: ResolvedType[]) {
        super(rstr);
        this.types = types;
    }

    static create(entries: ResolvedType[]): ResolvedEphemeralListType {
        const simplifiedEntries = [...entries];
        const cvalue = simplifiedEntries.map((entry) => entry.idStr).join(", ");
        return new ResolvedEphemeralListType("(|" + cvalue + "|)", simplifiedEntries);
    }
}

class ResolvedType {
    readonly idStr: string;
    readonly options: ResolvedAtomType[];

    constructor(rstr: string, options: ResolvedAtomType[]) {
        this.idStr = rstr;
        this.options = options;
    }

    static createEmpty(): ResolvedType {
        return new ResolvedType("", []);
    }

    static createSingle(type: ResolvedAtomType): ResolvedType {
        return new ResolvedType(type.idStr, [type]);
    }

    static create(types: ResolvedAtomType[]): ResolvedType {
        if (types.length === 0) {
            return ResolvedType.createEmpty();
        }
        else if (types.length === 1) {
            return ResolvedType.createSingle(types[0]);
        }
        else {
            const atoms = types.sort((a, b) => a.idStr.localeCompare(b.idStr));
            const res = atoms.map((arg) => arg.idStr).join("|");

            return new ResolvedType(res, atoms);
        }
    }

    static tryGetOOTypeInfo(t: ResolvedType): ResolvedEntityAtomType | ResolvedConceptAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedEntityAtomType) {
            return (t.options[0] as ResolvedEntityAtomType);
        }
        else if (t.options[0] instanceof ResolvedConceptAtomType) {
            return t.options[0] as ResolvedConceptAtomType;
        }
        else {
            return undefined;
        }
    }

    static tryGetTupleTypeInfo(t: ResolvedType): ResolvedTupleAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedTupleAtomType) {
            return (t.options[0] as ResolvedTupleAtomType);
        }
        else {
            return undefined;
        }
    }

    static tryGetRecordTypeInfo(t: ResolvedType): ResolvedRecordAtomType| undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedRecordAtomType) {
            return (t.options[0] as ResolvedRecordAtomType);
        }
        else {
            return undefined;
        }
    }

    isEmptyType(): boolean {
        return this.options.length === 0;
    }

    isUniqueTupleTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return (this.options[0] instanceof ResolvedTupleAtomType) && !(this.options[0] as ResolvedTupleAtomType).isvirtual;
    }

    isUniqueRecordTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return (this.options[0] instanceof ResolvedRecordAtomType) && !(this.options[0] as ResolvedRecordAtomType).isvirtual;
    }

    isUniqueCallTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return this.options[0] instanceof ResolvedEntityAtomType;
    }

    isNoneType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::None";
    }

    isSomeType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Some";
    }

    isAnyType(): boolean {
        return this.options.length === 1 && this.options[0].idStr === "NSCore::Any";
    }

    isGroundedType(): boolean {
        return this.options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return false;
            }
            else if(opt instanceof ResolvedEntityAtomType) {
                return true;
            }
            else if(opt instanceof ResolvedLiteralAtomType) {
                return true;
            }
            else if(opt instanceof ResolvedTupleAtomType) {
                return opt.types.every((entry) => entry.type.isGroundedType());
            }
            else if(opt instanceof ResolvedRecordAtomType) {
                return opt.entries.every((entry) => entry.type.isGroundedType());
            }
            else {
                //ephemeral list should never be in a grounded position
                return false;
            }
        });
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType | ResolvedFunctionType;
    readonly isRef: boolean;
    readonly isOptional: boolean;
    readonly defaultExp: Expression | undefined;

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, isOpt: boolean, isRef: boolean, defaultexp: Expression | undefined) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.defaultExp = defaultexp;
        this.isRef = isRef;
    }
}

class ResolvedFunctionType {
    readonly idStr: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultType: ResolvedType;

    readonly allParamNames: Set<string>;

    constructor(rstr: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType) {
        this.idStr = rstr;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;

        this.allParamNames = new Set<string>();
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType): ResolvedFunctionType {
        const cvalues = params.map((param) => (param.isRef ? "ref " : "") + param.name + (param.isOptional ? "?: " : ": ") + param.type.idStr);
        let cvalue = cvalues.join(", ");

        let recstr = "";
        if (recursive === "yes") {
            recstr = "recursive ";
        }
        if (recursive === "cond") {
            recstr = "recursive? ";
        }

        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.idStr));
        }

        return new ResolvedFunctionType(recstr + "(" + cvalue + ") -> " + resultType.idStr, recursive, params, optRestParamName, optRestParamType, resultType);
    }
}

export { 
    ResolvedAtomType, 
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, 
    ResolvedLiteralAtomType,
    ResolvedTupleAtomTypeEntry, ResolvedTupleAtomType, 
    ResolvedRecordAtomTypeEntry, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType
};
