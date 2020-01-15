//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl } from "./assembly";
import { StorageDeclarator } from "./type_signature";

function formatStorageInfo(storage: StorageDeclarator): string {
    return (storage.isValue ? "#" : "") + (storage.isUnique ? "*" : "") + (storage.isBorrow ? "^" : "");
}

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

class ResolvedTupleAtomTypeEntry {
    readonly type: ResolvedType;
    readonly isOptional: boolean;

    constructor(type: ResolvedType, isOpt: boolean) {
        this.isOptional = isOpt;
        this.type = type;
    }
}

class ResolvedTupleAtomType extends ResolvedAtomType {
    readonly types: ResolvedTupleAtomTypeEntry[];

    constructor(rstr: string, types: ResolvedTupleAtomTypeEntry[]) {
        super(rstr);
        this.types = types;
    }

    static create(entries: ResolvedTupleAtomTypeEntry[]): ResolvedTupleAtomType {
        let simplifiedEntries = [...entries];
        let cvalue = simplifiedEntries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        return new ResolvedTupleAtomType("[" + cvalue + "]", simplifiedEntries);
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
    readonly entries: ResolvedRecordAtomTypeEntry[];

    constructor(rstr: string, entries: ResolvedRecordAtomTypeEntry[]) {
        super(rstr);
        this.entries = entries;
    }

    static create(entries: ResolvedRecordAtomTypeEntry[]): ResolvedRecordAtomType {
        let simplifiedEntries: ResolvedRecordAtomTypeEntry[] = [...entries];
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));
        let cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");

        return new ResolvedRecordAtomType("{" + cvalue + "}", simplifiedEntries);
    }
}

class ResolvedEphemeralListTypeEntry {
    readonly storage: StorageDeclarator;
    readonly type: ResolvedType;

    constructor(storage: StorageDeclarator, type: ResolvedType) {
        this.storage = storage;
        this.type = type;
    }
}

class ResolvedEphemeralListType extends ResolvedAtomType {
    readonly types: ResolvedEphemeralListTypeEntry[];

    constructor(rstr: string, types: ResolvedEphemeralListTypeEntry[]) {
        super(rstr);
        this.types = types;
    }

    static create(entries: ResolvedEphemeralListTypeEntry[]): ResolvedEphemeralListType {
        const simplifiedEntries = [...entries];
        const cvalue = simplifiedEntries.map((entry) => formatStorageInfo(entry.storage) + entry.type.idStr).join(", ");
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

    isEmptyType(): boolean {
        return this.options.length === 0;
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

    isEphemeralListType(): boolean {
        return this.options.length === 1 && this.options[0] instanceof ResolvedEphemeralListType;
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType | ResolvedFunctionType;
    readonly isRef: boolean;
    readonly storage: StorageDeclarator;
    readonly isOptional: boolean;

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, isOpt: boolean, isRef: boolean, storage: StorageDeclarator) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.isRef = isRef;
        this.storage = storage;
    }
}

class ResolvedFunctionType {
    readonly idStr: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultInfo: [ResolvedType, StorageDeclarator][];

    readonly allParamNames: Set<string>;

    constructor(rstr: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultInfo: [ResolvedType, StorageDeclarator][]) {
        this.idStr = rstr;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultInfo = resultInfo;

        this.allParamNames = new Set<string>();
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultInfo: [ResolvedType, StorageDeclarator][]): ResolvedFunctionType {
        const cvalues = params.map((param) => (param.isRef ? "ref " : "") + formatStorageInfo(param.storage) + param.name + (param.isOptional ? "?: " : ": ") + param.type.idStr);
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

        let rformat = resultInfo.length === 1 ? (formatStorageInfo(resultInfo[0][1]) + resultInfo[0][0].idStr) : ("(|" + resultInfo.map((ri) => formatStorageInfo(ri[1]) + ri[0].idStr).join(", ") + "|)");
        return new ResolvedFunctionType(recstr + "(" + cvalue + ") -> " + rformat, recursive, params, optRestParamName, optRestParamType, resultInfo);
    }
}

export { 
    ResolvedAtomType, 
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, 
    ResolvedTupleAtomTypeEntry, ResolvedTupleAtomType, 
    ResolvedRecordAtomTypeEntry, ResolvedRecordAtomType, 
    ResolvedEphemeralListTypeEntry, ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType
};
