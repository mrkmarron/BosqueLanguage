//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ConceptTypeDecl, EntityTypeDecl } from "./assembly";

class ResolvedAtomType {
    readonly idStr: string;

    constructor(rstr: string) {
        this.idStr = rstr;
    }
}

class ResolvedWildcardAtomType extends ResolvedAtomType {
    constructor() {
        super("*");
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
    readonly oftype: ResolvedType;
    readonly typevalue: boolean | number | {enumtype: ResolvedType, enumvalue: string};

    constructor(rstr: string, oftype: ResolvedType, ofvalue: boolean | number | {enumtype: ResolvedType, enumvalue: string}) {
        super(rstr);
        this.oftype = oftype;
        this.typevalue = ofvalue;
    }

    static create(oftype: ResolvedType, ofvalue: boolean | number | {enumtype: ResolvedType, enumvalue: string}): ResolvedLiteralAtomType {
        let rstr = "";
        if(typeof(ofvalue) === "boolean" || typeof(ofvalue) === "number") {
            rstr = `${ofvalue}`;
        }
        else {
            rstr = `${ofvalue.enumtype.idStr}::${ofvalue.enumvalue}`
        }
        
        return new ResolvedLiteralAtomType(rstr, oftype, ofvalue);
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
    readonly grounded: boolean;
    readonly types: ResolvedTupleAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, grounded: boolean, types: ResolvedTupleAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.grounded = grounded;
        this.types = types;
    }

    static create(isvalue: boolean, entries: ResolvedTupleAtomTypeEntry[]): ResolvedTupleAtomType {
        const cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.idStr).join(", ");
        const grounded = entries.every((entry) => entry.type.isGroundedType());

        return new ResolvedTupleAtomType((isvalue ? "#[" : "@[") + cvalue + "]", isvalue, grounded, entries);
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
    readonly grounded: boolean;
    readonly entries: ResolvedRecordAtomTypeEntry[];

    constructor(rstr: string, isvalue: boolean, grounded: boolean, entries: ResolvedRecordAtomTypeEntry[]) {
        super(rstr);
        this.isvalue = isvalue;
        this.grounded = grounded;
        this.entries = entries;
    }

    static create(isvalue: boolean, entries: ResolvedRecordAtomTypeEntry[]): ResolvedRecordAtomType {
        let simplifiedEntries: ResolvedRecordAtomTypeEntry[] = [...entries];
        simplifiedEntries.sort((a, b) => a.name.localeCompare(b.name));
        const cvalue = simplifiedEntries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.idStr).join(", ");
        const grounded = entries.every((entry) => entry.type.isGroundedType());

        return new ResolvedRecordAtomType((isvalue ? "#{" : "@{") + cvalue + "}", isvalue, grounded, simplifiedEntries);
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

        return (this.options[0] instanceof ResolvedTupleAtomType) && (this.options[0] as ResolvedTupleAtomType).types.some((value) => value.isOptional);
    }

    tryGetInferrableTupleConstructorType(isvalue: boolean): ResolvedTupleAtomType | undefined {
        const tcopts = this.options.filter((opt) => opt instanceof ResolvedTupleAtomType);

        if (tcopts.length !== 1) {
            return undefined;
        }

        const tt = tcopts[0] as ResolvedTupleAtomType;
        return (tt.isvalue === isvalue) ? tt : undefined;
    }

    isUniqueRecordTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return (this.options[0] instanceof ResolvedRecordAtomType) && !(this.options[0] as ResolvedRecordAtomType).entries.some((value) => value.isOptional);
    }

    tryGetInferrableRecordConstructorType(isvalue: boolean): ResolvedRecordAtomType | undefined {
        const rcopts = this.options.filter((opt) => opt instanceof ResolvedRecordAtomType);

        if (rcopts.length !== 1) {
            return undefined;
        }

        const tr = rcopts[0] as ResolvedRecordAtomType;
        return (tr.isvalue === isvalue) ? tr : undefined;
    }

    isUniqueCallTargetType(): boolean {
        if (this.options.length !== 1) {
            return false;
        }

        return this.options[0] instanceof ResolvedEntityAtomType;
    }

    tryGetInferrableValueListConstructorType(): ResolvedEphemeralListType | undefined {
        const vlopts = this.options.filter((opt) => opt instanceof ResolvedRecordAtomType);

        if (vlopts.length !== 1) {
            return undefined;
        }

        return (vlopts[0] as ResolvedEphemeralListType);
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

    isSameType(otype: ResolvedType): boolean {
        return this.idStr === otype.idStr;
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
                return opt.grounded;
            }
            else if(opt instanceof ResolvedRecordAtomType) {
                return opt.grounded;
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

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, isOpt: boolean, isRef: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
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
    ResolvedWildcardAtomType,
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, 
    ResolvedLiteralAtomType,
    ResolvedTupleAtomTypeEntry, ResolvedTupleAtomType, 
    ResolvedRecordAtomTypeEntry, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType
};
