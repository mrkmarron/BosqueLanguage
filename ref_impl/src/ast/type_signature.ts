//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

class StorageDeclarator {
    isValue: boolean;
    isUnique: boolean;
    isBorrow: boolean;

    constructor(isValue: boolean, isUnique: boolean, isBorrow: boolean) {
        this.isValue = isValue;
        this.isUnique = isUnique;
        this.isBorrow = isBorrow;
    }

    static createSimple(): StorageDeclarator {
        return new StorageDeclarator(false, false, false);
    }

    static createInvlaid(): StorageDeclarator {
        return new StorageDeclarator(true, true, true);
    }

    isSimpleStorage(): boolean {
        return !(this.isValue || this.isUnique || this.isBorrow);
    }

    isInvalidStorage(): boolean {
        return (this.isValue && this.isUnique && this.isBorrow);
    }

    static checkDeclsMatch(d1: StorageDeclarator, d2: StorageDeclarator): boolean {
        return (d1.isValue === d2.isValue) && (d1.isBorrow === d2.isBorrow) && (d1.isUnique === d2.isUnique);
    }

    static allDeclsMatch(...decls: StorageDeclarator[]): boolean {
        if(decls.length === 0) {
            return false;
        }
        else {
            const ddcl = decls[0];
            for(let i = 1; i < decls.length; ++i) {
                if(!StorageDeclarator.checkDeclsMatch(ddcl, decls[i])) {
                    return false;
                }
            }
            return true;
        }
    }
}

class TypeSignature {
}

class ParseErrorTypeSignature extends TypeSignature {
}

class AutoTypeSignature extends TypeSignature {
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(name: string) {
        super();
        this.name = name;
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly nameSpace: string;
    readonly baseName: string;
    readonly terms: TypeSignature[];

    constructor(ns: string, base: string, terms?: TypeSignature[]) {
        super();
        this.nameSpace = ns;
        this.baseName = base;
        this.terms = terms || [];
    }
}

class TupleTypeSignature extends TypeSignature {
    readonly entries: [TypeSignature, boolean][];

    constructor(entries: [TypeSignature, boolean][]) {
        super();
        this.entries = entries;
    }
}

class RecordTypeSignature extends TypeSignature {
   readonly entries: [string, TypeSignature, boolean][];

    constructor(entries: [string, TypeSignature, boolean][]) {
        super();
        this.entries = entries;
    }
}

class FunctionParameter {
    readonly name: string;
    readonly type: TypeSignature;
    readonly isRef: boolean;
    readonly storage: StorageDeclarator; 
    readonly isOptional: boolean;

    constructor(name: string, type: TypeSignature, isOpt: boolean, isRef: boolean, storage: StorageDeclarator) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.isRef = isRef;
        this.storage = storage;
    }
}

class FunctionTypeSignature extends TypeSignature {
    readonly recursive: "yes" | "no" | "cond";
    readonly params: FunctionParameter[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: TypeSignature | undefined;
    readonly resultInfo: [TypeSignature, StorageDeclarator][];

    constructor(recursive: "yes" | "no" | "cond", params: FunctionParameter[], optRestParamName: string | undefined, optRestParamType: TypeSignature | undefined, resultInfo: [TypeSignature, StorageDeclarator][]) {
        super();
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultInfo = resultInfo;
    }
}

class ProjectTypeSignature extends TypeSignature {
    readonly fromtype: TypeSignature;
    readonly oftype: TypeSignature;

    constructor(fromtype: TypeSignature, oftype: TypeSignature) {
        super();
        this.fromtype = fromtype;
        this.oftype = oftype;
    }
}

class IntersectionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }
}

export { 
    StorageDeclarator, TypeSignature, ParseErrorTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, 
    FunctionParameter, FunctionTypeSignature, ProjectTypeSignature, IntersectionTypeSignature, UnionTypeSignature
};
