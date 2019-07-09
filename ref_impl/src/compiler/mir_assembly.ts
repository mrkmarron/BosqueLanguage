//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { MIRBody, MIRResolvedTypeKey, MIRConstantKey, MIRFieldKey, MIRInvokeKey, MIRVirtualMethodKey, MIRNominalTypeKey } from "./mir_ops";

class MIRFunctionParameter {
    readonly name: string;
    readonly type: MIRResolvedTypeKey;

    constructor(name: string, type: MIRResolvedTypeKey) {
        this.name = name;
        this.type = type;
    }
}

class MIRConstantDecl {
    readonly cname: string;
    readonly key: MIRConstantKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [MIRType, string][];

    readonly declaredType: MIRResolvedTypeKey;
    readonly value: MIRBody;

    constructor(cname: string, key: MIRConstantKey, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, declaredType: MIRResolvedTypeKey, value: MIRBody) {
        this.cname = cname;
        this.key = key;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;

        this.declaredType = declaredType;
        this.value = value;
    }
}

abstract class MIRInvokeDecl {
    readonly iname: string;
    readonly key: MIRInvokeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly recursive: boolean;
    readonly pragmas: [MIRType, string][];

    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRResolvedTypeKey;

    constructor(iname: string, key: MIRInvokeKey, recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey) {
        this.iname = iname;
        this.key = key;

        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.recursive = recursive;
        this.pragmas = pragmas;

        this.params = params;
        this.resultType = resultType;
    }
}

class MIRInvokeBodyDecl extends MIRInvokeDecl {
    readonly preconditions: MIRBody[];
    readonly postconditions: MIRBody[];

    readonly body: MIRBody;

    constructor(iname: string, key: MIRInvokeKey, recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, preconds: MIRBody[], postconds: MIRBody[], body: MIRBody) {
        super(iname, key, recursive, pragmas, sinfo, srcFile, params, resultType);

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.body = body;
    }
}

type MIRPCode = {
    code: MIRInvokeKey,
    cargs: string[]
};

class MIRInvokePrimitiveDecl extends MIRInvokeDecl {
    readonly implkey: string;
    readonly binds: Map<string, MIRResolvedTypeKey>;
    readonly pcodes: Map<string, MIRPCode>;

    constructor(iname: string, key: MIRInvokeKey, recursive: boolean, pragmas: [MIRType, string][], sinfo: SourceInfo, srcFile: string, binds: Map<string, MIRResolvedTypeKey>,  params: MIRFunctionParameter[], resultType: MIRResolvedTypeKey, implkey: string, pcodes: Map<string, MIRPCode>) {
        super(iname, key, recursive, pragmas, sinfo, srcFile, params, resultType);

        this.implkey = implkey;
        this.binds = binds;
        this.pcodes = pcodes;
    }
}

class MIRFieldDecl {
    readonly fname: string;
    readonly fkey: MIRFieldKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [MIRType, string][];

    readonly name: string;

    readonly declaredType: MIRResolvedTypeKey;
    readonly value: MIRBody | undefined;

    constructor(fname: string, srcInfo: SourceInfo, srcFile: string, fkey: MIRFieldKey, pragmas: [MIRType, string][], name: string, dtype: MIRResolvedTypeKey, value: MIRBody | undefined) {
        this.fname = fname;
        this.fkey = fkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;

        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }
}

class MIROOTypeDecl {
    readonly ooname: string;
    readonly tkey: MIRNominalTypeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [MIRType, string][];

    readonly ns: string;
    readonly name: string;
    readonly terms: Map<string, MIRType>;
    readonly provides: MIRType[];

    readonly invariants: MIRBody[] = [];
    readonly fields: MIRFieldDecl[] = [];
    readonly vcallMap: Map<MIRVirtualMethodKey, MIRInvokeKey> = new Map<string, MIRInvokeKey>();

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRType[], invariants: MIRBody[], fields: MIRFieldDecl[]) {
        this.ooname = ooname;
        this.tkey = tkey;

        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;

        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;

        this.invariants = invariants;
        this.fields = fields;
    }
}

class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRType[], invariants: MIRBody[], fields: MIRFieldDecl[]) {
        super(ooname, srcInfo, srcFile, tkey, pragmas, ns, name, terms, provides, invariants, fields);
    }
}

class MIREntityTypeDecl extends MIROOTypeDecl {
    readonly isEnum: boolean;
    readonly isKey: boolean;

    readonly isCollectionEntityType: boolean;
    readonly isMapEntityType: boolean;

    constructor(ooname: string, srcInfo: SourceInfo, srcFile: string, tkey: MIRNominalTypeKey, pragmas: [MIRType, string][], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRType[], invariants: MIRBody[], fields: MIRFieldDecl[], isCollectionEntityType: boolean, isMapEntityType: boolean, isEnum: boolean, isKey: boolean) {
        super(ooname, srcInfo, srcFile, tkey, pragmas, ns, name, terms, provides, invariants, fields);

        this.isEnum = isEnum;
        this.isKey = isKey;

        this.isCollectionEntityType = isCollectionEntityType;
        this.isMapEntityType = isMapEntityType;
    }
}

abstract class MIRTypeOption {
    readonly trkey: MIRResolvedTypeKey;

    constructor(trkey: MIRResolvedTypeKey) {
        this.trkey = trkey;
    }
}

abstract class MIRNominalType extends MIRTypeOption {
    constructor(trkey: MIRResolvedTypeKey) {
        super(trkey);
    }
}

class MIREntityType extends MIRNominalType {
    readonly ekey: MIRNominalTypeKey;

    private constructor(ekey: MIRNominalTypeKey) {
        super(ekey);
        this.ekey = ekey;
    }

    static create(ekey: MIRNominalTypeKey): MIREntityType {
        return new MIREntityType(ekey);
    }
}

class MIRConceptType extends MIRNominalType {
    readonly ckeys: MIRNominalTypeKey[];

    private constructor(trkey: MIRResolvedTypeKey, ckeys: MIRNominalTypeKey[]) {
        super(trkey);
        this.ckeys = ckeys;
    }

    static create(ckeys: MIRNominalTypeKey[]): MIRConceptType {
        const skeys = ckeys.sort();
        return new MIRConceptType(skeys.join(" & "), skeys);
    }
}

abstract class MIRStructuralType extends MIRTypeOption {
    constructor(trkey: MIRResolvedTypeKey) {
        super(trkey);
    }
}

class MIRTupleTypeEntry {
    readonly type: MIRType;
    readonly isOptional: boolean;

    constructor(type: MIRType, isOpt: boolean) {
        this.isOptional = isOpt;
        this.type = type;
    }
}

class MIRTupleType extends MIRStructuralType {
    readonly entries: MIRTupleTypeEntry[];
    readonly isOpen: boolean;

    private constructor(trkey: MIRResolvedTypeKey, entries: MIRTupleTypeEntry[], isOpen: boolean) {
        super(trkey);
        this.entries = entries;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: MIRTupleTypeEntry[]): MIRTupleType {
        let cvalue = entries.map((entry) => (entry.isOptional ? "?:" : "") + entry.type.trkey).join(", ");
        if (isOpen) {
            cvalue += (entries.length !== 0 ? ", " : "") + "...";
        }

        return new MIRTupleType("[" + cvalue + "]", [...entries], isOpen);
    }
}

class MIRRecordTypeEntry {
    readonly name: string;
    readonly type: MIRType;
    readonly isOptional: boolean;

    constructor(name: string, type: MIRType, isOpt: boolean) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
    }
}

class MIRRecordType extends MIRStructuralType {
    readonly entries: MIRRecordTypeEntry[];
    readonly isOpen: boolean;

    constructor(rstr: string, entries: MIRRecordTypeEntry[], isOpen: boolean) {
        super(rstr);
        this.entries = entries;
        this.isOpen = isOpen;
    }

    static create(isOpen: boolean, entries: MIRRecordTypeEntry[]): MIRRecordType {
        const rentries = [...entries].sort((a, b) => a.name.localeCompare(b.name));

        let cvalue = rentries.map((entry) => entry.name + (entry.isOptional ? "?:" : ":") + entry.type.trkey).join(", ");
        if (isOpen) {
            cvalue += (rentries.length !== 0 ? ", " : "") + "...";
        }

        return new MIRRecordType("{" + cvalue + "}", rentries, isOpen);
    }
}

class MIRType {
    readonly trkey: MIRResolvedTypeKey;
    readonly options: MIRTypeOption[];

    private constructor(trkey: MIRResolvedTypeKey, options: MIRTypeOption[]) {
        this.trkey = trkey;
        this.options = options;
    }

    static createSingle(option: MIRTypeOption): MIRType {
        return new MIRType(option.trkey, [option]);
    }

    static create(options: MIRTypeOption[]): MIRType {
        const trkey = [...options].sort().map((tk) => tk.trkey).join(" | ");
        return new MIRType(trkey, options);
    }
}

class PackageConfig {
    //TODO: package.config data
}

class MIRAssembly {
    readonly package: PackageConfig;
    readonly srcFiles: { relativePath: string, contents: string }[];
    readonly srcHash: string;

    readonly constantDecls: Map<MIRConstantKey, MIRConstantDecl> = new Map<MIRConstantKey, MIRConstantDecl>();
    readonly fieldDecls: Map<MIRFieldKey, MIRFieldDecl> = new Map<MIRFieldKey, MIRFieldDecl>();

    readonly entryPoints: MIRInvokeKey[] = [];
    readonly invokeDecls: Map<MIRInvokeKey, MIRInvokeBodyDecl> = new Map<MIRInvokeKey, MIRInvokeBodyDecl>();
    readonly primitiveInvokeDecls: Map<MIRInvokeKey, MIRInvokePrimitiveDecl> = new Map<MIRInvokeKey, MIRInvokePrimitiveDecl>();

    readonly conceptDecls: Map<MIRNominalTypeKey, MIRConceptTypeDecl> = new Map<MIRNominalTypeKey, MIRConceptTypeDecl>();
    readonly entityDecls: Map<MIRNominalTypeKey, MIREntityTypeDecl> = new Map<MIRNominalTypeKey, MIREntityTypeDecl>();

    readonly typeMap: Map<MIRResolvedTypeKey, MIRType> = new Map<MIRResolvedTypeKey, MIRType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private atomSubtypeOf_EntityEntity(t1: MIREntityType, t2: MIREntityType): boolean {
        const t1e = this.entityDecls.get(t1.ekey) as MIREntityTypeDecl;
        const t2e = this.entityDecls.get(t2.ekey) as MIREntityTypeDecl;
        if (t1e.ns !== t2e.ns || t1e.name !== t2e.name) {
            return false;
        }

        let allBindsOk = true;
        t1e.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, t2e.terms.get(k) as MIRType); });
        return allBindsOk;
    }

    private atomSubtypeOf_EntityConcept(t1: MIREntityType, t2: MIRConceptType): boolean {
        const t1e = this.entityDecls.get(t1.ekey) as MIREntityTypeDecl;
        const mcc = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(provide, mcc));
    }

    private atomSubtypeOf_ConceptConcept(t1: MIRConceptType, t2: MIRConceptType): boolean {
        return t1.ckeys.every((c1t) => {
            return t2.ckeys.some((c2t) => {
                const c1 = this.conceptDecls.get(c1t) as MIRConceptTypeDecl;
                const c2 = this.conceptDecls.get(c2t) as MIRConceptTypeDecl;

                if (c1.ns === c2.ns && c1.name === c2.name) {
                    let allBindsOk = true;
                    c1.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, c2.terms.get(k) as MIRType); });
                    return allBindsOk;
                }

                return c1.provides.some((provide) => this.subtypeOf(provide, this.typeMap.get(c2t) as MIRType));
            });
        });
    }

    private atomSubtypeOf_TupleTuple(t1: MIRTupleType, t2: MIRTupleType): boolean {
        //Then this is definitely not ok
        if (t1.isOpen && !t2.isOpen) {
            return false;
        }

        for (let i = 0; i < t1.entries.length; ++i) {
            const t1e = t1.entries[i];

            if (i >= t2.entries.length) {
                if (!t2.isOpen) {
                    return false;
                }
            }
            else {
                const t2e = t2.entries[i];
                if ((t1e.isOptional && !t2e.isOptional) || !this.subtypeOf(t1e.type, t2e.type)) {
                    return false;
                }
            }
        }

        //t2 has a required entry that is not required in t1
        if (t2.entries.length > t1.entries.length && t2.entries.slice(t1.entries.length).some((entry) => !entry.isOptional)) {
            return false;
        }

        return true;
    }

    private atomSubtypeOf_RecordRecord(t1: MIRRecordType, t2: MIRRecordType): boolean {
        //Then this is definitely not ok
        if (t1.isOpen && !t2.isOpen) {
            return false;
        }

        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                if (!t2.isOpen) {
                    badEntry = badEntry || true;
                }
            }
            else {
                if ((entry.isOptional && !t2e.isOptional) || !this.subtypeOf(entry.type, t2e.type)) {
                    badEntry = badEntry || true;
                }
            }
        });

        t2.entries.forEach((entry) => {
            badEntry = badEntry || (t1.entries.find((e) => e.name === entry.name) === undefined && !entry.isOptional);
        });

        if (badEntry) {
            return false;
        }

        return true;
    }

    private atomSubtypeOf(t1: MIRTypeOption, t2: MIRTypeOption): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.trkey, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.trkey) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.trkey === t2.trkey) {
            res = true;
        }
        else {
            if (t1 instanceof MIRConceptType && t2 instanceof MIRConceptType) {
                res = this.atomSubtypeOf_ConceptConcept(t1, t2);
            }
            else if (t1 instanceof MIRConceptType) {
                //res stays false
            }
            else if (t2 instanceof MIRConceptType) {
                if (t1 instanceof MIREntityType) {
                    res = this.atomSubtypeOf_EntityConcept(t1, t2);
                }
                else if (t1 instanceof MIRTupleType) {
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Tuple"]), t2);
                }
                else if (t1 instanceof MIRRecordType) {
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Record"]), t2);
                }
                else {
                    res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Function"]), t2);
                }
            }
            else {
                if (t1 instanceof MIREntityType && t2 instanceof MIREntityType) {
                    res = this.atomSubtypeOf_EntityEntity(t1, t2);
                }
                else if (t1 instanceof MIRTupleType && t2 instanceof MIRTupleType) {
                    res = this.atomSubtypeOf_TupleTuple(t1, t2);
                }
                else if (t1 instanceof MIRRecordType && t2 instanceof MIRRecordType) {
                    res = this.atomSubtypeOf_RecordRecord(t1, t2);
                }
                else {
                    //fall-through
                }
            }
        }

        memores.set(t2.trkey, res);
        return res;
    }

    constructor(pckge: PackageConfig, srcFiles: { relativePath: string, contents: string }[], srcHash: string) {
        this.package = pckge;
        this.srcFiles = srcFiles;
        this.srcHash = srcHash;
    }

    subtypeOf(t1: MIRType, t2: MIRType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.trkey);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.trkey, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.trkey) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.trkey);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = (t1.trkey === t2.trkey) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.trkey, res);
        return res;
    }
}

export {
    MIRConstantDecl, MIRFunctionParameter, MIRInvokeDecl, MIRInvokeBodyDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRFieldDecl,
    MIROOTypeDecl, MIRConceptTypeDecl, MIREntityTypeDecl,
    MIRType, MIRTypeOption, MIRNominalType, MIREntityType, MIRConceptType,
    MIRStructuralType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType,
    PackageConfig, MIRAssembly
};
