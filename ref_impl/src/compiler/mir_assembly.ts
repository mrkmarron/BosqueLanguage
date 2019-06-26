//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo } from "../ast/parser";
import { MIRBody, MIRResolvedTypeKey, MIRTypeKey, MIRConstantKey, MIRFieldKey, MIRInvokeKey, MIRVirtualMethodKey } from "./mir_ops";

class MIRFunctionParameter {
    readonly name: string;
    readonly type: MIRType;

    constructor(name: string, type: MIRType) {
        this.name = name;
        this.type = type;
    }
}

class MIRConstantDecl {
    readonly key: MIRConstantKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly declaredType: MIRType;
    readonly value: MIRBody;

    constructor(key: MIRConstantKey, sinfo: SourceInfo, srcFile: string, declaredType: MIRType, value: MIRBody) {
        this.key = key;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.declaredType = declaredType;
        this.value = value;
    }
}

class MIRInvokeDecl {
    readonly iname: string;
    readonly key: MIRInvokeKey;

    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly params: MIRFunctionParameter[];
    readonly resultType: MIRType;

    readonly preconditions: MIRBody[];
    readonly postconditions: MIRBody[];

    readonly body: MIRBody;

    constructor(iname: string, key: MIRInvokeKey, sinfo: SourceInfo, srcFile: string, params: MIRFunctionParameter[], resultType: MIRType, preconds: MIRBody[], postconds: MIRBody[], body: MIRBody) {
        this.iname = iname;
        this.key = key;
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.params = params;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.body = body;
    }
}

abstract class MIROOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly enclosingType: MIRTypeKey;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, enclosingType: MIRTypeKey) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.enclosingType = enclosingType;
    }
}

class MIRFieldDecl extends MIROOMemberDecl {
    readonly fkey: MIRFieldKey;
    readonly declaredType: MIRType;
    readonly value: MIRBody | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, fkey: MIRFieldKey, attributes: string[], name: string, enclosingType: MIRTypeKey, dtype: MIRType, value: MIRBody | undefined) {
        super(srcInfo, srcFile, attributes, name, enclosingType);

        this.fkey = fkey;
        this.declaredType = dtype;
        this.value = value;
    }
}

class MIRMethodDecl extends MIROOMemberDecl {
    readonly vkey: MIRVirtualMethodKey;
    readonly invoke: MIRInvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, vkey: MIRVirtualMethodKey, attributes: string[], name: string, enclosingType: MIRTypeKey, invoke: MIRInvokeDecl) {
        super(sinfo, srcFile, attributes, name, enclosingType);

        this.vkey = vkey;
        this.invoke = invoke;
    }
}

class MIROOTypeDecl {
    readonly tkey: MIRTypeKey;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: Map<string, MIRType>;

    readonly provides: MIRTypeKey[];

    readonly isCollectionEntityType: boolean;
    readonly isMapEntityType: boolean;
    readonly declaredInvariants: MIRBody[];

    readonly memberMethods: MIRMethodDecl[] = [];
    readonly memberFields: MIRFieldDecl[];

    readonly invariants: MIRBody[] = [];
    readonly fieldMap: Map<string, MIRFieldDecl> = new Map<string, MIRFieldDecl>();
    readonly fieldLayout: string[] = [];
    readonly vcallMap: Map<MIRVirtualMethodKey, MIRMethodDecl> = new Map<string, MIRMethodDecl>();

    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[]) {
        this.tkey = tkey;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.isCollectionEntityType = isCollectionEntityType;
        this.isMapEntityType = isMapEntityType;
        this.declaredInvariants = declaredInvariants;
        this.memberFields = declaredFields;
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class MIRConceptTypeDecl extends MIROOTypeDecl {
    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[]) {
        super(tkey, srcFile, attributes, ns, name, terms, provides, isCollectionEntityType, isMapEntityType, declaredInvariants, declaredFields);
    }
}

class MIREntityTypeDecl extends MIROOTypeDecl {
    readonly isEnum: boolean;
    readonly isKey: boolean;

    constructor(tkey: MIRTypeKey, srcFile: string, attributes: string[], ns: string, name: string, terms: Map<string, MIRType>, provides: MIRTypeKey[], isCollectionEntityType: boolean, isMapEntityType: boolean, declaredInvariants: MIRBody[], declaredFields: MIRFieldDecl[], isEnum: boolean, isKey: boolean) {
        super(tkey, srcFile, attributes, ns, name, terms, provides, isCollectionEntityType, isMapEntityType, declaredInvariants, declaredFields);

        this.isEnum = isEnum;
        this.isKey = isKey;
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
    readonly ekey: MIRTypeKey;

    private constructor(ekey: MIRTypeKey) {
        super(ekey);
        this.ekey = ekey;
    }

    static create(ekey: MIRTypeKey): MIREntityType {
        return new MIREntityType(ekey);
    }
}

class MIRConceptType extends MIRNominalType {
    readonly ckeys: MIRTypeKey[];

    private constructor(trkey: MIRResolvedTypeKey, ckeys: MIRTypeKey[]) {
        super(trkey);
        this.ckeys = ckeys;
    }

    static create(ckeys: MIRTypeKey[]): MIRConceptType {
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
        const ropts = [...options].sort((a, b) => a.trkey.localeCompare(b.trkey));
        const trkey = ropts.map((opt) => opt.trkey).join(" | ");
        return new MIRType(trkey, ropts);
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
    readonly invokeDecls: Map<MIRInvokeKey, MIRInvokeDecl> = new Map<MIRInvokeKey, MIRInvokeDecl>();

    readonly memberFields: Map<MIRFieldKey, MIRFieldDecl> = new Map<MIRFieldKey, MIRFieldDecl>();

    readonly conceptMap: Map<MIRTypeKey, MIRConceptTypeDecl> = new Map<MIRTypeKey, MIRConceptTypeDecl>();
    readonly entityMap: Map<MIRTypeKey, MIREntityTypeDecl> = new Map<MIRTypeKey, MIREntityTypeDecl>();

    readonly typeMap: Map<MIRResolvedTypeKey, MIRType> = new Map<MIRResolvedTypeKey, MIRType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private atomSubtypeOf_EntityEntity(t1: MIREntityType, t2: MIREntityType): boolean {
        const t1e = this.entityMap.get(t1.ekey) as MIREntityTypeDecl;
        const t2e = this.entityMap.get(t2.ekey) as MIREntityTypeDecl;
        if (t1e.ns !== t2e.ns || t1e.name !== t2e.name) {
            return false;
        }

        let allBindsOk = true;
        t1e.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, t2e.terms.get(k) as MIRType); });
        return allBindsOk;
    }

    private atomSubtypeOf_EntityConcept(t1: MIREntityType, t2: MIRConceptType): boolean {
        const t1e = this.entityMap.get(t1.ekey) as MIREntityTypeDecl;
        const t2type = MIRType.createSingle(t2);
        return t1e.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, t2type));
    }

    private atomSubtypeOf_ConceptConcept(t1: MIRConceptType, t2: MIRConceptType): boolean {
        return t1.ckeys.every((c1t) => {
            return t2.ckeys.some((c2t) => {
                const c1 = this.conceptMap.get(c1t) as MIRConceptTypeDecl;
                const c2 = this.conceptMap.get(c2t) as MIRConceptTypeDecl;

                if (c1.ns === c2.ns && c1.name === c2.name) {
                    let allBindsOk = true;
                    c1.terms.forEach((v, k) => { allBindsOk = allBindsOk && this.subtypeOf(v, c2.terms.get(k) as MIRType); });
                    return allBindsOk;
                }

                const t2type = MIRType.createSingle(MIRConceptType.create([c2t]));
                return c1.provides.some((provide) => this.subtypeOf(this.typeMap.get(provide) as MIRType, t2type));
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
        else if (t1 instanceof MIRConceptType && t2 instanceof MIRConceptType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t1 instanceof MIRConceptType) {
            //res stays false
        }
        else if (t2 instanceof MIRConceptType) {
            if (t1 instanceof MIREntityType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2 as MIRConceptType);
            }
            else if (t1 instanceof MIRTupleType) {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Tuple"]), t2 as MIRConceptType);
            }
            else if (t1 instanceof MIRRecordType) {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Record"]), t2 as MIRConceptType);
            }
            else {
                res = this.atomSubtypeOf_ConceptConcept(MIRConceptType.create(["NSCore::Function"]), t2 as MIRConceptType);
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
            else if (t1 instanceof MIRFunctionType && t2 instanceof MIRFunctionType) {
                res = this.atomSubtypeOf_FunctionFunction(t1, t2);
            }
            else {
                //fall-through
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

    closeConceptDecl(cpt: MIRConceptTypeDecl) {
        cpt.provides.forEach((tkey) => {
            const ccdecl = this.conceptMap.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.invariants.forEach((inv) => cpt.invariants.push(inv));
            ccdecl.fieldMap.forEach((fd, name) => cpt.fieldMap.set(name, fd));
            ccdecl.vcallMap.forEach((vcall, vcname) => cpt.vcallMap.set(vcname, vcall));
        });

        cpt.memberFields.forEach((fd) => {
            if (fd.attributes.indexOf("abstract") === -1) {
                cpt.fieldMap.set(fd.name, fd);
            }
        });

        cpt.memberMethods.forEach((vm) => {
            if (vm.attributes.indexOf("abstract") === -1) {
                cpt.vcallMap.set(vm.vkey, vm);
            }
        });
    }

    closeEntityDecl(entity: MIREntityTypeDecl) {
        entity.provides.forEach((tkey) => {
            const ccdecl = this.conceptMap.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.invariants.forEach((inv) => entity.invariants.push(inv));
            ccdecl.fieldMap.forEach((fd, name) => entity.fieldMap.set(name, fd));
            ccdecl.vcallMap.forEach((vcall, vcname) => entity.vcallMap.set(vcname, vcall));
        });

        entity.memberFields.forEach((fd) => {
            entity.fieldMap.set(fd.name, fd);
        });

        entity.memberMethods.forEach((vm) => {
            entity.vcallMap.set(vm.vkey, vm);
        });

        entity.fieldMap.forEach((v, f) => entity.fieldLayout.push(f));
        entity.fieldLayout.sort();
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

        const res = t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.trkey, res);
        return res;
    }
}

export {
    MIRConstantDecl, MIRFunctionParameter, MIRInvokeDecl,
    MIROOMemberDecl, MIRConstDecl, MIRStaticDecl, MIRFieldDecl, MIRMethodDecl,
    MIROOTypeDecl, MIRConceptTypeDecl, MIREntityTypeDecl,
    MIRType, MIRTypeOption, MIRNominalType, MIREntityType, MIRConceptType,
    MIRStructuralType, MIRTupleTypeEntry, MIRTupleType, MIRRecordTypeEntry, MIRRecordType,
    PackageConfig, MIRAssembly
};
