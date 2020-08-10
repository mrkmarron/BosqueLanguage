//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomTypeEntry, ResolvedAtomType, ResolvedFunctionTypeParam, ResolvedFunctionType, ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedWildcardAtomType, ResolvedLiteralAtomType } from "./resolved_type";
import { TemplateTypeSignature, NominalTypeSignature, TypeSignature, TupleTypeSignature, RecordTypeSignature, FunctionTypeSignature, UnionTypeSignature, ParseErrorTypeSignature, AutoTypeSignature, FunctionParameter, ProjectTypeSignature, EphemeralListTypeSignature, LiteralTypeSignature, PlusTypeSignature, AndTypeSignature } from "./type_signature";
import { Expression, BodyImplementation } from "./body";
import { SourceInfo } from "./parser";

import * as assert from "assert";
import { type } from "os";
import { BSQRegex } from "./bsqregex";

type BuildLevel = "debug" | "test" | "release";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(enabled === "debug") {
        return true;
    }
    else if(enabled === "test") {
        return check === "test" || check === "release";
    }
    else {
        return check === "release";
    }
}

class TemplateTermDecl {
    readonly name: string;
    readonly constraint: TypeSignature;
    readonly isInfer: boolean;
    readonly defaultType: TypeSignature | undefined;
    readonly isLiteral: boolean;

    constructor(name: string, constraint: TypeSignature, isinfer: boolean, defaulttype: TypeSignature | undefined, isliteral: boolean) {
        this.name = name;
        this.constraint = constraint;
        this.isInfer = isinfer;
        this.defaultType = defaulttype;
        this.isLiteral = isliteral;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly constraint: TypeSignature;

    constructor(t: TypeSignature, constraint: TypeSignature) {
        this.t = t;
        this.constraint = constraint;
    }
}

class TypeConditionRestriction {
    readonly constraints: TemplateTypeRestriction[];

    constructor(constraints: TemplateTypeRestriction[]) {
        this.constraints = constraints;
    }
}

class PreConditionDecl {
    readonly sinfo: SourceInfo;
    readonly isvalidate: boolean;
    readonly level: BuildLevel;
    readonly exp: Expression;
    readonly err: Expression | undefined;

    constructor(sinfo: SourceInfo, isvalidate: boolean, level: BuildLevel, exp: Expression, err: Expression | undefined) {
        this.sinfo = sinfo;
        this.isvalidate = isvalidate;
        this.level = level;
        this.exp = exp;
        this.err = err;
    }
}

class PostConditionDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: Expression) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }
}

class InvariantDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: Expression) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }
}

class InvokeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly recursive: "yes" | "no" | "cond";
    readonly pragmas: [TypeSignature, string][];

    readonly terms: TemplateTermDecl[];
    readonly termRestrictions: TypeConditionRestriction | undefined;

    readonly params: FunctionParameter[];
    readonly optRestName: string | undefined;
    readonly optRestType: TypeSignature | undefined;

    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly isLambda: boolean;
    readonly captureSet: Set<string>;
    readonly body: BodyImplementation | undefined;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", pragmas: [TypeSignature, string][], terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], isLambda: boolean, captureSet: Set<string>, body: BodyImplementation | undefined) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.recursive = recursive;
        this.pragmas = pragmas;

        this.terms = terms;
        this.termRestrictions = termRestrictions;

        this.params = params;
        this.optRestName = optRestName;
        this.optRestType = optRestType;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;

        this.isLambda = isLambda;
        this.captureSet = captureSet;
        this.body = body;
    }

    generateSig(): TypeSignature {
        return new FunctionTypeSignature(this.recursive, [...this.params], this.optRestName, this.optRestType, this.resultType);
    }

    static createPCodeInvokeDecl(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, captureSet: Set<string>, body: BodyImplementation) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, [], [], undefined, params, optRestName, optRestType, resultInfo, [], [], true, captureSet, body);
    }

    static createStaticInvokeDecl(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", pragmas: [TypeSignature, string][], terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], body: BodyImplementation | undefined) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultInfo, preconds, postconds, false, new Set<string>(), body);
    }

    static createMemberInvokeDecl(sinfo: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", pragmas: [TypeSignature, string][], terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], optRestName: string | undefined, optRestType: TypeSignature | undefined, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], body: BodyImplementation | undefined) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultInfo, preconds, postconds, false, new Set<string>(), body);
    }
}

interface OOMemberDecl {
    getName(): string;
}

class StaticMemberDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [TypeSignature, string][];
    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], name: string, dtype: TypeSignature, value: Expression | undefined) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    getName(): string {
        return this.name;
    }
}

class StaticFunctionDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;

        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class MemberFieldDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [TypeSignature, string][];
    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], name: string, dtype: TypeSignature, value: Expression | undefined) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    getName(): string {
        return this.name;
    }
}

class MemberMethodDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }
}

class OOPTypeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [TypeSignature, string][];
    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: TemplateTermDecl[];

    readonly provides: [TypeSignature, TypeConditionRestriction | undefined][];

    readonly invariants: InvariantDecl[];

    readonly staticMembers: Map<string, StaticMemberDecl>;
    readonly staticFunctions: Map<string, StaticFunctionDecl>;
    readonly memberFields: Map<string, MemberFieldDecl>;
    readonly memberMethods: Map<string, MemberMethodDecl>;

    constructor(sourceLocation: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
    }

    isTypeAnExpandoableCollection(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "List" || this.name === "Set" || this.name === "DynamicSet" || this.name === "Map" || this.name === "DynamicMap";
    }

    isTypeAListEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "List" || this.name === "Vector";
    }

    isTypeAQueueEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "Queue";
    }

    isTypeAStackEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "Stack";
    }

    isTypeASetEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "Set" || this.name === "DynamicSet";
    }

    isTypeAMapEntity(): boolean {
        if (this.ns !== "NSCore") {
            return false;
        }

        return this.name === "Map" || this.name === "DynamicMap";
    }

    static attributeSetContains(attr: string, attrSet: string[]): boolean {
        return attrSet.indexOf(attr) !== -1;
    }
}

class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        super(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[],
        staticMembers: Map<string, StaticMemberDecl>, staticFunctions: Map<string, StaticFunctionDecl>,
        memberFields: Map<string, MemberFieldDecl>, memberMethods: Map<string, MemberMethodDecl>) {
        super(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
    }
}

class NamespaceConstDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly pragmas: [TypeSignature, string][];
    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: Expression;

    constructor(srcInfo: SourceInfo, srcFile: string, pragmas: [TypeSignature, string][], attributes: string[], ns: string, name: string, dtype: TypeSignature, value: Expression) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.pragmas = pragmas;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.declaredType = dtype;
        this.value = value;
    }
}

class NamespaceFunctionDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;
    readonly attributes: string[];

    readonly ns: string;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceTypedef {
    readonly ns: string;
    readonly name: string;
    readonly terms: TemplateTermDecl[];
    readonly boundType: TypeSignature;

    constructor(ns: string, name: string, terms: TemplateTermDecl[], btype: TypeSignature) {
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.boundType = btype;
    }
}

class NamespaceUsing {
    readonly fromNamespace: string;
    readonly names: string[];

    constructor(from: string, names: string[]) {
        this.fromNamespace = from;
        this.names = names;
    }
}

class NamespaceDeclaration {
    readonly ns: string;

    usings: NamespaceUsing[];
    declaredNames: Set<string>;

    typeDefs: Map<string, NamespaceTypedef>;
    consts: Map<string, NamespaceConstDecl>;
    functions: Map<string, NamespaceFunctionDecl>;
    concepts: Map<string, ConceptTypeDecl>;
    objects: Map<string, EntityTypeDecl>;

    constructor(ns: string) {
        this.ns = ns;
        this.usings = [];
        this.declaredNames = new Set<string>();

        this.typeDefs = new Map<string, NamespaceTypedef>();
        this.consts = new Map<string, NamespaceConstDecl>();
        this.functions = new Map<string, NamespaceFunctionDecl>();
        this.concepts = new Map<string, ConceptTypeDecl>();
        this.objects = new Map<string, EntityTypeDecl>();
    }

    checkUsingNameClash(names: string[]): boolean {
        return names.some((name) => this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1));
    }

    checkDeclNameClash(ns: string, name: string): boolean {
        const rname = ns + "::" + name;
        return this.typeDefs.has(rname) || this.consts.has(rname) || this.functions.has(rname) || this.concepts.has(rname) || this.objects.has(rname) || this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1);
    }
}

class OOMemberLookupInfo {
    readonly contiainingType: OOPTypeDecl;
    readonly decl: OOMemberDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(contiainingType: OOPTypeDecl, decl: OOMemberDecl, binds: Map<string, ResolvedType>) {
        this.contiainingType = contiainingType;
        this.decl = decl;
        this.binds = binds;
    }
}

class Assembly {
    private m_specialTypeMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();
    private m_namespaceMap: Map<string, NamespaceDeclaration> = new Map<string, NamespaceDeclaration>();
    private m_conceptMap: Map<string, ConceptTypeDecl> = new Map<string, ConceptTypeDecl>();
    private m_objectMap: Map<string, EntityTypeDecl> = new Map<string, EntityTypeDecl>();

    private m_literalRegexs: Set<BSQRegex> = new Set<BSQRegex>();
    private m_validatorRegexs: Map<string, BSQRegex> = new Map<string, BSQRegex>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private resolveTemplateBinds(declterms: TemplateTermDecl[], giventerms: TypeSignature[], binds: Map<string, ResolvedType>): Map<string, ResolvedType> | undefined {
        const fullbinds = new Map<string, ResolvedType>();

        for (let i = 0; i < declterms.length; ++i) {
            if(giventerms.length <= i) {
                if(declterms[i].defaultType !== undefined) {
                    fullbinds.set(declterms[i].name, this.normalizeTypeOnly(declterms[i].defaultType as TypeSignature, new Map<string, ResolvedType>()));
                }
                else {
                    return undefined;
                }
            }
            else {
                fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], binds));
            }
        }

        return fullbinds;
    }

    private splitConceptTypes(ofc: ResolvedConceptAtomType, withc: ResolvedConceptAtomType): {tp: ResolvedConceptAtomType | undefined, fp: ResolvedConceptAtomType | undefined} {
        if(this.atomSubtypeOf(ofc, withc)) {
            return {tp: ofc, fp: undefined};
        }
        else {
            const itypes = [...ofc.conceptTypes, ...withc.conceptTypes].sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

            //do a simplification based on A & B when A \Subtypeeq B is A
            let simplifiedTypes: ResolvedConceptAtomTypeEntry[] = [];
            for (let i = 0; i < itypes.length; ++i) {
                let docopy = true;
                for (let j = 0; j < itypes.length; ++j) {
                    if (i === j) {
                        continue; //ignore check on same element
                    }

                    //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Tj
                    if (this.atomSubtypeOf(ResolvedConceptAtomType.create([itypes[j]]), ResolvedConceptAtomType.create([itypes[i]]))) {
                        docopy = (itypes[i].idStr === itypes[j].idStr) && i < j; //if same type only keep one copy
                        break;
                    }
                }

                if (docopy) {
                    simplifiedTypes.push(itypes[i]);
                }
            }

            const tpt = ResolvedConceptAtomType.create(simplifiedTypes);

            return { tp: tpt, fp: ofc };
        }
    }

    private splitEntityConceptTypes(ofe: ResolvedEntityAtomType, withc: ResolvedConceptAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(ofe, withc)) {
            return { tp: ofe, fp: undefined };
        }
        else {
            return { tp: undefined, fp: ofe };
        }
    }

    private splitTupleTypes(oft: ResolvedTupleAtomType, witht: ResolvedTupleAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(oft, witht)) {
            return { tp: oft, fp: undefined };
        }
        else {
            return { tp: witht, fp: oft };
        }
    }

    private splitTupleConcept(oft: ResolvedTupleAtomType, withc: ResolvedConceptAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(oft, withc)) {
            return { tp: oft, fp: undefined };
        }
        else {
            return { tp: withc, fp: oft };
        }
    }

    private splitRecordTypes(ofr: ResolvedRecordAtomType, withr: ResolvedRecordAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(ofr, withr)) {
            return { tp: ofr, fp: undefined };
        }
        else {
            return { tp: withr, fp: ofr };
        }
    }

    private splitRecordConcept(ofr: ResolvedRecordAtomType, withc: ResolvedConceptAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (this.atomSubtypeOf(ofr, withc)) {
            return { tp: ofr, fp: undefined };
        }
        else {
            return { tp: withc, fp: ofr };
        }
    }

    private splitAtomTypes(ofa: ResolvedAtomType, witha: ResolvedAtomType): { tp: ResolvedAtomType | undefined, fp: ResolvedAtomType | undefined } {
        if (ofa.idStr === witha.idStr) {
            return { tp: ofa, fp: undefined };
        }

        if (ofa instanceof ResolvedEntityAtomType) {
            if (witha instanceof ResolvedConceptAtomType) {
                return this.splitEntityConceptTypes(ofa, witha);
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else if(ofa instanceof ResolvedConceptAtomType) {
            if (witha instanceof ResolvedEntityAtomType) {
                return this.splitEntityConceptTypes(witha, ofa);
            }
            else if(witha instanceof ResolvedConceptAtomType) {
                return this.splitConceptTypes(ofa, witha);
            }
            else if (witha instanceof ResolvedTupleAtomType) {
                return this.splitTupleConcept(witha, ofa);
            }
            else if (witha instanceof ResolvedRecordAtomType) {
                return this.splitRecordConcept(witha, ofa);
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else if (ofa instanceof ResolvedTupleAtomType) {
            if(witha instanceof ResolvedConceptAtomType) {
                return this.splitTupleConcept(ofa, witha);
            }
            else if (witha instanceof ResolvedTupleAtomType) {
                return this.splitTupleTypes(ofa, witha);
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else if (ofa instanceof ResolvedRecordAtomType) {
            if(witha instanceof ResolvedConceptAtomType) {
                return this.splitRecordConcept(ofa, witha);
            }
            else if (witha instanceof ResolvedRecordAtomType) {
                return this.splitRecordTypes(ofa, witha);
            }
            else {
                return { tp: undefined, fp: ofa };
            }
        }
        else {
            return { tp: undefined, fp: ofa };
        }
    }

    private splitAtomWithType(ofa: ResolvedAtomType, witht: ResolvedType): { tp: ResolvedType[], fp: ResolvedType[] } {
        let tp: ResolvedType[] = [];
        let fp: ResolvedType[] = [];
        witht.options
            .map((opt) => this.splitAtomTypes(ofa, opt))
            .forEach((rr) => {
                if(rr.tp !== undefined) {
                    tp.push(ResolvedType.createSingle(rr.tp));
                }
                if(rr.fp !== undefined) {
                    fp.push(ResolvedType.createSingle(rr.fp));
                }
            });

        return { tp: tp, fp: fp };
    }

    splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType() || witht.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        if (oft.idStr === witht.idStr) {
            return { tp: oft, fp: ResolvedType.createEmpty() };
        }

        const paths = oft.options.map((opt) => this.splitAtomWithType(opt, witht));
        let tp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.tp));
        let fp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.fp));

        return {tp: this.typeUpperBound(tp), fp: this.typeUpperBound(fp)};
    }

    getDerivedTypeProjection(fromtype: ResolvedType, oftype: ResolvedType): ResolvedType {
        if(oftype.idStr === "NSCore::Record") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else if(oftype.idStr === "NSCore::KeyType") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else if(oftype.idStr === "NSCore::APIType") {
            //
            //NOT IMPLEMENTED YET
            //
            assert(false);
            return ResolvedType.createEmpty();
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Template(t: TemplateTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if(t.name === "*") {
            return ResolvedType.createSingle(new ResolvedWildcardAtomType());
        }
        return binds.has(t.name) ? binds.get(t.name) as ResolvedType : ResolvedType.createEmpty();
    }

    private normalizeType_Nominal(t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedType | ResolvedFunctionType {
        const [aliasResolvedType, aliasResolvedBinds] = this.lookupTypeDef(t, binds);
        if (aliasResolvedType === undefined) {
            return ResolvedType.createEmpty();
        }
        else if (!(aliasResolvedType instanceof NominalTypeSignature)) {
            return this.normalizeTypeGeneral(aliasResolvedType, aliasResolvedBinds);
        }
        else {
            const fconcept = this.tryGetConceptTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName);
            if (fconcept !== undefined) {
                if (fconcept.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                const cta = this.createConceptTypeAtom(fconcept, aliasResolvedType, aliasResolvedBinds);
                return cta !== undefined ? ResolvedType.createSingle(cta) : ResolvedType.createEmpty();
            }

            const fobject = this.tryGetObjectTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName);
            if (fobject !== undefined) {
                if (fobject.terms.length !== aliasResolvedType.terms.length) {
                    return ResolvedType.createEmpty();
                }

                const ota = this.createObjectTypeAtom(fobject, aliasResolvedType, aliasResolvedBinds);
                return ota !== undefined ? ResolvedType.createSingle(ota) : ResolvedType.createEmpty();
            }

            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_Literal(l: LiteralTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const ltype = this.normalizeTypeOnly(l.oftype, new Map<string, ResolvedType>());

        //should be Bool, Int, or Enum
        if (ltype.isEmptyType() || !ltype.isUniqueCallTargetType()) {
            return ResolvedType.createEmpty();
        }

        if (typeof (l.typevalue) === "boolean" || typeof (l.typevalue) === "number") {
            return ResolvedType.createSingle(ResolvedLiteralAtomType.create(ltype, l.typevalue));
        }
        else {
            const lenum = l.typevalue as { enumtype: TypeSignature, enumvalue: string };
            return ResolvedType.createSingle(ResolvedLiteralAtomType.create(ltype, { enumtype: ltype, enumvalue: lenum.enumvalue }));
        }
    }

    private normalizeType_Tuple(t: TupleTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => new ResolvedTupleAtomTypeEntry(this.normalizeTypeOnly(entry[0], binds), entry[1]));
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        let seenreq = false;
        for (let i = entries.length - 1; i >= 0; --i) {
            seenreq = seenreq || !entries[i].isOptional;
            if (entries[i].isOptional && seenreq) {
                return ResolvedType.createEmpty();
            }
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(t.isvalue, entries));
    }

    private normalizeType_Record(t: RecordTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        let seenNames = new Set<string>();
        let entries: ResolvedRecordAtomTypeEntry[] = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                return ResolvedType.createEmpty();
            }

            entries.push(new ResolvedRecordAtomTypeEntry(t.entries[i][0], this.normalizeTypeOnly(t.entries[i][1], binds), t.entries[i][2]));
        }
        if (entries.some((e) => e.type.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(t.isvalue, entries));
    }

    private normalizeType_EphemeralList(t: EphemeralListTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const entries = t.entries.map((entry) => this.normalizeTypeOnly(entry, binds));
        if (entries.some((e) => e.isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedEphemeralListType.create(entries));
    }

    private normalizeType_Projection(t: ProjectTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const fromt = this.normalizeTypeOnly(t.fromtype, binds);
        const oft = this.normalizeTypeOnly(t.oftype, binds);

        if(fromt.isEmptyType() || oft.isEmptyType()) {
            return ResolvedType.createEmpty();
        }

        return this.getDerivedTypeProjection(fromt, oft);
    }

    private normalizeType_Plus(t: PlusTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const ccs = t.types.map((tt) => this.normalizeTypeOnly(tt, binds));
        assert(ccs.length !== 0);

        if(ccs.some((tt) => tt.isEmptyType)) {
            return ResolvedType.createEmpty();
        }

        if(ccs.every((tt) => tt.isUniqueTupleTargetType())) {
            let tte: ResolvedTupleAtomTypeEntry[][] = [];
            let allvals = (ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).isvalue;
            let allrefs = !(ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).isvalue;
            for(let i = 0; i < ccs.length - 1; ++i) {
                const rte = ccs[i].options[0] as ResolvedTupleAtomType;
                if(rte.types.some((entry) => entry.isOptional)) {
                    return ResolvedType.createEmpty();
                }

                tte.push(rte.types);
                allvals = allvals && rte.isvalue;
                allrefs = allrefs && !rte.isvalue;
            }

            tte.push((ccs[ccs.length -1].options[0] as ResolvedTupleAtomType).types);

            if(!allvals && !allrefs) {
                return ResolvedType.createEmpty();
            }

            const fte = ([] as ResolvedTupleAtomTypeEntry[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(allvals, fte));
        }
        else if(ccs.every((tt) => tt.isUniqueRecordTargetType())) {
            let tte: ResolvedRecordAtomTypeEntry[][] = [];
            let names = new Set<string>();
            let allvals = true;
            let allrefs = true;
            for(let i = 0; i < ccs.length; ++i) {
                const rte = ccs[i].options[0] as ResolvedRecordAtomType;
                if(rte.entries.some((entry) => names.has(entry.name))) {
                    return ResolvedType.createEmpty();
                }

                tte.push(rte.entries);
                rte.entries.forEach((entry) => names.add(entry.name));

                allvals = allvals && rte.isvalue;
                allrefs = allrefs && !rte.isvalue;
            }

            if(!allvals && !allrefs) {
                return ResolvedType.createEmpty();
            }

            const fte = ([] as ResolvedRecordAtomTypeEntry[]).concat(...tte);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(allvals, fte));
        }
        else {
            return ResolvedType.createEmpty();
        }
    }

    private normalizeType_And(t: AndTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const ntypes: ResolvedAtomType[][] = t.types.map((opt) => this.normalizeTypeOnly(opt, binds).options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        if (flattened.some((ttype) => !(ttype instanceof ResolvedConceptAtomType))) {
            return ResolvedType.createEmpty();
        }

        const ctypes = flattened.map((arg) => (arg as ResolvedConceptAtomType).conceptTypes);
        const itypes = (([] as ResolvedConceptAtomTypeEntry[]).concat(...ctypes)).sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

        //do a simplification based on A & B when A \Subtypeeq B is A
        let simplifiedTypes: ResolvedConceptAtomTypeEntry[] = [];
        for (let i = 0; i < itypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < itypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Tj
                if (this.atomSubtypeOf(ResolvedConceptAtomType.create([itypes[j]]), ResolvedConceptAtomType.create([itypes[i]]))) {
                    docopy = (itypes[i].idStr === itypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(itypes[i]);
            }
        }

        if (simplifiedTypes.length === 0) {
            return ResolvedType.createEmpty();
        }

        return ResolvedType.createSingle(ResolvedConceptAtomType.create(simplifiedTypes));
    }

    private normalizeType_Union(t: UnionTypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return ResolvedType.createEmpty();
        }

        const utypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));
        return this.normalizeUnionList(utypes);
    }

    private normalizeEphemerals(ephemerals: ResolvedEphemeralListType[]): ResolvedEphemeralListType | undefined {
        const lidx = Math.max(...ephemerals.map((tt) => tt.types.length));
        const uidx = Math.min(...ephemerals.map((tt) => tt.types.length));
        if(lidx !== uidx) {
            return undefined; //can't have different lengths!!!
        }

        let nte: ResolvedType[] = [];
        for (let i = 0; i < lidx; ++i) {
            const ttypes = ephemerals.map((tt) => tt.types[i]);
            const ttype = this.typeUpperBound(ttypes);
            nte.push(ttype);
        }

        return ResolvedEphemeralListType.create(nte);
    }

    private normalizeUnionList(types: ResolvedType[]): ResolvedType {
        //flatten any union types
        const ntypes: ResolvedAtomType[][] = types.map((opt) => opt.options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        //check for Some | None and add Any if needed
        if (flattened.some((atom) => atom.idStr === "NSCore::None") && flattened.some((atom) => atom.idStr === "NSCore::Some")) {
            flattened.push(this.getSpecialAnyConceptType().options[0]);
        }

        const teph = flattened.filter((tt) => tt instanceof ResolvedEphemeralListType) as ResolvedEphemeralListType[];
        let merged = flattened.filter((tt) => !(tt instanceof ResolvedEphemeralListType));

        if (teph.length !== 0) {
            const eet = this.normalizeEphemerals(teph);
            if (eet === undefined || merged.length !== 0) {
                return ResolvedType.createEmpty();
            }
            else {
                merged.push(eet);
            }
        }

        const utypes = merged.sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));

        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes: ResolvedAtomType[] = [];
        for (let i = 0; i < utypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < utypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Ti
                if (this.atomSubtypeOf(utypes[i], utypes[j])) {
                    docopy = (utypes[i].idStr === utypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(utypes[i]);
            }
        }

        return ResolvedType.create(simplifiedTypes);
    }

    private normalizeType_Function(t: FunctionTypeSignature, binds: Map<string, ResolvedType>): ResolvedFunctionType | undefined {
        const params = t.params.map((param) => new ResolvedFunctionTypeParam(param.name, this.normalizeTypeGeneral(param.type, binds), param.isOptional, param.isRef));
        const optRestParamType = (t.optRestParamType !== undefined) ? this.normalizeTypeOnly(t.optRestParamType, binds) : undefined;
        const rtype = this.normalizeTypeOnly(t.resultType, binds);

        if (params.some((p) => p.type instanceof ResolvedType && p.type.isEmptyType()) || params.some((p) => p.isOptional && p.isRef) || (optRestParamType !== undefined && optRestParamType.isEmptyType()) || rtype.isEmptyType()) {
            return undefined;
        }

        return ResolvedFunctionType.create(t.recursive, params, t.optRestParamName, optRestParamType, rtype);
    }

    private atomSubtypeOf_EntityConcept(t1: ResolvedEntityAtomType, t2: ResolvedConceptAtomType): boolean {
        const t2type = ResolvedType.createSingle(t2);
        return this.resolveProvides(t1.object, t1.binds).some((provide) => {
            const tt = this.normalizeTypeOnly(provide, t1.binds);
            return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
        });
    }

    private checkAllTupleEntriesOfType(t1: ResolvedTupleAtomType, t2: ResolvedType): boolean {
        return t1.types.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private atomSubtypeOf_TupleConcept(t1: ResolvedTupleAtomType, t2: ResolvedConceptAtomType): boolean {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        if (t1.grounded) {
            if (this.checkAllTupleEntriesOfType(t1, this.getSpecialKeyTypeConceptType())) {
                tci.push(...(this.getSpecialKeyTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
            if (this.checkAllTupleEntriesOfType(t1, this.getSpecialAPITypeConceptType())) {
                if (this.checkAllTupleEntriesOfType(t1, this.getSpecialPODTypeConceptType())) {
                    tci.push(...(this.getSpecialPODTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
                else {
                    tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
            }
        }

        return this.subtypeOf(ResolvedType.createSingle(ResolvedConceptAtomType.create(tci)), ResolvedType.createSingle(t2));
    }

    private checkAllRecordEntriesOfType(t1: ResolvedRecordAtomType, t2: ResolvedType): boolean {
        return t1.entries.every((entry) => this.subtypeOf(entry.type, t2));
    }

    private atomSubtypeOf_RecordConcept(t1: ResolvedRecordAtomType, t2: ResolvedConceptAtomType): boolean {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        if (t1.grounded) {
            if (this.checkAllRecordEntriesOfType(t1, this.getSpecialKeyTypeConceptType())) {
                tci.push(...(this.getSpecialKeyTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
            if (this.checkAllRecordEntriesOfType(t1, this.getSpecialAPITypeConceptType())) {
                if (this.checkAllRecordEntriesOfType(t1, this.getSpecialPODTypeConceptType())) {
                    tci.push(...(this.getSpecialPODTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
                else {
                    tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
                }
            }
        }

        return this.subtypeOf(ResolvedType.createSingle(ResolvedConceptAtomType.create(tci)), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_ConceptConcept(t1: ResolvedConceptAtomType, t2: ResolvedConceptAtomType, ): boolean {
        return t2.conceptTypes.every((c2t) => {
            return t1.conceptTypes.some((c1t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => (allBindsOk = allBindsOk && v.idStr === (c2t.binds.get(k) as ResolvedType).idStr));
                    return allBindsOk;
                }

                const t2type = ResolvedType.createSingle(ResolvedConceptAtomType.create([c2t]));
                return this.resolveProvides(c1t.concept, c1t.binds).some((provide) => {
                    const tt = this.normalizeTypeOnly(provide, c1t.binds);
                    return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
                });
            });
        });
    }

    private atomSubtypeOf_TupleTuple(t1: ResolvedTupleAtomType, t2: ResolvedTupleAtomType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return false;
        }

       for (let i = 0; i < t1.types.length; ++i) {
            const t1e = t1.types[i];

           if (i >= t2.types.length) {
               return false;
           }
           else {
               const t2e = t2.types[i];
               if ((t1e.isOptional && !t2e.isOptional) || t1e.type.idStr !== t2e.type.idStr) {
                   return false;
               }
            }
        }

        //t2 has a required entry that is not required in t1
        if (t2.types.length > t1.types.length && t2.types.slice(t1.types.length).some((entry) => !entry.isOptional)) {
            return false;
        }

        return true;
    }

    private atomSubtypeOf_RecordRecord(t1: ResolvedRecordAtomType, t2: ResolvedRecordAtomType): boolean {
        if(t1.isvalue !== t2.isvalue) {
            return false;
        }

        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                badEntry = badEntry || true;
            }
            else {
                if ((entry.isOptional && !t2e.isOptional) || entry.type.idStr !== t2e.type.idStr) {
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

    private internSpecialConceptType(name: string, terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", name, terms || [] as TypeSignature[]);
        const tconcept = this.createConceptTypeAtom(this.tryGetConceptTypeForFullyResolvedName("NSCore::" + name) as ConceptTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tconcept as ResolvedAtomType);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);

        return rtype;
    }

    private internSpecialObjectType(name: string, terms?: TypeSignature[], binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name) as ResolvedType;
        }

        const rsig = new NominalTypeSignature("NSCore", name, terms || [] as TypeSignature[]);
        const tobject = this.createObjectTypeAtom(this.tryGetObjectTypeForFullyResolvedName("NSCore::" + name) as EntityTypeDecl, rsig, binds || new Map<string, ResolvedType>());
        const rtype = ResolvedType.createSingle(tobject as ResolvedAtomType);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);

        return rtype;
    }

    getSpecialNoneType(): ResolvedType { return this.internSpecialObjectType("None"); }
    getSpecialEmptyType(): ResolvedType { return this.internSpecialObjectType("Empty"); }
    getSpecialBoolType(): ResolvedType { return this.internSpecialObjectType("Bool"); }
    getSpecialIntType(): ResolvedType { return this.internSpecialObjectType("Int"); }
    getSpecialBigIntType(): ResolvedType { return this.internSpecialObjectType("BigInt"); }
    getSpecialFloat64Type(): ResolvedType { return this.internSpecialObjectType("Float64"); }
    getSpecialStringType(): ResolvedType { return this.internSpecialObjectType("String"); }
    getSpecialBufferFormatType(): ResolvedType { return this.internSpecialObjectType("BufferFormat"); }
    getSpecialBufferEncodingType(): ResolvedType { return this.internSpecialObjectType("BufferEncoding"); }
    getSpecialBufferCompressionType(): ResolvedType { return this.internSpecialObjectType("BufferCompression"); }
    getSpecialByteBufferType(): ResolvedType { return this.internSpecialObjectType("ByteBuffer"); }
    getSpecialISOTimeType(): ResolvedType { return this.internSpecialObjectType("ISOTime"); }
    getSpecialUUIDType(): ResolvedType { return this.internSpecialObjectType("UUID"); }
    getSpecialLogicalTimeType(): ResolvedType { return this.internSpecialObjectType("LogicalTime"); }
    getSpecialCryptoHashType(): ResolvedType { return this.internSpecialObjectType("CryptoHash"); }
    getSpecialRegexType(): ResolvedType { return this.internSpecialObjectType("Regex"); }
    getSpecialRegexMatchType(): ResolvedType { return this.internSpecialObjectType("RegexMatch"); }

    getSpecialAnyConceptType(): ResolvedType { return this.internSpecialConceptType("Any"); }
    getSpecialSomeConceptType(): ResolvedType { return this.internSpecialConceptType("Some"); }

    getSpecialParsableConceptType(): ResolvedType { return this.internSpecialConceptType("Parsable"); }
    getSpecialValidatorConceptType(): ResolvedType { return this.internSpecialConceptType("Validator"); }
    getSpecialKeyTypeConceptType(): ResolvedType { return this.internSpecialConceptType("KeyType"); }
    getSpecialPODTypeConceptType(): ResolvedType { return this.internSpecialConceptType("PODType"); }
    getSpecialAPIValueConceptType(): ResolvedType { return this.internSpecialConceptType("APIValue"); }
    getSpecialAPITypeConceptType(): ResolvedType { return this.internSpecialConceptType("APIType"); }
    getSpecialTruthyConceptType(): ResolvedType { return this.internSpecialConceptType("Truthy"); }
    getSpecialEnumConceptType(): ResolvedType { return this.internSpecialConceptType("Enum"); }
    getSpecialIdKeyConceptType(): ResolvedType { return this.internSpecialConceptType("IdKey"); }
    
    getSpecialObjectConceptType(): ResolvedType { return this.internSpecialConceptType("Object"); }

    isStringOfType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::StringOf<"); }
    isDataStringType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::DataString<"); }
    isBufferType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Buffer<"); }
    isBufferOfType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::BufferOf<"); }
    isOptionConceptType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Option<"); }
    isOptionEntityType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Of<"); }
    isResultConceptType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Result<"); }
    isResultEntityType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Ok<") || ty.idStr.startsWith("NSCore::Err<"); }
    
    isExpandoableType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Expandoable<"); }
    isListType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Vector<") || ty.idStr.startsWith("NSCore::List<"); }
    isSetType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Set<") || ty.idStr.startsWith("NSCore::DynamicSet<"); }
    isMapType(ty: ResolvedAtomType): boolean { return ty.idStr.startsWith("NSCore::Map<") || ty.idStr.startsWith("NSCore::DynamicMap<"); }

    ensureNominalRepresentation(t: ResolvedType): ResolvedType {
        const opts = t.options.map((opt) => {
            if (opt instanceof ResolvedTupleAtomType) {
                return this.getSpecialSomeConceptType();
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return this.getSpecialSomeConceptType();
            }
            else {
                return ResolvedType.createSingle(opt);
            }
        });

        return this.typeUpperBound(opts);
    }

    tryGetConceptTypeForFullyResolvedName(name: string): ConceptTypeDecl | undefined {
        return this.m_conceptMap.get(name);
    }

    tryGetObjectTypeForFullyResolvedName(name: string): EntityTypeDecl | undefined {
        return this.m_objectMap.get(name);
    }

    tryGetValidatorForFullyResolvedName(name: string): BSQRegex | undefined {
        return this.m_validatorRegexs.get(name);
    }

    hasNamespace(ns: string): boolean {
        return this.m_namespaceMap.has(ns);
    }

    getNamespace(ns: string): NamespaceDeclaration {
        return this.m_namespaceMap.get(ns) as NamespaceDeclaration;
    }

    ensureNamespace(ns: string): NamespaceDeclaration {
        if (!this.hasNamespace(ns)) {
            this.m_namespaceMap.set(ns, new NamespaceDeclaration(ns));
        }

        return this.getNamespace(ns);
    }

    getNamespaces(): NamespaceDeclaration[] {
        let decls: NamespaceDeclaration[] = [];
        this.m_namespaceMap.forEach((v, k) => {
            decls.push(v);
        });
        return decls;
    }

    addConceptDecl(resolvedName: string, concept: ConceptTypeDecl) {
        this.m_conceptMap.set(resolvedName, concept);
    }

    addObjectDecl(resolvedName: string, object: EntityTypeDecl) {
        this.m_objectMap.set(resolvedName, object);
    }

    addValidatorRegex(resolvedName: string, validator: BSQRegex) {
        this.m_literalRegexs.add(validator);
        this.m_validatorRegexs.set(resolvedName, validator);
    }

    addLiteralRegex(re: BSQRegex) {
        this.m_literalRegexs.add(re);
    }

    getAllLiteralRegexs(): Set<BSQRegex> {
        return this.m_literalRegexs;
    }

    getAllValidators(): [ResolvedEntityAtomType, BSQRegex][] {
        return [...this.m_validatorRegexs].map((vre) => {
            const ve = ResolvedEntityAtomType.create(this.m_objectMap.get(vre[0]) as EntityTypeDecl, new Map<string, ResolvedType>());
            return [ve, vre[1]];
        });
    } 

    ////
    //Type representation, normalization, and operations
    lookupTypeDef(t: NominalTypeSignature, binds: Map<string, ResolvedType>): [TypeSignature | undefined, Map<string, ResolvedType>] {
        if (!this.hasNamespace(t.nameSpace)) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        const lname = t.nameSpace + "::" + t.baseName;
        const nsd = this.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            return [t, new Map<string, ResolvedType>(binds)];
        }

        //compute the bindings to use when resolving the RHS of the typedef alias
        const typealias = nsd.typeDefs.get(lname) as NamespaceTypedef;
        const updatedbinds = this.resolveTemplateBinds(typealias.terms, t.terms, binds);
        if(updatedbinds === undefined) {
            return [undefined, new Map<string, ResolvedType>()];
        }

        if (typealias.boundType instanceof NominalTypeSignature) {
            return this.lookupTypeDef(typealias.boundType, updatedbinds);
        }
        else {
            return [typealias.boundType, updatedbinds];
        }
    }

    createConceptTypeAtom(concept: ConceptTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedConceptAtomType | undefined {
        const fullbinds = this.resolveTemplateBinds(concept.terms, t.terms, binds);
        if(fullbinds === undefined) {
            return undefined;
        }

        return ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(concept, fullbinds)]);
    }

    createObjectTypeAtom(object: EntityTypeDecl, t: NominalTypeSignature, binds: Map<string, ResolvedType>): ResolvedEntityAtomType | undefined {
        const fullbinds = this.resolveTemplateBinds(object.terms, t.terms, binds);
        if(fullbinds === undefined) {
            return undefined;
        }

        return ResolvedEntityAtomType.create(object, fullbinds);
    }

    getAllOOFields(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, fmap?: Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        let declfields = fmap || new Map<string, [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();

        //Important to do traversal in Left->Right Topmost traversal order

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFields(concept.concept, concept.binds, declfields);
            });
        });

        ooptype.memberFields.forEach((mf, name) => {
            if (!declfields.has(name)) {
                declfields.set(name, [ooptype, mf, binds]);
            }
        });

        return declfields;
    }

    getExpandoProvides(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>): ResolvedType | undefined {
        if(ooptype.ns === "NSCore" && ooptype.name === "Expandoable") {
            return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ooptype as ConceptTypeDecl, binds)]));
        }

        const rtypes = this.resolveProvides(ooptype, binds);
        for(let i = 0; i < rtypes.length; ++i) {
            const tt = this.normalizeTypeOnly(rtypes[i], binds);
            const ct = (tt.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const ep = this.getExpandoProvides(ct.concept, ct.binds);
            if(ep !== undefined) {
                return ep;
            }
        }
        
        return undefined;
    }

    getAllInvariantProvidingTypes(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs:  [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        this.resolveProvides(ooptype, binds).forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            (tt.options[0] as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                declinvs = this.getAllInvariantProvidingTypes(concept.concept, concept.binds, declinvs);
            });
        });

        const ttype = ResolvedType.createSingle(ooptype instanceof EntityTypeDecl ? ResolvedEntityAtomType.create(ooptype, binds) : ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ooptype as ConceptTypeDecl, binds)]));
        if(declinvs.find((dd) => dd[0].idStr === ttype.idStr)) {
            return declinvs;
        }
        else {
            if(ooptype.invariants.length !== 0) {
                declinvs.push([ttype, ooptype, binds]);
            }

            return declinvs;
        }
    }

    hasInvariants(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>): boolean {
        return this.getAllInvariantProvidingTypes(ooptype, binds).length !== 0;
    }

    getAbstractPrePostConds(fname: string, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, callbinds: Map<string, ResolvedType>): {pre: [PreConditionDecl[], Map<string, ResolvedType>], post: [PostConditionDecl[], Map<string, ResolvedType>] } | undefined {
        const rprovides = this.resolveProvides(ooptype, oobinds);
        for (let i = 0; i < rprovides.length; ++i) {
            const provide = rprovides[i];
            const tt = this.normalizeTypeOnly(provide, oobinds);
            for (let j = 0; j < (tt.options[0] as ResolvedConceptAtomType).conceptTypes.length; ++j) {
                const concept = (tt.options[0] as ResolvedConceptAtomType).conceptTypes[j];
                const pc = this.getAbstractPrePostConds(fname, concept.concept, concept.binds, callbinds);
                if (pc !== undefined) {
                    return pc;
                }
            }
        }

        if (ooptype.memberMethods.has(fname) && !(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.attributes.includes("override")) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            (ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.preconditions, newbinds], post: [(ooptype.memberMethods.get(fname) as MemberMethodDecl).invoke.postconditions, newbinds]};
        }

        if (ooptype.staticFunctions.has(fname) && !(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.attributes.includes("override")) {
            let newbinds = new Map<string, ResolvedType>();
            oobinds.forEach((v, k) => newbinds.set(k, v));
            (ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.terms.forEach((term) => newbinds.set(term.name, callbinds.get(term.name) as ResolvedType));

            return {pre: [(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.preconditions, newbinds], post: [(ooptype.staticFunctions.get(fname) as StaticFunctionDecl).invoke.postconditions, newbinds]};
        }

        return undefined;
    }

    private tryGetOOMemberDeclThis(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        let decl: OOMemberDecl | undefined = undefined;
        if (kind === "const") {
            decl = ooptype.staticMembers.get(search);
        }
        else if (kind === "static") {
            decl = ooptype.staticFunctions.get(search);
        }
        else if (kind === "field") {
            decl = ooptype.memberFields.get(search);
        }
        else {
            decl = ooptype.memberMethods.get(search);
        }

        if (decl === undefined) {
            return undefined;
        }
        else {
            return new OOMemberLookupInfo(ooptype, decl, binds);
        }
    }

    private tryGetOOMemberDeclParent(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        const rprovides = this.resolveProvides(ooptype, binds);
        for (let i = 0; i < rprovides.length; ++i) {
            const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
            const res = this.tryGetOOMemberDeclThis(tt.concept, tt.binds, kind, search) || this.tryGetOOMemberDeclParent(tt.concept, tt.binds, kind, search);
            if (res !== undefined) {
                return res;
            }
        }

        return undefined;
    }

    private tryGetOOMemberRootDeclarationOptions(ooptype: OOPTypeDecl, binds: Map<string, ResolvedType>, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo[] | undefined {
        const tdecl = this.tryGetOOMemberDeclThis(ooptype, binds, kind, search);
        const pdecl = this.tryGetOOMemberDeclParent(ooptype, binds, kind, search);
        if (tdecl === undefined && pdecl === undefined) {
            return undefined;
        }
        else if (tdecl !== undefined && pdecl === undefined) {
            return [tdecl];
        }
        else {
            let dopts: OOMemberLookupInfo[] = [];

            const rprovides = this.resolveProvides(ooptype, binds);
            for (let i = 0; i < rprovides.length; ++i) {
                const tt = (this.normalizeTypeOnly(rprovides[i], binds).options[0] as ResolvedConceptAtomType).conceptTypes[0];
                const copts = this.tryGetOOMemberRootDeclarationOptions(tt.concept, tt.binds, kind, search);
                if (copts !== undefined) {
                    dopts = dopts.concat(copts);
                }
            }

            return dopts;
        }
    }

    private ensureSingleDecl(opts: OOMemberLookupInfo[]): OOMemberLookupInfo | undefined {
        if (opts.length === 0) {
            return undefined;
        }
        else if (opts.length === 1) {
            return opts[0];
        }
        else {
            const opt1 = opts[0];
            const allSame = opts.every((opt) => {
                if (opt1.contiainingType.ns !== opt.contiainingType.ns || opt1.contiainingType.name !== opt.contiainingType.name) {
                    return false;
                }

                if (opt1.binds.size !== opt.binds.size) {
                    return false;
                }

                let bindsok = true;
                opt1.binds.forEach((v, k) => {
                    bindsok = bindsok && opt.binds.has(k) && v.idStr === (opt.binds.get(k) as ResolvedType).idStr;
                });

                return bindsok;
            });

            return allSame ? opt1 : undefined;
        }
    }

    tryGetOOMemberDeclUnique(tt: ResolvedType, kind: "const" | "static" | "field" | "method", search: string): OOMemberLookupInfo | undefined {
        const atom = ResolvedType.tryGetOOTypeInfo(this.ensureNominalRepresentation(tt));
        if (atom === undefined) {
            return undefined;
        }

        if (atom instanceof ResolvedEntityAtomType) {
            return this.tryGetOOMemberDeclThis(atom.object, atom.binds, kind, search) || this.tryGetOOMemberDeclParent(atom.object, atom.binds, kind, search);
        }
        else {
            const opts = atom.conceptTypes.map((opt) => this.tryGetOOMemberDeclThis(opt.concept, opt.binds, kind, search) || this.tryGetOOMemberDeclParent(opt.concept, opt.binds, kind, search));
            return this.ensureSingleDecl(opts.filter((opt) => opt !== undefined) as OOMemberLookupInfo[]);
        }
    }

    tryGetOOMemberDeclOptions(tt: ResolvedType, kind: "const" | "static" | "field" | "method", search: string): { decls: OOMemberLookupInfo[] | undefined, root: OOMemberLookupInfo | undefined } {
        const decls = this.ensureNominalRepresentation(tt).options.map((atom) => this.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), kind, search));
        if (decls.some((opt) => opt === undefined)) {
            return { decls: undefined, root: undefined };
        }

        const ropts = (decls as OOMemberLookupInfo[]).map((info) => this.tryGetOOMemberRootDeclarationOptions(info.contiainingType, info.binds, kind, search) as OOMemberLookupInfo[]);
        const roots = ([] as OOMemberLookupInfo[]).concat(...ropts);
        return { decls: decls as OOMemberLookupInfo[], root: this.ensureSingleDecl(roots) };
    }

    resolveBindsForCall(declterms: TemplateTermDecl[], giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>): Map<string, ResolvedType> | undefined {
        let fullbinds = new Map<string, ResolvedType>();
        implicitBinds.forEach((v, k) => {
            fullbinds.set(k, v);
        });

        for (let i = 0; i < declterms.length; ++i) {
            if(giventerms.length <= i) {
                if(declterms[i].defaultType !== undefined) {
                    fullbinds.set(declterms[i].name, this.normalizeTypeOnly(declterms[i].defaultType as TypeSignature, implicitBinds));
                }
                else if (declterms[i].isInfer) {
                    fullbinds.set(declterms[i].name, this.getSpecialAnyConceptType());
                }
                else {
                    return undefined;
                }
            }
            else {
                fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], callBinds));
            }
        }

        return fullbinds;
    }

    normalizeTypeOnly(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const res = this.normalizeTypeGeneral(t, binds);
        if (res instanceof ResolvedFunctionType) {
            return ResolvedType.createEmpty();
        }
        else {
            return res;
        }
    }

    normalizeTypeFunction(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedFunctionType | undefined {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return undefined;
        }
        else {
            return this.normalizeType_Function(t as FunctionTypeSignature, binds);
        }
    }

    normalizeTypeGeneral(t: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType | ResolvedFunctionType {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return ResolvedType.createEmpty();
        }
        else if (t instanceof FunctionTypeSignature) {
            return this.normalizeTypeFunction(t, binds) || ResolvedType.createEmpty();
        }
        else if (t instanceof TemplateTypeSignature) {
            return this.normalizeType_Template(t, binds);
        }
        else if (t instanceof LiteralTypeSignature) {
            return this.normalizeType_Literal(t, binds);
        }
        else if (t instanceof NominalTypeSignature) {
            return this.normalizeType_Nominal(t, binds);
        }
        else if (t instanceof TupleTypeSignature) {
            return this.normalizeType_Tuple(t, binds);
        }
        else if (t instanceof RecordTypeSignature) {
            return this.normalizeType_Record(t, binds);
        }
        else if (t instanceof EphemeralListTypeSignature) {
            return this.normalizeType_EphemeralList(t, binds);
        }
        else if(t instanceof ProjectTypeSignature) {
            return this.normalizeType_Projection(t, binds);
        }
        else if (t instanceof PlusTypeSignature) {
            return this.normalizeType_Plus(t, binds);
        }
        else if (t instanceof AndTypeSignature) {
            return this.normalizeType_And(t, binds);
        }
        else {
            return this.normalizeType_Union(t as UnionTypeSignature, binds);
        }
    }

    normalizeToNominalRepresentation(t: ResolvedAtomType): ResolvedAtomType {
        if (t instanceof ResolvedTupleAtomType) {
            return this.getSpecialSomeConceptType();
        }
        else {
            return t;
        }
    }

    computeUnifiedFunctionType(funcs: ResolvedFunctionType[], rootSig: ResolvedFunctionType): ResolvedFunctionType | undefined {
        if (funcs.length === 0) {
            return undefined;
        }

        if (funcs.length === 1) {
            return funcs[0];
        }
        else {
            if (funcs.some((ft) => !this.functionSubtypeOf(ft, rootSig))) {
                return undefined;
            }

            return rootSig;
        }
    }

    restrictNone(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialNoneType());
    }

    restrictSome(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialSomeConceptType());
    }

    restrictT(from: ResolvedType, t: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, t);
    }

    typeUpperBound(types: ResolvedType[]): ResolvedType {
        if(type.length === 0) {
            return ResolvedType.createEmpty();
        }
        else {
            return this.normalizeUnionList(types);
        }
    }

    atomSubtypeOf(t1: ResolvedAtomType, t2: ResolvedAtomType): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.idStr === t2.idStr) {
            res = true;
        }
        else if(t1.idStr === "NSCore::Empty" && t2.idStr.startsWith("NSCore::Option<")) {
            res = true;
        }
        else if(t1 instanceof ResolvedWildcardAtomType || t2 instanceof ResolvedWildcardAtomType) {
            res = true;
        }
        else if (t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t2 instanceof ResolvedConceptAtomType) {
            if (t1 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordConcept(t1, t2);
            }
            else {
                //fall-through
            }
        }
        else {
            if (t1 instanceof ResolvedTupleAtomType && t2 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleTuple(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType && t2 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordRecord(t1, t2);
            }
            else {
                //fall-through
            }
        }

        memores.set(t2.idStr, res);
        return res;
    }

    subtypeOf(t1: ResolvedType, t2: ResolvedType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.idStr, res);
        return res;
    }
 
    resolveProvides(tt: OOPTypeDecl, binds: Map<string, ResolvedType>): TypeSignature[] {
        let oktypes: TypeSignature[] = [];
        
        for (let i = 0; i < tt.provides.length; ++i) {
            const psig = tt.provides[i][0];
            const pcond = tt.provides[i][1];
            
            if(pcond === undefined) {
                oktypes.push(psig);
            }
            else {
                const allok = pcond.constraints.every((consinfo) => {
                    const constype = this.normalizeTypeOnly(consinfo.t, binds)
                    return this.subtypeOf(constype, this.normalizeTypeOnly(consinfo.constraint, binds));
                });

                if(allok) {
                    oktypes.push(psig);
                }
            }
        }

        return oktypes;
    }

    private functionSubtypeOf_helper(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }

        if ((t2.optRestParamType !== undefined) !== (t1.optRestParamType !== undefined)) {
            return false; //should both have rest or not
        }

        if (t2.optRestParamType !== undefined && t2.optRestParamType.idStr !== (t1.optRestParamType as ResolvedType).idStr) {
            return false; //variance
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            if ((t2p.isOptional !== t1p.isOptional) || (t2p.isRef !== t1p.isRef)) {
                return false;
            }

            //We want the argument types to be the same for all cases -- no clear reason to overload to more general types
            if (t2p.type instanceof ResolvedFunctionType && t1p.type instanceof ResolvedFunctionType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
                    return false;
                }
            }
            else if (t2p.type instanceof ResolvedType && t1p.type instanceof ResolvedType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
                    return false;
                }
            }
            else {
                return false;
            }

            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t2.params[i].name !== t1.params[i].name) {
                    return false;
                }
            }
        }

        if(t1.resultType.idStr !== t2.resultType.idStr) {
            return false;
        }

        return true;
    }

    functionSubtypeOf(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.idStr) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = this.functionSubtypeOf_helper(t1, t2);

        memores.set(t2.idStr, res);
        return res;
    }
}

export {
    BuildLevel, isBuildLevelEnabled,
    TemplateTermDecl, TemplateTypeRestriction, TypeConditionRestriction, PreConditionDecl, PostConditionDecl, InvokeDecl,
    OOMemberDecl, InvariantDecl, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    OOMemberLookupInfo, Assembly
};
