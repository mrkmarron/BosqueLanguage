//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedFunctionTypeParam, ResolvedEphemeralListType, ResolvedConceptAtomTypeEntry } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, BuildLevel, isBuildLevelEnabled, PreConditionDecl, PostConditionDecl, TypeConditionRestriction, ConceptTypeDecl, SpecialTypeCategory, TemplateTermSpecialRestriction, NamespaceOperatorDecl, StaticOperatorDecl, NamespaceDeclaration } from "../ast/assembly";
import { TypeEnvironment, ExpressionReturnResult, VarInfo, FlowTypeTruthValue, StructuredAssignmentPathStep } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature, FunctionParameter, FunctionTypeSignature, TupleTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixModifyWithIndecies, PostfixModifyWithNames, PrefixNotOp, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ConstructorEphemeralValueList, VariablePackDeclarationStatement, VariablePackAssignmentStatement, NominalStructuredAssignment, ValueListStructuredAssignment, NakedCallStatement, ValidateStatement, IfElse, CondBranchEntry, LiteralBigIntegerExpression, LiteralFloatExpression, MapEntryConstructorExpression, SpecialConstructorExpression, LiteralNaturalExpression, LiteralBigNaturalExpression, LiteralRationalExpression, LiteralDecimalExpression, PragmaArguments, PostfixIs, PostfixHasIndex, PostfixHasProperty, PostfixAs, BinEqExpression, InvokeArgument, BinCmpExpression } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator, MIRBodyEmitter, ResultCheckCategory } from "../compiler/mir_emitter";
import { MIRTempRegister, MIRArgument, MIRConstantNone, MIRBody, MIRVirtualMethodKey, MIRConstantKey, MIRInvokeKey, MIRResolvedTypeKey, MIRFieldKey, MIRConstantString, MIRParameterVariable, MIRVariableArgument, MIRLocalVariable } from "../compiler/mir_ops";
import { SourceInfo, unescapeLiteralString } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIROOTypeDecl, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIREntityType, MIRRegex, MIREphemeralListType } from "../compiler/mir_assembly";
import * as assert from "assert";
import { BSQRegex } from "../ast/bsqregex";

class TypeError extends Error {
    readonly file: string;
    readonly line: number;

    constructor(file: string, line: number, message?: string) {
        super(`Type error on ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.file = file;
        this.line = line;
    }
}

type ExpandedArgument = {
    name: string | undefined,
    argtype: ResolvedType | ResolvedFunctionType,
    expando: boolean,
    ref: MIRVariableArgument | undefined,
    pcode: PCode | undefined,
    treg: MIRTempRegister
};

type FilledLocation = {
    vtype: ResolvedType | ResolvedFunctionType,
    mustDef: boolean,
    fflagchk: boolean,
    ref: MIRVariableArgument | undefined,
    pcode: PCode | undefined,
    trgt: MIRArgument
};

function createTupleStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, ival: number): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "tuple", ival: ival, nval: "[empty]" };
}

function createRecordStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, nval: string): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "record", ival: -1, nval: nval };
}

function createEphemeralStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, ival: number): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "elist", ival: ival, nval: "[empty]" };
}

function createNominalStructuredAssignmentPathStep(fromtype: ResolvedType, t: ResolvedType, nval: string): StructuredAssignmentPathStep {
    return { fromtype: fromtype, t: t, step: "nominal", ival: -1, nval: nval };
}

class TypeChecker {
    private readonly m_assembly: Assembly;

    private readonly m_buildLevel: BuildLevel;
    private readonly m_doLiteralStringValidate: boolean;

    private m_file: string;
    private m_errors: [string, number, string][];

    private readonly m_emitter: MIREmitter;

    private readonly AnySplitMethods = ["is", "as"];

    constructor(assembly: Assembly, emitter: MIREmitter, buildlevel: BuildLevel, doLiteralStringValidate: boolean) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;
        this.m_doLiteralStringValidate = doLiteralStringValidate;

        this.m_file = "[No File]";
        this.m_errors = [];

        this.m_emitter = emitter;
    }

    private raiseError(sinfo: SourceInfo, msg?: string) {
        this.m_emitter.setEmitEnabled(false);

        this.m_errors.push([this.m_file, sinfo.line, msg || "Type error"]);
        throw new TypeError(this.m_file, sinfo.line, msg || "Type error");
    }

    private raiseErrorIf(sinfo: SourceInfo, cond: boolean, msg?: string) {
        if (cond) {
            this.raiseError(sinfo, msg);
        }
    }

    getErrorList(): [string, number, string][] {
        return this.m_errors;
    }

    private resolveAndEnsureTypeOnly(sinfo: SourceInfo, ttype: TypeSignature, binds: Map<string, ResolvedType>): ResolvedType {
        const rtype = this.m_assembly.normalizeTypeOnly(ttype, binds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");

        this.m_emitter.registerResolvedTypeReference(rtype);
        return rtype;
    }

    private resolveOOTypeFromDecls(oodecl: OOPTypeDecl, oobinds: Map<string, ResolvedType>): ResolvedType {
        if(oodecl instanceof EntityTypeDecl) {
            return ResolvedType.createSingle(ResolvedEntityAtomType.create(oodecl, oobinds));
        }
        else {
            return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(oodecl as ConceptTypeDecl, oobinds)]));
        }
    }

    private isConstructorTypeOfValue(ctype: ResolvedType): boolean {
        const ootd = this.m_assembly.tryGetObjectTypeForFullyResolvedName(ctype.options[0].idStr);
        if (ootd === undefined) {
            return false;
        }

        return OOPTypeDecl.attributeSetContains("struct", ootd.attributes);
    }

    private getResultSubtypes(rtype: ResolvedType): [ResolvedType, ResolvedType] {
        const binds = (rtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
        const okentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Ok") as EntityTypeDecl;
        const errentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Err") as EntityTypeDecl;

        return [
            ResolvedType.createSingle(ResolvedEntityAtomType.create(okentity, new Map<string, ResolvedType>().set("T", binds.get("T") as ResolvedType))),
            ResolvedType.createSingle(ResolvedEntityAtomType.create(errentity, new Map<string, ResolvedType>().set("E", binds.get("E") as ResolvedType)))
        ];
    }

    private getResultBinds(rtype: ResolvedType): { T: ResolvedType, E: ResolvedType } {
        const binds = (rtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
        return { T: binds.get("T") as ResolvedType, E: binds.get("E") as ResolvedType };
    }

    private genInferInfo(sinfo: SourceInfo, oftype: ResolvedType, infertype: ResolvedType | undefined, trgt: MIRTempRegister): [ResolvedType, [MIRTempRegister, MIRTempRegister | undefined]] {
        if(infertype === undefined || oftype.isSameType(infertype)) {
            return [oftype, [trgt, undefined]];
        }
        else {
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(oftype, infertype), `Cannot convert type ${oftype.idStr} into ${infertype.idStr}`);
        
            return [infertype, [this.m_emitter.generateTmpRegister(), trgt]];
        }
    }

    private emitConvertIfNeeded(sinfo: SourceInfo, oftype: ResolvedType, infertype: ResolvedType | undefined, iipack: [MIRTempRegister, MIRTempRegister | undefined]) {
        if(iipack[1] === undefined) {
            return;
        }

        const mirsrctype = this.m_emitter.registerResolvedTypeReference(oftype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(infertype as ResolvedType);

        this.m_emitter.emitConvertUp(sinfo, mirsrctype, mirintotype, iipack[0], iipack[1]);
    }

    private emitInlineConvertIfNeeded(sinfo: SourceInfo, src: MIRArgument, srctype: ResolvedType, trgttype: ResolvedType): MIRArgument {
        if(srctype.isSameType(trgttype)) {
            return src;
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype, trgttype), `Cannot convert type ${srctype.idStr} into ${trgttype.idStr}`);

        const mirsrctype = this.m_emitter.registerResolvedTypeReference(srctype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(trgttype);

        const rr = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitConvertUp(sinfo, mirsrctype, mirintotype, src, rr);

        return rr;
    }

    private emitCheckedInlineConvertIfNeeded(sinfo: SourceInfo, src: MIRArgument, srctype: ResolvedType, trgttype: ResolvedType, fflag: string, index: number): MIRArgument {
        if(srctype.isSameType(trgttype)) {
            return src;
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(srctype, trgttype), `Cannot convert type ${srctype.idStr} into ${trgttype.idStr}`);

        const mirsrctype = this.m_emitter.registerResolvedTypeReference(srctype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(trgttype);

        const rr = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitCheckedConvertUp(sinfo, mirsrctype, mirintotype, src, rr, fflag, index);

        return rr;
    }

    private emitAssignToTempAndConvertIfNeeded_KnownSafe(sinfo: SourceInfo, srctype: ResolvedType, intotype: ResolvedType, src: MIRArgument, trgt: MIRTempRegister) {
        const mirsrctype = this.m_emitter.registerResolvedTypeReference(srctype);
        const mirintotype = this.m_emitter.registerResolvedTypeReference(intotype);

        if (srctype.isSameType(intotype)) {
            this.m_emitter.emitTempRegisterAssign(sinfo, src, trgt);
        }
        else if (this.m_assembly.subtypeOf(srctype, intotype)) {
            this.m_emitter.emitConvertUp(sinfo, mirsrctype, mirintotype, src, trgt);
        }
        else {
            this.m_emitter.emitConvertDown(sinfo, mirsrctype, mirintotype, src, trgt);
        }
    }

    private checkTemplateTypes(sinfo: SourceInfo, terms: TemplateTermDecl[], binds: Map<string, ResolvedType>, optTypeRestrict?: TypeConditionRestriction) {
        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];
            const termtype = binds.get(terminfo.name) as ResolvedType;

            const termconstraint = this.resolveAndEnsureTypeOnly(sinfo, terminfo.tconstraint, new Map<string, ResolvedType>());
            const boundsok = this.m_assembly.subtypeOf(termtype, termconstraint);
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.idStr}`);

            let opok = true;
            if(terminfo.opconstraint !== undefined) {
                xxxx;
            }
            this.raiseErrorIf(sinfo, !opok, "Template instantiation deos not satisfy the operator requirements");

            if (terminfo.specialRestrictions.size !== 0) {
                terminfo.specialRestrictions.forEach((srv) => {
                    switch (srv) {
                        case TemplateTermSpecialRestriction.Validator: {
                            const isunique = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isunique, "Validator types must be unique");
                            const isvalidator = termtype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl);
                            this.raiseErrorIf(sinfo, !isvalidator, "Not a valid validator type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Parsable:  {
                            const isunique = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isunique, "Parsable types must be unique");
                            const isparsable = termtype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ParsableTypeDecl);
                            this.raiseErrorIf(sinfo, !isparsable, "Not a valid parsable type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Grounded: {
                            this.raiseErrorIf(sinfo, !termtype.isGroundedType(), "Type is not grounded");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Entity: {
                            const isuniqueentity = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isuniqueentity, "entity types must be of a single entity declared type");
                            break;
                        }
                        case TemplateTermSpecialRestriction.Struct: {
                            const isuniqueentity = termtype.isUniqueCallTargetType();
                            this.raiseErrorIf(sinfo, !isuniqueentity, "struct types must be of a single entity declared type");
                            const isstruct = OOPTypeDecl.attributeSetContains("struct", termtype.getUniqueCallTargetType().object.attributes);
                            this.raiseErrorIf(sinfo, !isstruct, "struct types must have decl with struct attribute");
                            break;
                        }
                    }
                });
            }
        }

        if (optTypeRestrict !== undefined) {
            for (let i = 0; i < optTypeRestrict.constraints.length; ++i) {
                const consinfo = optTypeRestrict.constraints[i];
                const constype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.t, binds)

                const constrainttype = this.resolveAndEnsureTypeOnly(sinfo, consinfo.tconstraint, binds);
                const boundsok = this.m_assembly.subtypeOf(constype, constrainttype);
                this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified restriction -- not subtype of ${constrainttype.idStr}`);
            }
        }
    }

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl, invokeBinds: Map<string, ResolvedType>, pcodes: PCode[]) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");

        this.raiseErrorIf(sinfo, invoke.recursive === "no" && pcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            const rtype = this.m_assembly.normalizeTypeGeneral(invoke.params[i].type, invokeBinds);
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedType && rtype.isEmptyType(), "Bad type signature");

            xxxx;
            //TODO: need to check that optional argument parameter default values are type ok and that we register the initialization functions 
        }

        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }

        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, invokeBinds);
        }

        const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, invokeBinds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");
    }

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType, rec: "yes" | "no" | "cond") {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (fsig.optRestParamName !== undefined && fsig.optRestParamName !== "_") {
            allNames.add(fsig.optRestParamName);
        }
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        
            const rtype = fsig.params[i].type;
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedFunctionType, "Cannot have nested function type param");
        }

        const firstOptIndex = fsig.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < fsig.params.length; ++i) {
            this.raiseErrorIf(sinfo, !fsig.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
    }

    private checkRecursion(sinfo: SourceInfo, fsig: ResolvedFunctionType, pcodes: PCode[], crec: "yes" | "no" | "cond") {
        if ((fsig.recursive === "no" && crec === "no") || (fsig.recursive === "yes" && crec === "yes")) {
            return;
        }

        let sigr = fsig.recursive;
        if (sigr === "cond") {
            sigr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        let callr = crec;
        if (callr === "cond") {
            callr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }

        this.raiseErrorIf(sinfo, (sigr === "yes" && callr === "no") || (sigr === "no" && callr === "yes"), "Mismatched recursive annotations on call");
    }

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "stringof" | "datastring" | "operator" {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return rhs.options.some((opt) => opt.idStr === "NSCore::None") ? "lhsnone" : "falsealways";
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return lhs.options.some((opt) => opt.idStr === "NSCore::None") ? "rhsnone" : "falsealways";
        }
        
        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl))) {
            return !lhs.isSameType(rhs) ? "falsealways" : "stringof";
        }

        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl))) {
            return !lhs.isSameType(rhs) ? "falsealways" : "datastring";
        }

        return "operator";
    }
    
    private checkValueLess(lhs: ResolvedType, rhs: ResolvedType): "truealways" | "falsealways" | "stringof" | "datastring" | "operator" {
        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl))) {
            if(lhs.idStr < rhs.idStr) {
                return "truealways";
            }
            else if(lhs.idStr > rhs.idStr) {
                return "falsealways";
            }
            else {
                return "stringof";
            }
        }

        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl))) {
            if(lhs.idStr < rhs.idStr) {
                return "truealways";
            }
            else if(lhs.idStr > rhs.idStr) {
                return "falsealways";
            }
            else {
                return "datastring";
            }
        }
        
        return "operator";
    }

    private getInfoForHasIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Can only load indecies from Tuples");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx < tatom.types.length) && !tatom.types[idx].isOptional;
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx >= tatom.types.length);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) === "no");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => (atom as ResolvedTupleAtomType).types[idx].type));
    }

    private getInfoForHasProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedRecordAtomType)), "Can only load properties from Records");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.name === pname);
            return (eidx !== -1) && !tatom.entries[eidx].isOptional;
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.name === pname);
            return (eidx === -1);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) === "no");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) as ResolvedRecordAtomTypeEntry).type));
    }

    private getTypeForParameter(p: ResolvedFunctionTypeParam): ResolvedType {
        if (!p.isOptional) {
            return p.type as ResolvedType;
        }
        else {
            return p.exp === undefined ? this.m_assembly.typeUpperBound([p.type as ResolvedType, this.m_assembly.getSpecialNoneType()]) : (p.type as ResolvedType)
        }
    }

    private checkTypeOkForTupleExpando(sinfo: SourceInfo, rtype: ResolvedType): [number, number] {
        const tslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Can only expando into positional arguments with Tuple");
            return opt as ResolvedTupleAtomType;
        });
        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.filter((te) => !te.isOptional).length), Number.MAX_SAFE_INTEGER);
        const tlen = tslist.reduce((acc, v) => Math.max(acc, v.types.length), 0);

        return [reqlen, tlen];
    }

    private checkTypeOkForRecordExpando(sinfo: SourceInfo, rtype: ResolvedType): [Set<string>, Set<string>] {
        const rslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Can only expando into named arguments with Record");
            return opt as ResolvedRecordAtomType;
        });

        let allNames = new Set<string>();
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                allNames.add(re.name);
            });
        });

        let reqNames = new Set<string>(allNames);
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                if (re.isOptional) {
                    allNames.delete(re.name);
                }
            });
        });

        return [reqNames, allNames];
    }

    private checkPCodeExpressionInfer(env: TypeEnvironment, exp: ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): ResolvedType {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), cbinds);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

        this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");

        const fsig = ltypetry as ResolvedFunctionType;
        let refNames: string[] = [];
        let cargs = new Map<string, VarInfo>();

        for(let i = 0; i < exp.invoke.params.length; ++i) {
            const p = fsig.params[i];
            const ptype = this.getTypeForParameter(p);
            cargs.set(exp.invoke.params[i].name, new VarInfo(ptype, !p.isRef, false, true, ptype, FlowTypeTruthValue.Unknown));

            if (p.isRef) {
                refNames.push(p.name);
            }
        }
        if (fsig.optRestParamType !== undefined) {
            cargs.set(exp.invoke.optRestName as string, new VarInfo(fsig.optRestParamType, true, false, true, fsig.optRestParamType, FlowTypeTruthValue.Unknown));
        }

        exp.invoke.captureSet.forEach((v) => {
            if(v === "%this_captured" && env.lookupVar(v) === null) {
                const vinfo = env.lookupVar("this") as VarInfo;
                cargs.set(v, vinfo);
            }
            else {
                const vinfo = env.lookupVar(v) as VarInfo;
                this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");
                cargs.set(v, vinfo);
            }
        });

        const ikey = MIRKeyGenerator.generatePCodeKey(exp.invoke);
        const pcenv = TypeEnvironment.createInitialEnvForCall(ikey, new Map<string, ResolvedType>(cbinds), refNames, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, undefined);

        if (exp.invoke.body instanceof Expression) {
            const dummyreg = this.m_emitter.generateTmpRegister();
            const evalue = this.checkExpression(pcenv, exp.invoke.body, dummyreg, undefined);
            return evalue.getExpressionResult().exptype;
        }
        else {
            const renv = this.checkBlock(pcenv, (exp.invoke.body as BodyImplementation).body as BlockStatement);

            this.raiseErrorIf(exp.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            return renv.returnResult as ResolvedType;
        }
    }

    private checkArgumentsEvaluationWSigInfer(sinfo: SourceInfo, env: TypeEnvironment, ptypes: FunctionParameter[], args: Arguments, hasself: boolean, ibinds: Map<string, ResolvedType>, infer: string[]): Map<string, ResolvedType> {
        let resbinds = new Map<string, ResolvedType | undefined>();

        //
        //TODO: assumes a simple signature and call layout -- no optional, no rest, no named, no spread, no ref
        //      if we want to support some/all of this we will need to split the checking like we do for the real thing
        //

        const pidx = hasself ? 1 : 0;
        
        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const ptype = this.m_assembly.normalizeTypeGeneral(ptypes[pidx + i].type, ibinds);
            
            if (arg.value instanceof ConstructorPCodeExpression) {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedFunctionType), "Must have function type for function arg");
                
                const pcrtype = this.checkPCodeExpressionInfer(env, arg.value, ibinds, ptype as ResolvedFunctionType | undefined);
                this.m_assembly.typeUnify((ptype as ResolvedFunctionType).resultType, pcrtype, resbinds);
            }
            else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedFunctionType), "Must have function type for function arg");

                const pcode =  (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                this.m_assembly.typeUnify((ptype as ResolvedFunctionType).resultType, pcode.ftype.resultType, resbinds);
            }
            else {
                this.raiseErrorIf(arg.value.sinfo, !(ptype instanceof ResolvedType), "Must have non-function type for non-function arg");
                const dummyreg = this.m_emitter.generateTmpRegister();

                const etype = this.checkExpression(env, arg.value, dummyreg, undefined).getExpressionResult().exptype;
                this.m_assembly.typeUnify((ptype as ResolvedType), etype, resbinds);
            }
        }

        this.raiseErrorIf(sinfo, infer.some((ii) => !resbinds.has(ii)), "Could not compute bind for all needed variables");
        this.raiseErrorIf(sinfo, [...resbinds].some((bb) => bb[1] === undefined), "Binds were ambig for inference");

        let fbinds = new Map<string, ResolvedType>();
        resbinds.forEach((v, k) => fbinds.set(k, v as ResolvedType));
        return fbinds;
    }

    private checkPCodeExpression(env: TypeEnvironment, exp: ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), cbinds);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

        this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");
        this.raiseErrorIf(exp.sinfo, expectedFunction !== undefined && !this.m_assembly.functionSubtypeOf(ltypetry as ResolvedFunctionType, expectedFunction), "Mismatch in expected and provided function signature");

        let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

        let captures: string[] = [];
        exp.invoke.captureSet.forEach((v) => captures.push(v));
        captures.sort();

        captures.forEach((v) => {
            if(v === "%this_captured" && env.lookupVar(v) === null) {
                const vinfo = env.lookupVar("this") as VarInfo;

                capturedMap.set(v, vinfo.flowType);
            }
            else {
                const vinfo = env.lookupVar(v) as VarInfo;
                this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof ResolvedFunctionType, "Cannot capture function typed argument");

                capturedMap.set(v, vinfo.flowType);
            }
        });

        this.m_emitter.registerPCode(exp.invoke, ltypetry as ResolvedFunctionType, cbinds, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])));

        return {code: exp.invoke, scope: env.scope, captured: capturedMap, ftype: ltypetry as ResolvedFunctionType};
    }

    private checkArgumentsEvaluationWSig(sinfo: SourceInfo, env: TypeEnvironment, sig: ResolvedFunctionType, sigbinds: Map<string, ResolvedType>, args: Arguments, optSelfValue: [ResolvedType, string | undefined, MIRTempRegister] | undefined, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];

        if (optSelfValue !== undefined) {
            if(optSelfValue[1] === undefined) {
                eargs.push({ name: "this", argtype: optSelfValue[0], ref: undefined, expando: false, pcode: undefined, treg: optSelfValue[2] });
            }
            else {
                const rvname = optSelfValue[1];
                this.raiseErrorIf(sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                const earg = (env.lookupVar(rvname) as VarInfo);
                eargs.push({ name: "this", argtype: earg.declaredType, ref: new MIRParameterVariable(rvname), expando: false, pcode: undefined, treg: optSelfValue[2] });
            }
        }

        const ridx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        
        this.raiseErrorIf(sinfo, !refallowed && ((optSelfValue !== undefined && optSelfValue[1] !== undefined) || args.argList.some((arg) => arg.isRef)), "Cannot use ref params in this call position");

        //
        //TODO: we only end up doing type inference for calls that are simple (no expandos)
        //      we may want to fix this by augmenting our template type inference to do more!!!
        //

        if (noExpando) {
            let fillednames = new Set<string>();

            for (let i = 0; i < args.argList.length; ++i) {
                this.raiseErrorIf(args.argList[i].value.sinfo, args.argList[i].isRef && !refallowed, "Cannot use ref params in this call position");

                if (args.argList[i] instanceof PositionalArgument) {
                    continue;
                }
                const narg = args.argList[i] as NamedArgument;
                fillednames.add(narg.name);

                const paramIdx = sig.params.findIndex((p) => p.name === narg.name);
                this.raiseErrorIf(narg.value.sinfo, paramIdx === -1 || eargs[paramIdx] !== undefined, "Named argument does not match parameter or is multiply defined");
                const param = sig.params[paramIdx];

                const treg = this.m_emitter.generateTmpRegister();
                if (narg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(narg.value.sinfo, !(param.type instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(narg.value.sinfo, narg.isRef, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, narg.value, sigbinds, param.type as ResolvedFunctionType);
                    eargs[i] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (narg.value instanceof AccessVariableExpression && env.pcodes.has(narg.value.name)) {
                    this.raiseErrorIf(narg.value.sinfo, !(param.type instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(narg.value.sinfo, narg.isRef, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(narg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (narg.isRef) {
                        this.raiseErrorIf(narg.value.sinfo, !(narg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (narg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(narg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, narg.value, treg, param.type as ResolvedType);
                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        eargs[i] = { name: narg.name, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg };
                    }
                    else {
                        const earg = this.checkExpression(env, narg.value, treg, param.type as ResolvedType).getExpressionResult();
                        eargs[i] = { name: narg.name, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg };
                    }
                }
            }

            let sigidx = ridx;
            for (let i = 0; i < args.argList.length; ++i) {
                if (args.argList[i] instanceof NamedArgument) {
                    continue;
                }
                const parg = args.argList[i] as PositionalArgument;

                while(sigidx < sig.params.length && fillednames.has(sig.params[sigidx].name)) {
                    sigidx++;
                }

                const oftypett = (sigidx < sig.params.length) ? sig.params[sigidx].type : sig.optRestParamType;
                this.raiseErrorIf(sinfo, oftypett === undefined, "Too many parameters for call");
                const oftype = oftypett as ResolvedFunctionType | ResolvedType;

                const treg = this.m_emitter.generateTmpRegister();
                if (parg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, parg.isRef, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, parg.value, sigbinds, oftype as ResolvedFunctionType);
                    eargs[i] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (parg.value instanceof AccessVariableExpression && env.pcodes.has(parg.value.name)) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, parg.isRef, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(parg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (parg.isRef) {
                        this.raiseErrorIf(parg.value.sinfo, !(parg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (parg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(parg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, parg.value, treg, oftype as ResolvedType);
                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        eargs[i] = { name: undefined, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg };
                    }
                    else {
                        const earg = this.checkExpression(env, parg.value, treg, oftype as ResolvedType).getExpressionResult();
                        eargs[i] = { name: undefined, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg };
                    }
                }

                ++sigidx;
            }
        }
        else {
            for (let i = 0; i < args.argList.length; ++i) {
                const arg = args.argList[i];

                const treg = this.m_emitter.generateTmpRegister();

                this.raiseErrorIf(arg.value.sinfo, arg.isRef && !refallowed, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, arg.isRef && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

                if (arg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, arg.value, sigbinds, undefined);

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                    else {
                        this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                        eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                }
                else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                    this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                    else {
                        this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                        eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                    }
                }
                else {
                    if (arg.isRef) {
                        this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (arg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, arg.value, treg, undefined);
                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        if (arg instanceof NamedArgument) {
                            eargs.push({ name: arg.name, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg });
                        }
                        else {
                            eargs.push({ name: undefined, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg });
                        }
                    }
                    else {
                        if (arg instanceof NamedArgument) {
                            const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                            eargs.push({ name: arg.name, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                        }
                        else {
                            const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                            eargs.push({ name: undefined, argtype: earg.exptype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                        }
                    }
                }
            }
        }

        return eargs;
    }

    private inferAndCheckArguments(sinfo: SourceInfo, env: TypeEnvironment, args: Arguments, invk: InvokeDecl, giventerms: TypeSignature[], implicitBinds: Map<string, ResolvedType>, callBinds: Map<string, ResolvedType>, optSelfValue: [ResolvedType, string | undefined, MIRTempRegister] | undefined, refallowed: boolean): [ResolvedFunctionType, Map<string, ResolvedType>, ExpandedArgument[]] {
        const oldenable = this.m_emitter.getEmitEnabled();
        this.m_emitter.setEmitEnabled(false);
        let rrbinds = new Map<string, ResolvedType>();

        try {
            const [ibinds, iterms] = this.m_assembly.resolveBindsForCallWithInfer(invk.terms, giventerms, implicitBinds, callBinds);
            this.raiseErrorIf(sinfo, ibinds === undefined, "Template instantiation failure");

            //Do checking and infer any template params that we need
            rrbinds = ibinds as Map<string, ResolvedType>;
            if (iterms.length !== 0) {
                const fbinds = this.checkArgumentsEvaluationWSigInfer(sinfo, env, invk.params, args, optSelfValue !== undefined, rrbinds, iterms);

                const binds = this.m_assembly.resolveBindsForCallComplete(invk.terms, giventerms, implicitBinds, callBinds, fbinds);
                this.raiseErrorIf(sinfo, binds === undefined, "Call bindings could not be resolved");

                rrbinds = binds as Map<string, ResolvedType>;
            }
        }
        finally {
            this.m_emitter.setEmitEnabled(oldenable);
        }

        this.checkTemplateTypes(sinfo, invk.terms, rrbinds);

        const fsig = this.m_assembly.normalizeTypeFunction(invk.generateSig(), rrbinds);
        this.raiseErrorIf(sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(sinfo, env, fsig as ResolvedFunctionType, rrbinds, args, optSelfValue, refallowed);

        return [fsig as ResolvedFunctionType, rrbinds, eargs];
    }

    private checkArgumentsEvaluationWOperator(sinfo: SourceInfo, env: TypeEnvironment, binds: Map<string, ResolvedType>, args: Arguments, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];
        
        this.raiseErrorIf(sinfo, !refallowed && args.argList.some((arg) => arg.isRef), "Cannot use ref params in this call position");

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];

            const treg = this.m_emitter.generateTmpRegister();

            this.raiseErrorIf(arg.value.sinfo, arg.isRef && !refallowed, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.isRef && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

            if (arg.value instanceof ConstructorPCodeExpression) {
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                const pcode = this.checkPCodeExpression(env, arg.value, binds, undefined);

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else if (arg.value instanceof AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");

                const pcode = (env.pcodes.get(arg.value.name) as { pcode: PCode, captured: string[] }).pcode;

                if (arg instanceof NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Cannot have spread on pcode argument");

                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else {
                if (arg.isRef) {
                    this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                    const rvname = (arg.value as AccessVariableExpression).name;
                    this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                    this.checkExpression(env, arg.value, treg, undefined);
                    const earg = (env.lookupVar(rvname) as VarInfo);
                    const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg.declaredType, ref: refv, expando: false, pcode: undefined, treg: treg });
                    }
                }
                else {
                    if (arg instanceof NamedArgument) {
                        const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                        eargs.push({ name: arg.name, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                        eargs.push({ name: undefined, argtype: earg.exptype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                    }
                }
            }
        }

        return eargs;
    }

    private checkArgumentsEvaluationTuple(env: TypeEnvironment, args: Arguments, itype: ResolvedTupleAtomType | undefined): [ResolvedType, MIRTempRegister][] {
        let eargs: [ResolvedType, MIRTempRegister][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in tuple constructor");
            this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && i < itype.types.length) {
                etype = itype.types[i].type;
            }
            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();

            this.raiseErrorIf(arg.value.sinfo, earg.exptype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store an Epehmeral list");
            eargs.push([earg.exptype, treg]);
        }

        return eargs;
    }

    private checkArgumentsTupleConstructor(sinfo: SourceInfo, isvalue: boolean, args: [ResolvedType, MIRTempRegister][], trgt: MIRTempRegister, infertype: ResolvedType | undefined): ResolvedType {
        let targs: ResolvedType[] = [];

        for (let i = 0; i < args.length; ++i) {
            targs.push(args[i][0] as ResolvedType);
        }

        const tupleatom = ResolvedTupleAtomType.create(isvalue, targs.map((targ) => new ResolvedTupleAtomTypeEntry(targ, false)));
        const rtuple = ResolvedType.createSingle(tupleatom);

        const [restype, iipack] = this.genInferInfo(sinfo, rtuple, infertype, trgt);

        const regs = args.map((e) => e[1]);
        const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
        this.m_emitter.emitConstructorTuple(sinfo, tupkey, regs, iipack[0]);

        this.emitConvertIfNeeded(sinfo, rtuple, infertype, iipack);
        return restype;
    }

    private checkArgumentsEvaluationRecord(env: TypeEnvironment, args: Arguments, itype: ResolvedRecordAtomType | undefined): [string, ResolvedType, MIRTempRegister][] {
        let eargs: [string, ResolvedType, MIRTempRegister][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof NamedArgument), "Only named arguments allowed in record constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && itype.entries.findIndex((entry) => entry.name === (arg as NamedArgument).name) !== -1) {
                etype = (itype.entries.find((entry) => entry.name === (arg as NamedArgument).name) as ResolvedRecordAtomTypeEntry).type;
            }
            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();

            this.raiseErrorIf(arg.value.sinfo, earg.exptype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store an Epehmeral list");
            eargs.push([(arg as NamedArgument).name, earg.exptype, treg]);
        }

        return eargs;
    }

    private checkArgumentsRecordConstructor(sinfo: SourceInfo, isvalue: boolean, args: [string, ResolvedType, MIRTempRegister][], trgt: MIRTempRegister, infertype: ResolvedType | undefined): ResolvedType {
        let rargs: [string, ResolvedType][] = [];

        const seenNames = new Set<string>();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, seenNames.has(args[i][0] as string), "Duplicate argument name in Record constructor");

            rargs.push([args[i][0] as string, args[i][1] as ResolvedType]);
        }

        const rentries = rargs.map((targ) => new ResolvedRecordAtomTypeEntry(targ[0], targ[1], false));
        const recordatom = ResolvedRecordAtomType.create(isvalue, rentries);
        const rrecord = ResolvedType.createSingle(recordatom);

        const [restype, iipack] = this.genInferInfo(sinfo, rrecord, infertype, trgt);

        const regs = args.map<[string, MIRTempRegister]>((e) => [e[0] as string, e[2]]).sort((a, b) => a[0].localeCompare(b[0]));
        const regkey = this.m_emitter.registerResolvedTypeReference(rrecord);
        this.m_emitter.emitConstructorRecord(sinfo, regkey, regs, iipack[0]);

        this.emitConvertIfNeeded(sinfo, rrecord, infertype, iipack);

        return restype;
    }

    private checkArgumentsEvaluationValueList(env: TypeEnvironment, args: Arguments, itype: ResolvedEphemeralListType | undefined): [ResolvedType, MIRTempRegister][] {
        let eargs: [ResolvedType, MIRTempRegister][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

            this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in tuple constructor");
            this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple constructor");

            const treg = this.m_emitter.generateTmpRegister();
            let etype: ResolvedType | undefined = undefined;
            if(itype !== undefined && i < itype.types.length) {
                etype = itype.types[i];
            }
            const earg = this.checkExpression(env, arg.value, treg, etype).getExpressionResult();

            this.raiseErrorIf(arg.value.sinfo, earg.exptype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store an Epehmeral list");
            eargs.push([earg.exptype, treg]);
        }

        return eargs;
    }

    private checkArgumentsValueListConstructor(sinfo: SourceInfo, args: [ResolvedType, MIRTempRegister][], trgt: MIRTempRegister, infertype: ResolvedType | undefined): ResolvedType {
        let targs: ResolvedType[] = [];

        for (let i = 0; i < args.length; ++i) {
            targs.push(args[i][0] as ResolvedType);
        }

        const vlatom = ResolvedEphemeralListType.create(targs);
        const rvl = ResolvedType.createSingle(vlatom);

        const [restype, iipack] = this.genInferInfo(sinfo, rvl, infertype, trgt);

        const regs = args.map((e) => e[1]);
        const vlkey = this.m_emitter.registerResolvedTypeReference(rvl);
        this.m_emitter.emitConstructorValueList(sinfo, vlkey, regs, iipack[0]);

        this.emitConvertIfNeeded(sinfo, rvl, infertype, iipack);

        return restype;
    }

    private getExpandoType(sinfo: SourceInfo, eatom: ResolvedEntityAtomType): ResolvedType {
        const ep = this.m_assembly.getExpandoProvides(eatom.object, eatom.binds);
        this.raiseErrorIf(sinfo, ep === undefined, "Not an expandoable type");

        return ep as ResolvedType;
    }

    private checkArgumentsEvaluationCollection(env: TypeEnvironment, args: Arguments, contentstype: ResolvedType): [ResolvedType, boolean, MIRTempRegister][] {
        let eargs: [ResolvedType, boolean, MIRTempRegister][] = [];

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg instanceof NamedArgument, "Cannot use named arguments in constructor");

            const treg = this.m_emitter.generateTmpRegister();
            if ((arg as PositionalArgument).isSpread) {
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().exptype;
                eargs.push([earg, true, treg]);
            }
            else {
                const earg = this.checkExpression(env, arg.value, treg, contentstype).getExpressionResult().exptype;
                eargs.push([earg, false, treg]);
            }
        }

        return eargs;
    }

    private checkExpandoType(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, argtype: ResolvedType): boolean {
        const oftexpando = this.getExpandoType(sinfo, oftype);
        const oftexpandoT = (oftexpando.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;

        this.raiseErrorIf(sinfo, argtype.options.length !== 1, "Must be unique type to use in collection expando");
        const opt = argtype.options[0];
            
        this.raiseErrorIf(sinfo, !(opt instanceof ResolvedEntityAtomType), "Can only expand other container types in container constructor");
        this.raiseErrorIf(sinfo, !(opt as ResolvedEntityAtomType).object.isTypeAnExpandoableCollection(), "Can only expand other container types in container constructor");
            
        const texpando = this.getExpandoType(sinfo, opt as ResolvedEntityAtomType);
        const texpandoT = (texpando.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;

        return texpandoT.isSameType(oftexpandoT);
    }

    private checkArgumentsCollectionConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, entrytype: ResolvedType, args: [ResolvedType, boolean, MIRTempRegister][], trgt: MIRTempRegister, infertype: ResolvedType | undefined, generatekeylistT: string | undefined): ResolvedType {
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];

            if (!arg[1]) {
                this.raiseErrorIf(sinfo, !arg[0].isSameType(entrytype));
            }
            else {
                this.raiseErrorIf(sinfo, !this.checkExpandoType(sinfo, oftype, arg[0]), "Container contents not of matching expando type");
            }
        }

        const resulttype = ResolvedType.createSingle(oftype);
        const [restype, iipack] = this.genInferInfo(sinfo, resulttype, infertype, trgt);

        if (generatekeylistT !== undefined && this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::KeyList") !== undefined) {
            const klobj = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::KeyList") as EntityTypeDecl;
            const klbinds = new Map<string, ResolvedType>().set("K", oftype.binds.get(generatekeylistT) as ResolvedType);
            const kltype = ResolvedType.createSingle(ResolvedEntityAtomType.create(klobj, klbinds));
            this.m_emitter.registerResolvedTypeReference(kltype);
        }

        const tkey = this.m_emitter.registerResolvedTypeReference(resulttype).trkey;
        this.m_emitter.registerResolvedTypeReference(entrytype);
        if (args.length === 0) {
            this.m_emitter.emitConstructorPrimaryCollectionEmpty(sinfo, tkey, iipack[0]);
        }
        else {
            if (args.every((v) => !v[1])) {
                this.m_emitter.emitConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map((arg) => arg[2]), iipack[0]);
            }
            else if (args.every((v) => v[1])) {
                if(args.length === 1 && args[0][0].isSameType(resulttype)) {
                    //special case where we expand a (say) List<Int> into a List<Int>
                    this.m_emitter.emitTempRegisterAssign(sinfo, args[0][2], iipack[0]);
                }
                else {
                    this.m_emitter.emitConstructorPrimaryCollectionCopies(sinfo, tkey, args.map((arg) => arg[2]), iipack[0]);
                }
            }
            else {
                this.m_emitter.emitConstructorPrimaryCollectionMixed(sinfo, tkey, args.map<[boolean, MIRArgument]>((arg) => [arg[1], arg[2]]), iipack[0]);
            }
        }

        this.emitConvertIfNeeded(sinfo, resulttype, infertype, iipack);

        return restype;
    }

    private checkArgumentsEvaluationEntity(sinfo: SourceInfo, env: TypeEnvironment, oftype: ResolvedEntityAtomType, args: Arguments): ExpandedArgument[] {
        const fieldinfo = [...this.m_assembly.getAllOOFields(oftype.object, oftype.binds)];
        let eargs: ExpandedArgument[] = [];

        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        if (noExpando) {
            let fillednames = new Set<string>();
            for (let i = 0; i < args.argList.length; ++i) {
                this.raiseErrorIf(args.argList[i].value.sinfo, args.argList[i].isRef, "Cannot use ref params in this call position");

                if (args.argList[i] instanceof PositionalArgument) {
                    continue;
                }
                const narg = args.argList[i] as NamedArgument;
                fillednames.add(narg.name);

                const fieldIdx = fieldinfo.findIndex((p) => p[0] === narg.name);
                this.raiseErrorIf(narg.value.sinfo, fieldIdx === -1 || eargs[fieldIdx] !== undefined, "Named argument does not match any field name or is multiply defined");
                const field = fieldinfo[fieldIdx];
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, field[1][1].declaredType, field[1][2]);

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, narg.value, treg, ftype).getExpressionResult();
                eargs[i] = { name: narg.name, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg };
            }

            let fidx = 0;
            for (let i = 0; i < args.argList.length; ++i) {
                if (args.argList[i] instanceof NamedArgument) {
                    continue;
                }
                const parg = args.argList[i] as PositionalArgument;

                while (fidx < fieldinfo.length && fillednames.has(fieldinfo[i][0])) {
                    fidx++;
                }

                const field = fieldinfo[fidx];
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, field[1][1].declaredType, field[1][2]);

                const treg = this.m_emitter.generateTmpRegister();

                const earg = this.checkExpression(env, parg.value, treg, ftype).getExpressionResult();
                eargs[i] = { name: undefined, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg };

                ++fidx;
            }
        }
        else {
            for (let i = 0; i < args.argList.length; ++i) {
                const arg = args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");

                const treg = this.m_emitter.generateTmpRegister();

                if (arg instanceof NamedArgument) {
                    const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                    eargs.push({ name: arg.name, argtype: earg.exptype, ref: undefined, expando: false, pcode: undefined, treg: treg });
                }
                else {
                    const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult();
                    eargs.push({ name: undefined, argtype: earg.exptype, ref: undefined, expando: (arg as PositionalArgument).isSpread, pcode: undefined, treg: treg });
                }
            }
        }

        return eargs;
    }

    private checkArgumentsEntityConstructor(sinfo: SourceInfo, oftype: ResolvedEntityAtomType, args: ExpandedArgument[], trgt: MIRTempRegister, infertype: ResolvedType | undefined): ResolvedType {
        const fieldInfo = this.m_assembly.getAllOOFields(oftype.object, oftype.binds);
        const flatfinfo = [...fieldInfo];
        let fields: string[] = [];
        fieldInfo.forEach((v, k) => {
            fields.push(k);
        });

        const optcount = flatfinfo.filter((fi) => fi[1][1].value !== undefined).length;
        const optfirst = flatfinfo.findIndex((fi) => fi[1][1].value !== undefined);
        const fflag = this.m_emitter.emitHasFlagLocation(oftype.object.name, optcount);

        let filledLocations: { vtype: ResolvedType, mustDef: boolean, fflagchk: boolean, trgt: MIRArgument }[] = [];

        //figure out named parameter mapping first
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                filledLocations[fidx] = { vtype: arg.argtype as ResolvedType, mustDef: true, fflagchk: false, trgt: arg.treg };
                if(flatfinfo[fidx][1][1].value !== undefined) {
                    this.m_emitter.emitSetHasFlagConstant(fflag, fidx - optfirst, true);
                }
            }
            else if (arg.expando && (arg.argtype as ResolvedType).isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);

                expandInfo[1].forEach((pname) => {
                    const fidx = fields.indexOf(pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, (fieldInfo.get(pname) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>])[1].value !== undefined && !expandInfo[0].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromSafeProperty(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if(expandInfo[0].has(pname)) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[fidx][1];
                        this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[fidx]}" is required and must be assigned a value in constructor`);

                        this.m_emitter.emitCheckedLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: false, fflagchk: true, trgt: etreg };
                    }
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ResolvedType).isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < fields.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional field "${fields[ii]}"`);
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype as ResolvedType, mustDef: true, fflagchk: false, trgt: arg.treg };
                if(flatfinfo[ii][1][1].value !== undefined) {
                    this.m_emitter.emitSetHasFlagConstant(fflag, ii - optfirst, true);
                }
                
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ResolvedType).isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype as ResolvedType);

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= fields.length, "Too many arguments as part of tuple expando");
                    this.raiseErrorIf(sinfo, (fieldInfo.get(fields[ii]) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>])[1].value !== undefined && ectr >= expandInfo[0], `Constructor requires "${fields[ii]}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if(ectr < expandInfo[0]) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: lvtype, mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[ii][1];
                        this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[ii]}" is required and must be assigned a value in constructor`);

                        this.m_emitter.emitCheckedLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
                        filledLocations[ii] = { vtype: lvtype, mustDef: false, fflagchk: true, trgt: etreg };
                    }

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional field "${fields[ii]}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ResolvedType).isRecordTargetType()))) {
                apos++;
            }
        }

        //go through arguments and type coearce as needed
        let cargs: MIRArgument[] = [];
        for (let i = 0; i < fields.length; ++i) {
            const field = (fieldInfo.get(fields[i]) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]);
            const fieldtype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);

            if(filledLocations[i].fflagchk) {
                cargs.push(this.emitCheckedInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype, fflag, i - optfirst));
            }
            else {
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype));
            }
        }

        const constype = ResolvedType.createSingle(oftype);
        const rtype = this.m_emitter.registerResolvedTypeReference(constype);
        const [restype, iipack] = this.genInferInfo(sinfo, constype, infertype, trgt);

        const ikey = MIRKeyGenerator.generateFunctionKey(MIRKeyGenerator.generateTypeKey(constype), "@@constructor", new Map<string, ResolvedType>(), []);
        this.m_emitter.emitInvokeFixedFunction(sinfo, ikey, cargs, fflag, rtype, iipack[0]);

        this.emitConvertIfNeeded(sinfo, constype, infertype, iipack);
        return restype;
    }

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, name: string, sig: ResolvedFunctionType, args: ExpandedArgument[]): { args: MIRArgument[], types: ResolvedType[], fflag: string, refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        const optcount = sig.params.filter((p) => p.isOptional).length;
        const optfirst = sig.params.findIndex((p) => p.isOptional);
        const fflag = this.m_emitter.emitHasFlagLocation(name, optcount);

        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = sig.params.findIndex((param) => param.name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                if(sig.params[fidx].isOptional) {
                    this.m_emitter.emitSetHasFlagConstant(fflag, fidx - optfirst, true);
                }
            }
            else if (arg.expando && (arg.argtype as ResolvedType).isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);

                expandInfo[1].forEach((pname) => {
                    const fidx = sig.params.findIndex((param) => param.name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    this.raiseErrorIf(sinfo, !sig.params[fidx].isOptional && !expandInfo[0].has(pname), `Call requires "${pname}" but it is provided as an optional argument`);


                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromSafeProperty(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if(expandInfo[0].has(pname)) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[fidx];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitCheckedLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ResolvedType).isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < sig.params.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                if(sig.params[ii].isOptional) {
                    this.m_emitter.emitSetHasFlagConstant(fflag, ii - optfirst, true);
                }

                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ResolvedType).isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype as ResolvedType);

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= sig.params.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    this.raiseErrorIf(sinfo, !sig.params[ii].isOptional && ectr >= expandInfo[0], `Call requires "${sig.params[ii].name}" but it is provided as an optional argument as part of tuple expando`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if(ectr < expandInfo[0]) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[ii];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitCheckedLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
                        filledLocations[ii] = { vtype: lvtype, mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: etreg };
                    }

                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ResolvedType).isRecordTargetType()))) {
                apos++;
            }
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ResolvedType).isRecordTargetType()))) {
            apos++;
        }

        if (ii < sig.params.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${sig.params[ii].name}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let mtypes: ResolvedType[] = [];
        let pcodes: PCode[] = [];
        let refs: MIRVariableArgument[] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;

            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                this.m_emitter.emitSetHasFlagConstant(fflag, j - optfirst, false);

                const etreg = this.m_emitter.generateTmpRegister();
                filledLocations[j] = { vtype: paramtype, mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: etreg };
            }

            if (sig.params[j].type instanceof ResolvedFunctionType) {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode === undefined, `Parameter ${sig.params[j].name} expected a function`);
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype as ResolvedFunctionType, paramtype as ResolvedFunctionType), `Parameter ${sig.params[j].name} expected function of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);

                if (sig.params[j].isRef) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, (filledLocations[j].vtype as ResolvedType).idStr !== (paramtype as ResolvedType).idStr, `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                    refs.push(filledLocations[j].ref as MIRVariableArgument);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype as ResolvedType, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                }


                let narg = filledLocations[j].trgt;
                if(filledLocations[j].fflagchk) {
                    narg = this.emitCheckedInlineConvertIfNeeded(sinfo, filledLocations[j].trgt, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType, fflag, j - optfirst);
                }
                else {
                    narg = this.emitInlineConvertIfNeeded(sinfo, filledLocations[j].trgt, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType);
                }

                margs.push(narg);
                mtypes.push(sig.params[j].type as ResolvedType);
            }
        }

        //if this has a rest parameter check it
        if (sig.optRestParamType !== undefined) {
            const objtype = ResolvedType.tryGetOOTypeInfo(sig.optRestParamType);
            this.raiseErrorIf(sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid rest type");

            const oodecl = (objtype as ResolvedEntityAtomType).object;
            const oobinds = (objtype as ResolvedEntityAtomType).binds;
            const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);

            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);
            const cargs = rargs.map((ca) => [ca.argtype, ca.expando, ca.treg] as [ResolvedType, boolean, MIRTempRegister]);

            const etype = oodecl.specialDecls.has(SpecialTypeCategory.MapTypeDecl) 
                ? ResolvedType.createSingle(ResolvedTupleAtomType.create(true, [new ResolvedTupleAtomTypeEntry(oobinds.get("K") as ResolvedType, false), new ResolvedTupleAtomTypeEntry(oobinds.get("V") as ResolvedType, false)]))
                : oobinds.get("T") as ResolvedType;

            let genkl: string | undefined = undefined;
            if(oodecl.specialDecls.has(SpecialTypeCategory.SetTypeDecl)) {
                genkl = "T";
            } 
            else if (oodecl.specialDecls.has(SpecialTypeCategory.MapTypeDecl)) {
                genkl = "K";
            }
            else {
                //nothing
            }

            const rtreg = this.m_emitter.generateTmpRegister();
            this.checkArgumentsCollectionConstructor(sinfo, oftype, etype, cargs, rtreg, sig.optRestParamType, genkl);

            margs.push(rtreg);
            mtypes.push(ResolvedType.createSingle(oftype));
        }

        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set<string>();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));

            const cnames = [...allcaptured].sort();
            for (let i = 0; i < cnames.length; ++i) {
                const vinfo = env.lookupVar(cnames[i]);
                if(vinfo === null) {
                    //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                    const tinfo = env.lookupVar("this") as VarInfo;
                    margs.push(new MIRParameterVariable("this"));
                    mtypes.push(tinfo.flowType);

                    cinfo.push([cnames[i], tinfo.flowType]);
                }
                else {
                    if(env.getLocalVarInfo(cnames[i]) !== undefined) {
                        margs.push(new MIRLocalVariable(cnames[i]));
                    }
                    else {
                        margs.push(new MIRParameterVariable(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    }
                    mtypes.push(vinfo.flowType);

                    cinfo.push([cnames[i], vinfo.flowType]);
                }
            }
        }

        return { args: margs, types: mtypes, fflag: fflag, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }

    private checkArgumentsWOperator(sinfo: SourceInfo, env: TypeEnvironment, opnames: string[], hasrest: boolean, args: ExpandedArgument[]): { args: MIRArgument[], types: ResolvedType[], refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = opnames.findIndex((name) => name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
            }
            else if (arg.expando && (arg.argtype as ResolvedType).isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, expandInfo[0].size !== expandInfo[1].size, "Cannot have optional arguments on operator");

                expandInfo[1].forEach((pname) => {
                    const fidx = opnames.findIndex((name) => name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromSafeProperty(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                    filledLocations[fidx] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                });
            }
            else {
                //nop
            }
        }

        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && (ae.argtype as ResolvedType).isRecordTargetType()));
        if (apos === -1) {
            apos = args.length;
        }

        let ii = 0;
        while (ii < opnames.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                ++ii;
                continue;
            }

            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, fflagchk: false, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ResolvedType).isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, expandInfo[0] !== expandInfo[1], "Cannot have optional arguments on operator");

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= opnames.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    
                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromSafeIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                    filledLocations[ii] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };

                    while (filledLocations[ii] !== undefined) {
                        ii++;
                    }
                }
            }

            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ResolvedType).isRecordTargetType()))) {
                apos++;
            }
        }

        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && (args[apos].argtype as ResolvedType).isRecordTargetType()))) {
            apos++;
        }

        this.raiseErrorIf(sinfo, ii < opnames.length, `Insufficient number of parameters -- missing value for ${opnames[ii]}`);
        this.raiseErrorIf(sinfo, !hasrest && apos !== args.length, "Too many arguments for operator");
        
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let mtypes: ResolvedType[] = [];
        let pcodes: PCode[] = [];
        let refs: MIRVariableArgument[] = [];
        for (let j = 0; j < opnames.length; ++j) {
            this.raiseErrorIf(sinfo, filledLocations[j] === undefined, `Parameter ${opnames[j]} was not provided`);

            if (filledLocations[j].vtype instanceof ResolvedFunctionType) {
                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${opnames[j]} cannot take a function`);

                if (filledLocations[j].ref !== undefined) {
                    refs.push(filledLocations[j].ref as MIRVariableArgument);
                }

                margs.push(filledLocations[j].trgt);
                mtypes.push(filledLocations[j].vtype as ResolvedType);
            }
        }

        //if this has a rest parameter check it
        if (hasrest) {
            //
            //TODO: we may want to distinguish List, Set, Map options
            //
            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);
            const cargs = rargs.map((ca) => [ca.argtype, ca.expando, ca.treg] as [ResolvedType, boolean, MIRTempRegister]);

            const etype = this.m_assembly.typeUpperBound(cargs.map((aa) => {
                if(!aa[1]) {
                    return aa[0];
                }
                else {
                    this.raiseErrorIf(sinfo, aa[0].isUniqueCallTargetType(), "Expected unique expandoable collection type in expando position");

                    const oftexpando = this.getExpandoType(sinfo, aa[0].getUniqueCallTargetType());
                    return ResolvedType.createSingle(oftexpando);
                }
            }));

            const lentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::List") as EntityTypeDecl;
            const oftype = ResolvedEntityAtomType.create(lentity, new Map<string, ResolvedType>().set("T", etype));

            const rtreg = this.m_emitter.generateTmpRegister();
            this.checkArgumentsCollectionConstructor(sinfo, oftype, etype, cargs, rtreg, undefined, undefined);

            margs.push(rtreg);
            mtypes.push(ResolvedType.createSingle(oftype));
        }

        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo: [string, ResolvedType][] = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set<string>();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));

            const cnames = [...allcaptured].sort();
            for (let i = 0; i < cnames.length; ++i) {
                const vinfo = env.lookupVar(cnames[i]);
                if(vinfo === null) {
                    //This is the first place we capture $$this_captured so we sould pass "this" as the arg for it
                    const tinfo = env.lookupVar("this") as VarInfo;
                    margs.push(new MIRParameterVariable("this"));
                    mtypes.push(tinfo.flowType);

                    cinfo.push([cnames[i], tinfo.flowType]);
                }
                else {
                    if(env.getLocalVarInfo(cnames[i]) !== undefined) {
                        margs.push(new MIRLocalVariable(cnames[i]));
                    }
                    else {
                        margs.push(new MIRParameterVariable(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    }
                    mtypes.push(vinfo.flowType);

                    cinfo.push([cnames[i], vinfo.flowType]);
                }
            }
        }

        return { args: margs, types: mtypes, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }

    private generateExpandedReturnSig(sinfo: SourceInfo, declaredType: ResolvedType, params: FunctionParameter[], binds: Map<string, ResolvedType>): MIRType {
        const rtype = this.m_emitter.registerResolvedTypeReference(declaredType);
        const rr = params.filter((fp) => fp.isRef).map((fp) => this.resolveAndEnsureTypeOnly(sinfo, fp.type, binds));
        const refinfo = rr.map((fpt) => this.m_emitter.registerResolvedTypeReference(fpt));

        if (refinfo.length === 0) {
            return rtype;
        }
        else {
            
            if (rtype.options.length !== 1 || !(rtype.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([declaredType, ...rr]));

                return this.m_emitter.registerResolvedTypeReference(etl);
            }
            else {
                const elr = declaredType.options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return this.m_emitter.registerResolvedTypeReference(etl);
            }
        }
    }

    private generateRefInfoForCallEmit(fsig: ResolvedFunctionType, refs: MIRVariableArgument[]): [MIRType, MIRType, number, [MIRVariableArgument, MIRType][]] {
        const rtype = this.m_emitter.registerResolvedTypeReference(fsig.resultType); 
        const refinfo = refs.map((rn) => {
            const rp = fsig.params.find((p) => p.name === rn.lname);
            const ptk = this.m_emitter.registerResolvedTypeReference((rp as ResolvedFunctionTypeParam).type as ResolvedType);
            return [rn, ptk] as [MIRVariableArgument, MIRType];
        });

        if (refinfo.length === 0) {
            return [rtype, rtype, -1, refinfo];
        }
        else {
            const rr = refs.map((rn) => (fsig.params.find((p) => p.name === rn.lname) as ResolvedFunctionTypeParam).type as ResolvedType);

            if (fsig.resultType.options.length !== 1 || !(fsig.resultType.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([fsig.resultType, ...rr]));

                return [rtype, this.m_emitter.registerResolvedTypeReference(etl), -1, refinfo];
            }
            else {
                const elr = fsig.resultType.options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return [rtype, this.m_emitter.registerResolvedTypeReference(etl), elr.types.length, refinfo];
            }
        }
    }

    private generateRefInfoForReturnEmit(sinfo: SourceInfo, inferrtype: ResolvedType, env: TypeEnvironment): [MIRType, MIRType, number, [string, MIRType][]] {
        if(!this.m_emitter.getEmitEnabled()) {
            return [this.m_emitter.registerResolvedTypeReference(this.m_emitter.assembly.getSpecialNoneType()), this.m_emitter.registerResolvedTypeReference(this.m_emitter.assembly.getSpecialNoneType()), -1, []];
        }

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(inferrtype, env.inferResult as ResolvedType), "Return value does not match the declared return type");

        const rtype = this.m_emitter.registerResolvedTypeReference(env.returnResult as ResolvedType);
        const refinfo = env.refparams.map((rn) => {
            const ptk = this.m_emitter.registerResolvedTypeReference((env.lookupVar(rn) as VarInfo).declaredType);
            return [rn, ptk] as [string, MIRType];
        });

        if (refinfo.length === 0) {
            return [rtype, rtype, -1, []];
        }
        else {
            const rr = env.refparams.map((rn) => (env.lookupVar(rn) as VarInfo).declaredType);
            if (rtype.options.length !== 1 || !(rtype.options[0] instanceof ResolvedEphemeralListType)) {
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([env.returnResult as ResolvedType, ...rr]));

                return [rtype, this.m_emitter.registerResolvedTypeReference(etl), -1, refinfo];
            }
            else {
                const elr = (env.returnResult as ResolvedType).options[0] as ResolvedEphemeralListType;
                const etl = ResolvedType.createSingle(ResolvedEphemeralListType.create([...elr.types, ...rr]));

                return [rtype, this.m_emitter.registerResolvedTypeReference(etl), elr.types.length, refinfo];
            }
        }
    }

    private checkLiteralNoneExpression(env: TypeEnvironment, exp: LiteralNoneExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, trgt);

        this.m_emitter.emitLoadConstNone(exp.sinfo, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralBoolExpression(env: TypeEnvironment, exp: LiteralBoolExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

        this.m_emitter.emitLoadConstBool(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
        return [env.setResultExpression(restype, exp.value ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
    }

    private checkLiteralIntegerExpression(env: TypeEnvironment, exp: LiteralIntegerExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialIntType(), infertype, trgt);

        this.m_emitter.emitLoadConstInt(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialIntType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralNatExpression(env: TypeEnvironment, exp: LiteralNaturalExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialNatType(), infertype, trgt);

        this.m_emitter.emitLoadConstInt(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialNatType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralBigIntExpression(env: TypeEnvironment, exp: LiteralBigIntegerExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBigIntType(), infertype, trgt);

        this.m_emitter.emitLoadConstBigInt(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBigIntType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralBigNatExpression(env: TypeEnvironment, exp: LiteralBigNaturalExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBigNatType(), infertype, trgt);

        this.m_emitter.emitLoadConstBigNat(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBigNatType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralRationalExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialRationalType(), infertype, trgt);

        this.m_emitter.emitLoadConstRational(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialRationalType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralFloatExpression(env: TypeEnvironment, exp: LiteralFloatExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialFloatType(), infertype, trgt);

        this.m_emitter.emitLoadConstFloat(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialFloatType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralDecimalExpression(env: TypeEnvironment, exp: LiteralDecimalExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialDecimalType(), infertype, trgt);

        this.m_emitter.emitLoadConstDecimal(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialDecimalType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralStringExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialStringType(), infertype, trgt);

        this.m_emitter.emitLoadConstString(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialStringType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialRegexType(), infertype, trgt);

        this.m_emitter.emitLoadLiteralRegex(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialRegexType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkStringOfCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType } {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        this.raiseErrorIf(sinfo, !oftype.isUniqueCallTargetType() || !oftype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl), "Validator type must be a unique type");
        
        const aoftype = ResolvedType.tryGetOOTypeInfo(oftype);
        const oodecl = (aoftype as ResolvedEntityAtomType).object;
        const oobinds = (aoftype as ResolvedEntityAtomType).binds;

        //ensure full string<T> type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new NominalTypeSignature("NSCore", ["StringOf"], terms), binds);

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype };
    }

    private checkDataStringCommon(sinfo: SourceInfo, env: TypeEnvironment, ttype: TypeSignature): { oftype: [OOPTypeDecl, Map<string, ResolvedType>], ofresolved: ResolvedType, stringtype: ResolvedType, parsetype: ResolvedType } {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        this.raiseErrorIf(sinfo, oftype.options.length !== 1, "Cannot have union of parsable types");
        this.raiseErrorIf(sinfo, oftype.options[0] instanceof ResolvedConceptAtomType && (oftype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1, "Cannot have & of concepts");
        
        const aoftype = oftype.options[0];
        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

        const fdecltry = oodecl.staticFunctions.get("tryParse");
        this.raiseErrorIf(sinfo, fdecltry === undefined, `Constant value not defined for type '${oftype.idStr}'`);

        //ensure full DataString<T> type is registered
        const terms = [new TemplateTypeSignature("T")];
        const binds = new Map<string, ResolvedType>().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new NominalTypeSignature("NSCore", ["DataString"], terms), binds);

        const frbinds = this.m_assembly.resolveBindsForCallComplete([], [], binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
        const ptype = this.resolveAndEnsureTypeOnly(sinfo, (fdecltry as StaticFunctionDecl).invoke.resultType, frbinds);

        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype, parsetype: ptype };
    }

    private checkCreateTypedString(env: TypeEnvironment, exp: LiteralTypedStringExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);
        this.raiseErrorIf(exp.sinfo, !oftype.isUniqueCallTargetType(), "Type must be a unique type");
        
        if(oftype.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.ValidatorTypeDecl)) {
            const aoftype = this.checkStringOfCommon(exp.sinfo, env, exp.stype);
    
            const sdecl = aoftype.oftype[0].staticFunctions.get("accepts");
            assert(sdecl !== undefined);

            const vv = this.m_assembly.tryGetValidatorForFullyResolvedName(oftype.idStr);
            this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${oftype.idStr}`);
            
            const argstr = unescapeLiteralString(exp.value.substring(1, exp.value.length - 1));
            const mtch = new RegExp((vv as BSQRegex).compileToJS()).exec(argstr);
            this.raiseErrorIf(exp.sinfo, mtch === null || mtch[0].length !== argstr.length, "Literal string failed Validator regex");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, aoftype.stringtype, infertype, trgt);
            this.m_emitter.emitLoadLiteralStringOf(exp.sinfo, exp.value, stype.trkey, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, aoftype.stringtype, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else {
            const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);
            const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
            this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");

            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);

            if (this.m_doLiteralStringValidate) {
                const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);

                const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
                const skey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl as StaticFunctionDecl, "tryParse", sbinds, [], []);

                const tmps = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);

                const tmpokt = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, ResultCheckCategory.ErrChk, tmpokt);
                this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);
            }
            
            const [restype, iipack] = this.genInferInfo(exp.sinfo, aoftype.stringtype, infertype, trgt);
            this.m_emitter.emitLoadConstDataString(exp.sinfo, exp.value, stype.trkey, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, aoftype.stringtype, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkDataStringConstructor(env: TypeEnvironment, exp: LiteralTypedStringConstructorExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const aoftype = this.checkDataStringCommon(exp.sinfo, env, exp.stype);

        const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
        this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");

        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(this.getResultBinds(aoftype.parsetype).T) !== exp.isvalue, "Mismatch in storage layout decl and call");

        const presult = this.m_emitter.registerResolvedTypeReference(aoftype.parsetype);
        const rok = this.m_emitter.registerResolvedTypeReference(this.getResultSubtypes(aoftype.parsetype)[0]);

        const sbinds = this.m_assembly.resolveBindsForCallComplete([], [], (aoftype.stringtype.options[0] as ResolvedEntityAtomType).binds, new Map<string, ResolvedType>(), new Map<string, ResolvedType>()) as Map<string, ResolvedType>;
        const skey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl as StaticFunctionDecl, "tryParse", sbinds, [], []);

        const tmps = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [new MIRConstantString(exp.value)], undefined, presult, tmps);

        const tmpokt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, ResultCheckCategory.ErrChk, tmpokt);
        this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);

        const convt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitConvertDown(exp.sinfo, presult, rok, tmps, convt);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, aoftype.stringtype, infertype, trgt);
        this.m_emitter.emitExtractResult(exp.sinfo, convt, rok, iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, this.getResultBinds(aoftype.parsetype).T, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessNamespaceConstant(env: TypeEnvironment, exp: AccessNamespaceConstantExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>());
        const gkey = this.m_emitter.registerPendingGlobalProcessing(cdecl);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, rtype, infertype, trgt);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, gkey, [], undefined, this.m_emitter.registerResolvedTypeReference(rtype), iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, rtype, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetConstMemberUniqueDeclFromType(oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined (or not uniquely defined) for type '${oftype.idStr}'`);

        const cdecl = cdecltry as OOMemberLookupInfo<StaticMemberDecl>;
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.decl.declaredType, cdecl.binds);

        const skey = this.m_emitter.registerPendingConstProcessing(cdecl.contiainingType, cdecl.decl, cdecl.binds);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, rtype, infertype, trgt);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [], undefined, this.m_emitter.registerResolvedTypeReference(rtype), iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, rtype, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");

        if (infertype === undefined || this.m_assembly.subtypeOf(vinfo.flowType, infertype)) {
            const totype = infertype || vinfo.flowType;

            if (env.getLocalVarInfo(exp.name) !== undefined) {
                this.emitAssignToTempAndConvertIfNeeded_KnownSafe(exp.sinfo, vinfo.declaredType, totype, new MIRLocalVariable(exp.name), trgt);
            }
            else {
                if ((env.lookupVar(exp.name) as VarInfo).isCaptured) {
                    this.emitAssignToTempAndConvertIfNeeded_KnownSafe(exp.sinfo, vinfo.declaredType, totype, new MIRParameterVariable(this.m_emitter.generateCapturedVarName(exp.name)), trgt);
                }
                else {
                    this.emitAssignToTempAndConvertIfNeeded_KnownSafe(exp.sinfo, vinfo.declaredType, totype, new MIRParameterVariable(exp.name), trgt);
                }
            }

            return [env.setResultExpressionWVarOptNoInfer(totype, exp.name, vinfo.truthval)];
        }
        else {
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(vinfo.declaredType, infertype), "Cannot converet valiable to needed type");
            const dtype = this.m_emitter.registerResolvedTypeReference(vinfo.declaredType);
            const itype = this.m_emitter.registerResolvedTypeReference(infertype);

            //aways need to convert otherwise the if case should be taken
            if (env.getLocalVarInfo(exp.name) !== undefined) {
                this.m_emitter.emitConvertUp(exp.sinfo, dtype, itype, new MIRLocalVariable(exp.name), trgt);
            }
            else {
                if ((env.lookupVar(exp.name) as VarInfo).isCaptured) {
                    this.m_emitter.emitConvertUp(exp.sinfo, dtype, itype, new MIRParameterVariable(this.m_emitter.generateCapturedVarName(exp.name)), trgt);
                }
                else {
                    this.m_emitter.emitConvertUp(exp.sinfo, dtype, itype, new MIRParameterVariable(exp.name), trgt);
                }
            }

            return [env.setResultExpressionWVarOptNoInfer(infertype, exp.name, vinfo.truthval)];
        }
    }

    private checkConstructorPrimary(env: TypeEnvironment, exp: ConstructorPrimaryExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");
        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(ctype) === exp.isvalue, "Mismatch in storage layout decl and call");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isTypeAListEntity() || oodecl.isTypeAStackEntity() || oodecl.isTypeAQueueEntity()) {
            const ctype = oobinds.get("T") as ResolvedType;
            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt, infertype, undefined);

            return [env.setResultExpression(atype)];
        }
        else if (oodecl.isTypeASetEntity()) {
            const ctype = oobinds.get("T") as ResolvedType;
            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, ctype);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, ctype, eargs, trgt, infertype, "T");

            return [env.setResultExpression(atype)];
        }
        else if (oodecl.isTypeAMapEntity()) {
            const entrytuple = new TupleTypeSignature(true, [[new TemplateTypeSignature("K"), false], [new TemplateTypeSignature("K"), false]]);
            const entrybinds = new Map<string, ResolvedType>().set("K", oobinds.get("K") as ResolvedType).set("V", oobinds.get("V") as ResolvedType);
            const entryobj = this.resolveAndEnsureTypeOnly(exp.sinfo, entrytuple, entrybinds);

            const eargs = this.checkArgumentsEvaluationCollection(env, exp.args, entryobj);
            const atype = this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, entryobj, eargs, trgt, infertype, "K");

            return [env.setResultExpression(atype)];
        }
        else {
            const eargs = this.checkArgumentsEvaluationEntity(exp.sinfo, env, oftype, exp.args);
            const atype = this.checkArgumentsEntityConstructor(exp.sinfo, oftype, eargs, trgt, infertype);

            return [env.setResultExpression(atype)];
        }
    }

    private checkConstructorPrimaryWithFactory(env: TypeEnvironment, exp: ConstructorPrimaryWithFactoryExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof ResolvedEntityAtomType), "Invalid constructor type");
        this.raiseErrorIf(exp.sinfo, this.isConstructorTypeOfValue(ctype) === exp.isvalue, "Mismatch in storage layout decl and call");

        const oodecl = (objtype as ResolvedEntityAtomType).object;
        const oobinds = (objtype as ResolvedEntityAtomType).binds;
        this.raiseErrorIf(exp.sinfo, !(oodecl instanceof EntityTypeDecl), "Can only construct concrete entities");
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);

        const fdecl = oodecl.staticFunctions.get(exp.factoryName);
        this.raiseErrorIf(exp.sinfo, fdecl === undefined || !OOPTypeDecl.attributeSetContains("factory", fdecl.attributes), `Function is not a factory function for type '${ctype.idStr}'`);

        const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, (fdecl as StaticFunctionDecl).invoke, exp.terms.targs, oobinds, env.terms, undefined, false);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.factoryName, fsig, eargs);

        this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.pragmas.recursive);

        const etreg = this.m_emitter.generateTmpRegister();
        const skey = this.m_emitter.registerStaticCall(oodecl, oobinds, fdecl as StaticFunctionDecl, exp.factoryName, callbinds, rargs.pcodes, rargs.cinfo);

        const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, rargs.args, rargs.fflag, refinfo, etreg);

        const oftype = ResolvedEntityAtomType.create(oodecl, oobinds);
        const returntype = (fsig as ResolvedFunctionType).resultType;
        const atype = this.checkArgumentsEntityConstructor(exp.sinfo, oftype, [{ name: undefined, argtype: returntype, expando: true, ref: undefined, pcode: undefined, treg: etreg }], trgt, infertype);

        return [env.setResultExpression(atype)];
    }

    private checkTupleConstructor(env: TypeEnvironment, exp: ConstructorTupleExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        let itype: ResolvedTupleAtomType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableTupleConstructorType(exp.isvalue);
        }

        const eargs = this.checkArgumentsEvaluationTuple(env, exp.args, itype);
        const rtype = this.checkArgumentsTupleConstructor(exp.sinfo, exp.isvalue, eargs, trgt, infertype);

        return [env.setResultExpression(rtype)];
    }

    private checkRecordConstructor(env: TypeEnvironment, exp: ConstructorRecordExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        let itype: ResolvedRecordAtomType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableRecordConstructorType(exp.isvalue);
        }

        const eargs = this.checkArgumentsEvaluationRecord(env, exp.args, itype);
        const rtype = this.checkArgumentsRecordConstructor(exp.sinfo, exp.isvalue, eargs, trgt, infertype);
        return [env.setResultExpression(rtype)];
    }

    private checkConstructorEphemeralValueList(env: TypeEnvironment, exp: ConstructorEphemeralValueList, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        let itype: ResolvedEphemeralListType | undefined = undefined;
        if(infertype !== undefined) {
            itype = infertype.tryGetInferrableValueListConstructorType();
        }

        const eargs = this.checkArgumentsEvaluationValueList(env, exp.args, itype);
        const rtype = this.checkArgumentsValueListConstructor(exp.sinfo, eargs, trgt, infertype);
        return [env.setResultExpression(rtype)];
    }

    private checkSpecialConstructorExpression(env: TypeEnvironment, exp: SpecialConstructorExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, infertype !== undefined && (infertype.options.length !== 1 || !(infertype as ResolvedType).idStr.startsWith("NSCore::Result<")), "ok/err shorthand constructors only valid with NSCore::Result typed expressions");

        const { T, E } = infertype !== undefined && infertype.options.length === 1 ? this.getResultBinds(infertype) : { T: undefined, E: undefined };
        const treg = this.m_emitter.generateTmpRegister();
        if (exp.rop === "ok") {
            const okenv = this.checkExpression(env, exp.arg, treg, T);
            const oktdcl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okbinds = new Map<string, ResolvedType>().set("T", T || okenv.getExpressionResult().exptype).set("E", E || this.m_assembly.getSpecialAnyConceptType());
            const okconstype = ResolvedType.createSingle(ResolvedEntityAtomType.create(oktdcl, okbinds));
            const mirokconstype = this.m_emitter.registerResolvedTypeReference(okconstype);

            const okconsfunc = oktdcl.staticFunctions.get("create") as StaticFunctionDecl;
            const okconskey = this.m_emitter.registerStaticCall(oktdcl, okbinds, okconsfunc, "create", new Map<string, ResolvedType>(), [], []);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, okconstype, infertype, trgt);
            const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, okenv.getExpressionResult().exptype, okbinds.get("T") as ResolvedType);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, okconskey, [ctarg], undefined, mirokconstype, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, okconstype, infertype, iipack);
    
            return [env.setResultExpression(restype)];
        }
        else {
            this.raiseErrorIf(exp.sinfo, infertype === undefined, "Can't infer success type for Result<T, E>::Err");

            const errenv = this.checkExpression(env, exp.arg, treg, E);
            const errtdcl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errbinds = new Map<string, ResolvedType>().set("T", T as ResolvedType).set("E", E || errenv.getExpressionResult().exptype);
            const errconstype = ResolvedType.createSingle(ResolvedEntityAtomType.create(errtdcl, errbinds));
            const mirerrconstype = this.m_emitter.registerResolvedTypeReference(errconstype);

            const errconsfunc = errtdcl.staticFunctions.get("create") as StaticFunctionDecl;
            const errconskey = this.m_emitter.registerStaticCall(errtdcl, errbinds, errconsfunc, "create", new Map<string, ResolvedType>(), [], []);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, errconstype, infertype, trgt);
            const ctarg = this.emitInlineConvertIfNeeded(exp.sinfo, treg, errenv.getExpressionResult().exptype, errbinds.get("T") as ResolvedType);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, errconskey, [ctarg], undefined, mirerrconstype, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, errconstype, infertype, iipack);
    
            return [env.setResultExpression(restype)];
        }
    }

    private checkNamespaceOperatorInvoke(sinfo: SourceInfo, env: TypeEnvironment, opdecl: NamespaceOperatorDecl, args: MIRArgument[], argtypes: ResolvedType[], refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][], pragmas: PragmaArguments, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const fsig = this.m_assembly.normalizeTypeFunction(opdecl.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType;
        const [restype, iipack] = this.genInferInfo(sinfo, fsig.resultType, infertype, trgt);

        this.checkRecursion(sinfo, fsig, pcodes, pragmas.recursive);

        //if it is a static operator or it has a unique dynamic resolution based on the types
        if (!opdecl.isDynamic || !OOPTypeDecl.attributeSetContains("abstract", opdecl.attributes)) {
            const opkey = this.m_emitter.registerNamespaceOperatorCall(opdecl.ns, opdecl.name, opdecl, pcodes, cinfo);
            let cargs: MIRArgument[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(fsig.params[i].isRef) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(fsig.params[i].isLiteral) {
                    const mirargtype = this.m_emitter.registerResolvedTypeReference(argtypes[argidx]);

                    const lcreg = this.m_emitter.generateTmpRegister();
                    const lccall = MIRKeyGenerator.generateFunctionKey(opkey, `@@literalkey${i}`, new Map<string, ResolvedType>(), []);
                    this.m_emitter.emitInvokeFixedFunction(sinfo, lccall, [], undefined, mirargtype, lcreg);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitBinKeyEq(sinfo, mirargtype, cargs[argidx], mirargtype, lcreg, ichkreg);
                    this.m_emitter.emitAssertCheck(sinfo, "Failed to match literal tag on dynamic operator invoke", ichkreg);
                }
            }

            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeFixedFunction(sinfo, opkey, cargs, "[IGNORE]", refinfo, iipack[0]);
        }
        else {
            let cargs: MIRArgument[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(opdecl.invoke.params[i].isRef) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(opdecl.invoke.params[i].type as ResolvedType));
                }
            }

            const opkey = this.m_emitter.registerVirtualNamespaceOperatorCall(opdecl.ns, opdecl.name, opdecl, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey, cargs,  refinfo, iipack[0]);
        }

        this.emitConvertIfNeeded(sinfo, fsig.resultType, infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkStaticOperatorInvoke(sinfo: SourceInfo, env: TypeEnvironment, oodecl: OOPTypeDecl, oobinds: Map<string, ResolvedType>, opdecl: StaticOperatorDecl, args: MIRArgument[], argtypes: ResolvedType[], refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][], pragmas: PragmaArguments, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const fsig = this.m_assembly.normalizeTypeFunction(opdecl.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType;
        const [restype, iipack] = this.genInferInfo(sinfo, fsig.resultType, infertype, trgt);

        this.checkRecursion(sinfo, fsig, pcodes, pragmas.recursive);

        //if it is a static operator or it has a unique dynamic resolution based on the types
        if (!opdecl.isDynamic || !OOPTypeDecl.attributeSetContains("abstract", opdecl.attributes)) {
            const opkey = this.m_emitter.registerStaticOperatorCall(oodecl, opdecl.name, opdecl, oobinds, pcodes, cinfo);
            let cargs: MIRArgument[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(fsig.params[i].isRef) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(fsig.params[i].isLiteral) {
                    const mirargtype = this.m_emitter.registerResolvedTypeReference(argtypes[argidx]);

                    const lcreg = this.m_emitter.generateTmpRegister();
                    const lccall = MIRKeyGenerator.generateFunctionKey(opkey, `@@literalkey${i}`, new Map<string, ResolvedType>(), []);
                    this.m_emitter.emitInvokeFixedFunction(sinfo, lccall, [], undefined, mirargtype, lcreg);

                    //Should have same error if we fail to find suitable dynamic dispatch -- this is just a nice optimization
                    const ichkreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitBinKeyEq(sinfo, mirargtype, cargs[argidx], mirargtype, lcreg, ichkreg);
                    this.m_emitter.emitAssertCheck(sinfo, "Failed to match literal tag on dynamic operator invoke", ichkreg);
                }
            }

            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeFixedFunction(sinfo, opkey, cargs, "[IGNORE]", refinfo, iipack[0]);
        }
        else {
            let cargs: MIRArgument[] = [];
            for (let i = 0; i < fsig.params.length; ++i) {
                if(fsig.params[i] instanceof ResolvedFunctionType) {
                    continue;
                }

                const argidx = cargs.length;
                if(opdecl.invoke.params[i].isRef) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(opdecl.invoke.params[i].type as ResolvedType));
                }
            }

            const opkey = this.m_emitter.registerVirtualStaticOperatorCall(oodecl, opdecl.name, opdecl, oobinds, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey, cargs,  refinfo, iipack[0]);
        }

        this.emitConvertIfNeeded(sinfo, fsig.resultType, infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkCallNamespaceFunctionOrOperatorExpression(env: TypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if (nsdecl.operators.has(exp.name)) {
            const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) => OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
            const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
            this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

            const pnames = (opsintro as NamespaceOperatorDecl).invoke.params.map((p) => p.name);
            const hasrest = (opsintro as NamespaceOperatorDecl).invoke.optRestType !== undefined;

            //No terms to be bound on operator call

            const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
            const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

            const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
            const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types, isigs);

            this.raiseErrorIf(exp.sinfo, opidx !== -1 || (opsintro !== undefined && opsintro.isDynamic), "Cannot resolve operator");
            const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as NamespaceOperatorDecl;
            
            return this.checkNamespaceOperatorInvoke(exp.sinfo, env, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.pragmas, trgt, refok, infertype);
        } 
        else {
            this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
            const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, fdecl.invoke, exp.terms.targs, new Map<string, ResolvedType>(), env.terms, undefined, refok);
            this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, callbinds, fdecl.invoke.termRestrictions);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, fsig.resultType, infertype, trgt);
            const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.name, fsig, eargs);
            this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.pragmas.recursive);

            const ckey = this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, fsig.resultType, infertype, iipack);
    
            return [env.setResultExpression(restype)];
        }
    }

    private checkCallStaticFunctionOrOperatorExpression(env: TypeEnvironment, exp: CallStaticFunctionOrOperatorExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const fromtype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);
        const fdecltry = this.m_assembly.tryGetFunctionUniqueDeclFromType(fromtype, exp.name);
        const opdecltry = this.m_assembly.tryGetOperatorUniqueDeclFromType(fromtype, exp.name);

        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined && opdecltry === undefined), `Static function/operator not defined for type '${fromtype.idStr}'`);
        this.raiseErrorIf(exp.sinfo, (fdecltry !== undefined && opdecltry !== undefined), `Static function/operator multiply defined for type '${fromtype.idStr}'`);

        if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fdecltry.contiainingType.name === "KeyType" && (exp.name === "less" || exp.name === "equal")) {
            const lhsexp = exp.args.argList[0].value;
            const lhsreg = this.m_emitter.generateTmpRegister();
            const tlhs = this.checkExpression(env, lhsexp, lhsreg, undefined).getExpressionResult().exptype;

            const rhsexp = exp.args.argList[1].value;
            const rhsreg = this.m_emitter.generateTmpRegister();
            const trhs = this.checkExpression(env, rhsexp, rhsreg, undefined).getExpressionResult().exptype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(tlhs, this.m_assembly.getSpecialKeyTypeConceptType()) || !tlhs.isGroundedType(), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(trhs, this.m_assembly.getSpecialKeyTypeConceptType()) || !trhs.isGroundedType(), "Invalid argument");

            //
            //TODO: we could be more precise here by checking for degenerate cases -- equal(Int, String) -- not sure how useful this actually would be though
            //

            let mirlhs = this.m_emitter.registerResolvedTypeReference(tlhs);
            let mirrhs = this.m_emitter.registerResolvedTypeReference(trhs);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);
            if(exp.name === "equal") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, mirlhs, lhsreg, mirrhs, rhsreg, iipack[0]);
            }
            else {
                this.m_emitter.emitBinKeyLess(exp.sinfo, mirlhs, lhsreg, mirrhs, rhsreg, iipack[0]);
            }

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fromtype.idStr === "Tuple" && exp.name === "append") {
            let eargs: [ResolvedType, MIRTempRegister][] = [];
            let ttypes: ResolvedTupleAtomTypeEntry[] = [];
            let isvalue: boolean[] = [];

            for (let i = 0; i < exp.args.argList.length; ++i) {
                const arg = exp.args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

                this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in Tuple::append");
                this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Tuple::append");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().exptype;

                this.raiseErrorIf(exp.sinfo, earg.isUniqueTupleTargetType(), "Can only join arguments of (known) Tuple types");
                eargs.push([earg, treg]);
                ttypes = [...ttypes, ...earg.getUniqueTupleTargetType().types.map((tt) => new ResolvedTupleAtomTypeEntry(tt.type, false))];
                isvalue.push(earg.getUniqueTupleTargetType().isvalue);
            }

            const vcons = isvalue.every((vv) => vv);
            this.raiseErrorIf(exp.sinfo, isvalue.some((vv) => vv !== vcons), "Mix of value and reference tuple types is not allowed");

            const rtupletype = ResolvedType.createSingle(ResolvedTupleAtomType.create(vcons, ttypes));
            const [restype, iipack] = this.genInferInfo(exp.sinfo, rtupletype, infertype, trgt);

            this.m_emitter.emitStructuredAppendTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(rtupletype), eargs.map((ee) => ee[1]), eargs.map((ee) => this.m_emitter.registerResolvedTypeReference(ee[0])), iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, rtupletype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else if(fdecltry !== undefined && fdecltry.contiainingType.ns === "NSCore" && fromtype.idStr === "Record" && exp.name === "join") {
            let eargs: [ResolvedType, MIRTempRegister][] = [];
            let ttypes: ResolvedRecordAtomTypeEntry[] = [];
            let isvalue: boolean[] = [];
            let names = new Set<string>();

            for (let i = 0; i < exp.args.argList.length; ++i) {
                const arg = exp.args.argList[i];
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, arg.value instanceof ConstructorPCodeExpression, "Cannot use function in this call position");

                this.raiseErrorIf(arg.value.sinfo, !(arg instanceof PositionalArgument), "Only positional arguments allowed in Record::join");
                this.raiseErrorIf(arg.value.sinfo, (arg as PositionalArgument).isSpread, "Expando parameters are not allowed in Record::join");

                const treg = this.m_emitter.generateTmpRegister();
                const earg = this.checkExpression(env, arg.value, treg, undefined).getExpressionResult().exptype;

                this.raiseErrorIf(exp.sinfo, earg.isRecordTargetType(), "Can only join arguments of (known) Record types");
                eargs.push([earg, treg]);
                
                const allnamegroups = earg.options.map((opt) => (opt as ResolvedRecordAtomType).entries.map((entry) => entry.name));
                const allnames = [...new Set<string>(([] as string[]).concat(...allnamegroups))].sort();

                const allvals = earg.options.every((opt) => (opt as ResolvedRecordAtomType).isvalue);
                const allrefs = earg.options.every((opt) => !(opt as ResolvedRecordAtomType).isvalue);

                this.raiseErrorIf(exp.sinfo, allnames.some((pname) => names.has(pname)), "Cannot have (possibly) duplicate properties in join");
                this.raiseErrorIf(exp.sinfo, !allvals && !allrefs, "Cannot have mix of value and reference records");

                const ecc = allnames.map((pname) => {
                    names.add(pname);

                    const isopt = earg.options.some((opt) => {
                        const entry = (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname);
                        return entry === undefined || entry.isOptional;
                    });

                    const rtypes = earg.options
                        .filter((opt) => (opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) !== undefined)
                        .map((opt) => ((opt as ResolvedRecordAtomType).entries.find((ee) => ee.name === pname) as ResolvedRecordAtomTypeEntry).type);

                    return new ResolvedRecordAtomTypeEntry(pname, this.m_assembly.typeUpperBound(rtypes), isopt);
                });

                ttypes.push(...ecc);
                isvalue.push(allvals);
            }

            const vcons = isvalue.every((vv) => vv);
            this.raiseErrorIf(exp.sinfo, isvalue.some((vv) => vv !== vcons), "Mix of value and reference tuple types is not allowed");

            const rrecordtype = ResolvedType.createSingle(ResolvedRecordAtomType.create(vcons, ttypes));
            const [restype, iipack] = this.genInferInfo(exp.sinfo, rrecordtype, infertype, trgt);

            this.m_emitter.emitStructuredJoinRecord(exp.sinfo, this.m_emitter.registerResolvedTypeReference(rrecordtype), eargs.map((arg) => arg[1]), eargs.map((arg) => this.m_emitter.registerResolvedTypeReference(arg[0])), iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, rrecordtype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else {
            if (opdecltry !== undefined) {
                const oodecl = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).contiainingType;
                const oobinds = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).binds;

                const opsintro = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.find((nso) => OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
                const opdecls = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

                const pnames = (opsintro as StaticOperatorDecl).invoke.params.map((p) => p.name);
                const hasrest = (opsintro as StaticOperatorDecl).invoke.optRestType !== undefined;

                //No terms to be bound on operator call

                const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
                const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

                const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types, isigs);

                this.raiseErrorIf(exp.sinfo, opidx !== -1 || (opsintro !== undefined && opsintro.isDynamic), "Cannot resolve operator");
                const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as StaticOperatorDecl;
            
                return this.checkStaticOperatorInvoke(exp.sinfo, env, oodecl, oobinds, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.pragmas, trgt, refok, infertype); 
            }
            else {
                const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;

                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, fdecl.decl.invoke, exp.terms.targs, fdecl.binds, env.terms, undefined, refok);
                this.checkTemplateTypes(exp.sinfo, fdecl.decl.invoke.terms, callbinds, fdecl.decl.invoke.termRestrictions);

                const [restype, iipack] = this.genInferInfo(exp.sinfo, fsig.resultType, infertype, trgt);
                const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.name, fsig, eargs);
                this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.pragmas.recursive);

                const ckey = this.m_emitter.registerStaticCall(fdecl.contiainingType, fdecl.binds, fdecl.decl, exp.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
                this.emitConvertIfNeeded(exp.sinfo, fsig.resultType, infertype, iipack);

                return [env.setResultExpression(restype)];
            }
        }
    }

    private checkPCodeInvokeExpression(env: TypeEnvironment, exp: PCodeInvokeExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = (pco as { pcode: PCode, captured: string[] }).pcode;
        const captured = (pco as { pcode: PCode, captured: string[] }).captured;

        const cargs = [...exp.args.argList, ...captured.map((cv) => new PositionalArgument(false, false, new AccessVariableExpression(exp.sinfo, cv)))];
        const eargs = this.checkArgumentsEvaluationWSig(exp.sinfo, env, pcode.ftype, new Map<string, ResolvedType>(), new Arguments(cargs), undefined, refok);

        //A little strange since we don't expand captured args on the signature yet and don't expand/rest/etc -- slice them off for the checking
        const margs = this.checkArgumentsSignature(exp.sinfo, env, "pcode", pcode.ftype, eargs.slice(0, exp.args.argList.length));
        const cargsext = eargs.slice(exp.args.argList.length).map((ea) => ea.treg);

        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.pragmas.recursive);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, pcode.ftype.resultType, infertype, trgt);

        const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), [...margs.args, ...cargsext], undefined, refinfo, iipack[0]);        
        this.emitConvertIfNeeded(exp.sinfo, pcode.ftype.resultType, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessFromIndex(env: TypeEnvironment, op: PostfixAccessFromIndex, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, this.getInfoForHasIndex(op.sinfo, texp, op.index) !== "yes", "Index may not be defined for tuple");

        const idxtype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, op.index);

        const [restype, iipack] = this.genInferInfo(op.sinfo, idxtype, infertype, trgt);
        this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.index, !texp.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(idxtype), iipack[0]);
        this.emitConvertIfNeeded(op.sinfo, idxtype, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkProjectFromIndecies(env: TypeEnvironment, op: PostfixProjectFromIndecies, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx.index < 0), "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => this.getInfoForHasIndex(op.sinfo, texp, idx.index) !== "yes"), "Index may not be defined for all tuples");

        let itype: ResolvedType[] | undefined = undefined;
        if (infertype !== undefined) {
            if (op.isEphemeralListResult) {
                const eitype = infertype.tryGetInferrableValueListConstructorType();
                itype = eitype !== undefined ? eitype.types : undefined;
            }
            else {
                const eitype = infertype.tryGetInferrableTupleConstructorType(op.isValue);
                itype = eitype !== undefined ? eitype.types.map((entry) => entry.type) : undefined;
            }

            this.raiseErrorIf(op.sinfo, itype !== undefined && itype.length !== op.indecies.length, "Mismatch between number of indecies loaded and number expected by inferred type");
        }

        let etypes: ResolvedType[] = [];
        for (let i = 0; i < op.indecies.length; ++i) {
            const reqtype = op.indecies[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.indecies[i].reqtype as TypeSignature, env.terms) : undefined;
            let inferidx: ResolvedType | undefined = undefined
            if (reqtype !== undefined || itype !== undefined) {
                inferidx = reqtype !== undefined ? reqtype : (itype as ResolvedType[])[i];
            }

            const ttype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, op.indecies[i].index);
            etypes.push(inferidx || ttype);
        }

        const rephemeralatom = ResolvedEphemeralListType.create(etypes);
        const rephemeral = ResolvedType.createSingle(rephemeralatom);

        const rindecies = op.indecies.map((idv) => idv.index);

        const prjtemp = this.m_emitter.generateTmpRegister();
        if (texp.isUniqueTupleTargetType()) {
            const invk = this.m_emitter.registerTupleProjectToEphemeral(texp.getUniqueTupleTargetType(), rindecies, rephemeralatom);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
        }
        else {
            const invk = this.m_emitter.registerTupleProjectToEphemeralVirtual(texp, rindecies, rephemeralatom);
            this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
        }

        if (op.isEphemeralListResult) {
            const [restype, iipack] = this.genInferInfo(op.sinfo, rephemeral, infertype, trgt);

            this.m_emitter.emitTempRegisterAssign(op.sinfo, prjtemp, iipack[0]);

            this.emitConvertIfNeeded(op.sinfo, rephemeral, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else {
            const tupleatom = ResolvedTupleAtomType.create(op.isValue, etypes.map((tt) => new ResolvedTupleAtomTypeEntry(tt, false)));
            const rtuple = ResolvedType.createSingle(tupleatom);
    
            const [restype, iipack] = this.genInferInfo(op.sinfo, rtuple, infertype, trgt);

            const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
            this.m_emitter.emitConstructorTupleFromEphemeralList(op.sinfo, tupkey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), iipack[0]);
    
            this.emitConvertIfNeeded(op.sinfo, rtuple, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
    }

    private checkAccessFromName(env: TypeEnvironment, op: PostfixAccessFromName, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        if (texp.isRecordTargetType()) {
            this.raiseErrorIf(op.sinfo, !texp.isRecordTargetType(), "Base of property access expression must be of Record type");
            this.raiseErrorIf(op.sinfo, this.getInfoForHasProperty(op.sinfo, texp, op.name) !== "yes", "Property may not be defined for record");

            const rtype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp, op.name);

            const [restype, iipack] = this.genInferInfo(op.sinfo, rtype, infertype, trgt);
            
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.name, !texp.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);

            this.emitConvertIfNeeded(op.sinfo, rtype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else {
            const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(texp, op.name);
            this.raiseErrorIf(op.sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

            const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
            const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);

            const [restype, iipack] = this.genInferInfo(op.sinfo, ftype, infertype, trgt);
            
            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(finfo.contiainingType, finfo.binds), op.name);
            this.m_emitter.emitLoadField(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), fkey, texp.isUniqueCallTargetType(), this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
            
            this.emitConvertIfNeeded(op.sinfo, ftype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
    }

    private checkProjectFromNames(env: TypeEnvironment, op: PostfixProjectFromNames, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        let itype: ResolvedType[] | undefined = undefined;
        if (infertype !== undefined) {
            if (op.isEphemeralListResult) {
                const eitype = infertype.tryGetInferrableValueListConstructorType();
                itype = eitype !== undefined ? eitype.types : undefined;
            }
            else {
                const eitype = infertype.tryGetInferrableRecordConstructorType(op.isValue);
                this.raiseErrorIf(op.sinfo, eitype !== undefined && op.names.some((ln) => this.getInfoForHasProperty(op.sinfo, ResolvedType.createSingle(eitype), ln.name) !== "yes"), "Property may not be defined for all records");

                itype = eitype !== undefined ? op.names.map((nn) => (eitype.entries.find((entry) => entry.name === nn.name) as ResolvedRecordAtomTypeEntry).type) : undefined;
            }
        }
        this.raiseErrorIf(op.sinfo, itype !== undefined && itype.length !== op.names.length, "Mismatch between number of properties loaded and number expected by inferred type");


        if (texp.isRecordTargetType()) {
            this.raiseErrorIf(op.sinfo, op.names.some((ln) => this.getInfoForHasProperty(op.sinfo, texp, ln.name) !== "yes"), "Property may not be defined for all records");

            let etypes: [string, ResolvedType][] = [];
            for (let i = 0; i < op.names.length; ++i) {
                const reqtype = op.names[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.names[i].reqtype as TypeSignature, env.terms) : undefined;
                let inferidx: ResolvedType | undefined = undefined
                if (reqtype !== undefined || itype !== undefined) {
                    inferidx = reqtype !== undefined ? reqtype : (itype as ResolvedType[])[i];
                }

                const ttype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp, op.names[i].name);
                etypes.push([op.names[i].name, inferidx || ttype]);
            }

            const rephemeralatom = ResolvedEphemeralListType.create(etypes.map((ee) => ee[1]));
            const rephemeral = ResolvedType.createSingle(rephemeralatom);

            const pindecies = op.names.map((ndv) => ndv.name);

            const prjtemp = this.m_emitter.generateTmpRegister();
            if (texp.isUniqueRecordTargetType()) {
                const invk = this.m_emitter.registerRecordProjectToEphemeral(texp.getUniqueRecordTargetType(), pindecies, rephemeralatom);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
            }
            else {
                const invk = this.m_emitter.registerRecordProjectToEphemeralVirtual(texp, pindecies, rephemeralatom);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
            }

            if (op.isEphemeralListResult) {
                const [restype, iipack] = this.genInferInfo(op.sinfo, rephemeral, infertype, trgt);

                this.m_emitter.emitTempRegisterAssign(op.sinfo, prjtemp, iipack[0]);

                this.emitConvertIfNeeded(op.sinfo, rephemeral, infertype, iipack);
                return [env.setResultExpression(restype)];
            }
            else {
                const recordatom = ResolvedRecordAtomType.create(op.isValue, etypes.map((tt) => new ResolvedRecordAtomTypeEntry(tt[0], tt[1], false)));
                const rrecord = ResolvedType.createSingle(recordatom);

                const [restype, iipack] = this.genInferInfo(op.sinfo, rrecord, infertype, trgt);

                const tupkey = this.m_emitter.registerResolvedTypeReference(rrecord);
                this.m_emitter.emitConstructorRecordFromEphemeralList(op.sinfo, tupkey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), pindecies, iipack[0]);

                this.emitConvertIfNeeded(op.sinfo, rrecord, infertype, iipack);
                return [env.setResultExpression(restype)];
            }

        }
        else {
            const rfields = op.names.map((idv) => {
                const ff = this.m_assembly.tryGetFieldUniqueDeclFromType(texp, idv.name);
                this.raiseErrorIf(op.sinfo, ff === undefined, `Could not resolve field name "${idv}"`);

                return ff as OOMemberLookupInfo<MemberFieldDecl>;
            });

            const rephemeralatom = ResolvedEphemeralListType.create(rfields.map((ee) => this.resolveAndEnsureTypeOnly(op.sinfo, ee.decl.declaredType, ee.binds)));
            const rephemeral = ResolvedType.createSingle(rephemeralatom);

            const pindecies = rfields.map((ndv) => MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ndv.contiainingType, ndv.binds), ndv.decl.name));

            const prjtemp = this.m_emitter.generateTmpRegister();
            if (texp.isUniqueCallTargetType()) {
                const invk = this.m_emitter.registerEntityProjectToEphemeral(texp.getUniqueCallTargetType(), pindecies, rephemeralatom);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
            }
            else {
                const invk = this.m_emitter.registerOOTypeProjectToEphemeralVirtual(texp, pindecies, rephemeralatom);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg], undefined, this.m_emitter.registerResolvedTypeReference(rephemeral), prjtemp);
            }

            if (op.isEphemeralListResult) {
                const [restype, iipack] = this.genInferInfo(op.sinfo, rephemeral, infertype, trgt);

                this.m_emitter.emitTempRegisterAssign(op.sinfo, prjtemp, iipack[0]);

                this.emitConvertIfNeeded(op.sinfo, rephemeral, infertype, iipack);
                return [env.setResultExpression(restype)];
            }
            else {
                const recordatom = ResolvedRecordAtomType.create(op.isValue, rfields.map((tt) => new ResolvedRecordAtomTypeEntry(tt.decl.name, this.resolveOOTypeFromDecls(tt.contiainingType, tt.binds), false)));
                const rrecord = ResolvedType.createSingle(recordatom);

                const [restype, iipack] = this.genInferInfo(op.sinfo, rrecord, infertype, trgt);

                const tupkey = this.m_emitter.registerResolvedTypeReference(rrecord);
                this.m_emitter.emitConstructorRecordFromEphemeralList(op.sinfo, tupkey, prjtemp, this.m_emitter.registerResolvedTypeReference(rephemeral), rfields.map((tt) => tt.decl.name), iipack[0]);

                this.emitConvertIfNeeded(op.sinfo, rrecord, infertype, iipack);
                return [env.setResultExpression(restype)];
            }
        }
    }

    private checkModifyWithIndecies(env: TypeEnvironment, op: PostfixModifyWithIndecies, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType());

        const maxupdl = texp.getTupleTargetTypeIndexRange().req;
        const updates = op.updates.map<[number, ResolvedType, MIRArgument]>((update) => {
            this.raiseErrorIf(op.sinfo, update.index >= maxupdl, "Updates can only be applied to known indecies (i.e. cannot change the types of tuples)");

            const etreg = this.m_emitter.generateTmpRegister();
            const itype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, update.index);

            let eev = env;
            if (op.isBinder) {
                this.raiseErrorIf(op.sinfo, eev.isVarNameDefined(`$${update.index}`), `Duplicate definition of "$${update.index}" in binder`);

                this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.index}`, this.m_emitter.registerResolvedTypeReference(itype));
                this.m_emitter.localLifetimeStart(op.sinfo, `$${update.index}`, this.m_emitter.registerResolvedTypeReference(itype));
            }

            const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().exptype;

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.index}`)
            }

            return [update.index, utype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, itype)];
        });

        const [restype, iipack] = this.genInferInfo(op.sinfo, texp, infertype, trgt);

        const updateinfo = updates.map((upd) => [upd[0], this.m_emitter.registerResolvedTypeReference(upd[1])]) as [number, MIRType][];
        if (texp.isUniqueTupleTargetType()) {
            const invk = this.m_emitter.registerTupleUpdate(texp.getUniqueTupleTargetType(), updateinfo);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
        }
        else {
            const invk = this.m_emitter.registerTupleUpdateVirtual(texp, updateinfo);
            this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
        }

        this.emitConvertIfNeeded(op.sinfo, texp, infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkModifyWithNames(env: TypeEnvironment, op: PostfixModifyWithNames, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        if (texp.isRecordTargetType()) {
            const maxupdn = texp.getRecordTargetTypePropertySets().req;
            const updates = op.updates.map<[string, ResolvedType, MIRArgument]>((update) => {
                this.raiseErrorIf(op.sinfo, !maxupdn.has(update.name), "Updates can only be applied to known properties (i.e. cannot change the types of records)");

                const etreg = this.m_emitter.generateTmpRegister();
                const itype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp, update.name);

                let eev = env;
                if (op.isBinder) {
                    this.raiseErrorIf(op.sinfo, eev.isVarNameDefined(`$${update.name}`), `Duplicate definition of "$${update.name}" in binder`);

                    this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.name}`, this.m_emitter.registerResolvedTypeReference(itype));
                    this.m_emitter.localLifetimeStart(op.sinfo, `$${update.name}`, this.m_emitter.registerResolvedTypeReference(itype));
                }

                const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().exptype;

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}`)
                }

                return [update.name, utype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, itype)];
            });

            const [restype, iipack] = this.genInferInfo(op.sinfo, texp, infertype, trgt);

            const updateinfo = updates.map((upd) => [upd[0], this.m_emitter.registerResolvedTypeReference(upd[1])]) as [string, MIRType][];
            if (texp.isUniqueRecordTargetType()) {
                const invk = this.m_emitter.registerRecordUpdate(texp.getUniqueRecordTargetType(), updateinfo);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
            }
            else {
                const invk = this.m_emitter.registerRecordUpdateVirtual(texp, updateinfo);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
            }

            this.emitConvertIfNeeded(op.sinfo, texp, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
        else {
            const updates = op.updates.map<[OOMemberLookupInfo<MemberFieldDecl>, ResolvedType, MIRArgument]>((update) => {
                const etreg = this.m_emitter.generateTmpRegister();

                const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(texp, update.name);
                this.raiseErrorIf(op.sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

                const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
                const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);

                let eev = env;
                if (op.isBinder) {
                    this.raiseErrorIf(op.sinfo, eev.isVarNameDefined(`$${update.name}`), `Duplicate definition of "$${update.name}" in binder`);

                    this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.name}`, this.m_emitter.registerResolvedTypeReference(ftype));
                    this.m_emitter.localLifetimeStart(op.sinfo, `$${update.name}`, this.m_emitter.registerResolvedTypeReference(ftype));
                }

                const utype = this.checkExpression(eev, update.value, etreg, ftype).getExpressionResult().exptype;

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}`)
                }

                return [finfo, utype, this.emitInlineConvertIfNeeded(op.sinfo, etreg, utype, ftype)];
            });

            const [restype, iipack] = this.genInferInfo(op.sinfo, texp, infertype, trgt);

            const updateinfo = updates.map((upd) => {
                const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(upd[0].contiainingType, upd[0].binds), upd[0].decl.name);
                return [fkey, this.m_emitter.registerResolvedTypeReference(upd[1])] as [MIRFieldKey, MIRType];
            });

            if (texp.isUniqueRecordTargetType()) {
                const invk = this.m_emitter.registerEntityUpdate(texp.getUniqueCallTargetType(), updateinfo);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
            }
            else {
                const invk = this.m_emitter.registerOOTypeUpdateVirtual(texp, updateinfo);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, invk, [arg, ...updates.map((upd) => upd[2])], undefined, this.m_emitter.registerResolvedTypeReference(texp), iipack[0]);
            }

            this.emitConvertIfNeeded(op.sinfo, texp, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
    }

    private checkPostfixIs(env: TypeEnvironment, op: PostfixIs, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        const oftype = this.resolveAndEnsureTypeOnly(op.sinfo, op.istype, env.terms);

        const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

        this.m_emitter.emitTypeOf(op.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(texp));

        this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
        
        const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        return [
            ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True))), 
            ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False))),
        ];
    }

    private checkPostfixAs(env: TypeEnvironment, op: PostfixAs, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        const astype = this.resolveAndEnsureTypeOnly(op.sinfo, op.astype, env.terms);

        const creg = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitTypeOf(op.sinfo, creg, this.m_emitter.registerResolvedTypeReference(astype), arg, this.m_emitter.registerResolvedTypeReference(texp));
        this.m_emitter.emitAssertCheck(op.sinfo, "Failed type conversion", creg);

        const [restype, iipack] = this.genInferInfo(op.sinfo, astype, infertype, trgt);

        this.emitAssignToTempAndConvertIfNeeded_KnownSafe(op.sinfo, texp, astype, arg, iipack[0]);
        
        this.emitConvertIfNeeded(op.sinfo, astype, infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkPostfixHasIndex(env: TypeEnvironment, op: PostfixHasIndex, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Can only check for indecies on tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp, op.idx);
        const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.True)];
        }
        else {
            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, texp.isUniqueTupleTargetType(), iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const renvs = TypeEnvironment.convertToHasIndexNotHasIndexFlowsOnResult(this.m_assembly, op.idx, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, FlowTypeTruthValue.False))),
            ];
        }
    }

    private checkPostfixHasProperty(env: TypeEnvironment, op: PostfixHasProperty, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isRecordTargetType(), "Can only check for properties on record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp, op.pname);
        const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.True)];
        }
        else {
            this.m_emitter.emitRecordHasProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, texp.isUniqueRecordTargetType(), iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const renvs = TypeEnvironment.convertToHasIndexNotHasPropertyFlowsOnResult(this.m_assembly, op.pname, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False))),
            ];
        }
    }

    private checkInvoke(env: TypeEnvironment, op: PostfixInvoke, arg: MIRTempRegister, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        const resolvefrom = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp;
        const knownimpl = this.m_assembly.tryGetMethodUniqueConcreteDeclFromType(resolvefrom, op.name);

        if (knownimpl !== undefined) {
            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, env, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, [texp, env.getExpressionResult().expvar, arg], refok);
            this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

            const [restype, iipack] = this.genInferInfo(op.sinfo, fsig.resultType, infertype, trgt);
            const rargs = this.checkArgumentsSignature(op.sinfo, env, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.pragmas.recursive);

            const ckey = this.m_emitter.registerMethodCall(knownimpl.contiainingType, knownimpl.decl, knownimpl.binds, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, fsig.resultType, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else {
            const vinfo = this.m_assembly.tryGetMethodUniqueRootDeclFromType(texp, op.name);
            this.raiseErrorIf(op.sinfo, vinfo === undefined, `Missing (or multiple possible) declarations of "${op.name}" method`);

            const minfo = vinfo as OOMemberLookupInfo<MemberMethodDecl>;
            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, env, op.args, minfo.decl.invoke, op.terms.targs, minfo.binds, env.terms, [texp, env.getExpressionResult().expvar, arg], refok);
            this.checkTemplateTypes(op.sinfo, minfo.decl.invoke.terms, callbinds, minfo.decl.invoke.termRestrictions);

            const [restype, iipack] = this.genInferInfo(op.sinfo, fsig.resultType, infertype, trgt);
            const rargs = this.checkArgumentsSignature(op.sinfo, env, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.pragmas.recursive);

            const ckey = this.m_emitter.registerVirtualMethodCall(minfo.contiainingType, minfo.binds, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeVirtualFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, fsig.resultType, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkElvisAction(sinfo: SourceInfo, env: TypeEnvironment[], elvisEnabled: boolean, etrgt: MIRTempRegister, noneblck: string): [TypeEnvironment[], TypeEnvironment[]] {
        const paths = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), env);

        if (paths.tenvs.length === 0 && paths.fenvs.length === 0) {
            this.m_emitter.emitAbort(sinfo, "Infeasible flow path");
        }
        else {
            if (elvisEnabled) {
                if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                    //always some just keep going on current block emit
                }
                if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                    //always none
                    this.m_emitter.emitDirectJump(sinfo, noneblck);
                }
                else {
                    const nextblk = this.m_emitter.createNewBlock("Lelvis");
                    this.m_emitter.emitNoneJump(sinfo, etrgt, noneblck, nextblk);
                    this.m_emitter.setActiveBlock(nextblk);
                }
            }
        }

        return elvisEnabled ? [paths.fenvs, paths.tenvs] : [[...paths.fenvs, ...paths.tenvs], []];
    }

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck ? this.m_emitter.createNewBlock("Lelvis_none") : "INVALID";

        let etgrt = this.m_emitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt, undefined, {refok: refok, orok: false});

        let scflows: TypeEnvironment[] = [];
        let cenv = eenv;
        for (let i = 0; i < exp.ops.length; ++i) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, etgrt, noneblck);
            scflows = [...scflows, ...scflow];

            const itype = (i + 1 === exp.ops.length) ? infertype : undefined;

            const nflow = TypeEnvironment.join(this.m_assembly, ...fflow);
            if(nflow.isInfeasibleFlow()) {
                cenv = [];
                this.m_emitter.emitAbort(exp.sinfo, "Infeasible Flow");
                break;
            }

            const ntgrt = this.m_emitter.generateTmpRegister();
            switch (exp.ops[i].op) {
                case PostfixOpTag.PostfixAccessFromIndex:
                    cenv = this.checkAccessFromIndex(nflow, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixProjectFromIndecies:
                    cenv = this.checkProjectFromIndecies(nflow, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixAccessFromName:
                    cenv = this.checkAccessFromName(nflow, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixProjectFromNames:
                    cenv = this.checkProjectFromNames(nflow, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixModifyWithIndecies:
                    cenv = this.checkModifyWithIndecies(nflow, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixModifyWithNames:
                    cenv = this.checkModifyWithNames(nflow, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixIs:
                    cenv = this.checkPostfixIs(nflow, exp.ops[i] as PostfixIs, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixAs:
                    cenv = this.checkPostfixAs(nflow, exp.ops[i] as PostfixAs, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixHasIndex:
                    cenv = this.checkPostfixHasIndex(nflow, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    cenv = this.checkPostfixHasProperty(nflow, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt, itype);
                    break;
                default:
                    this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                    cenv = this.checkInvoke(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok, itype);
                    break;
            }

            etgrt = ntgrt;
        }


        const oktype = this.m_assembly.typeUpperBound(cenv.map((ee) => ee.getExpressionResult().exptype));
        const fulltype = this.m_assembly.typeUpperBound([oktype, ...(hasNoneCheck && scflows.length !== 0 ? [this.m_assembly.getSpecialNoneType()] : [])]);
        if (cenv.length === 0 && scflows.length === 0) {
            return [];
        }
        else {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, fulltype, infertype, trgt);

            if (cenv.length !== 0) {
                const convarg = this.emitInlineConvertIfNeeded(exp.sinfo, etgrt, oktype, fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, convarg, iipack[0]);
                this.emitConvertIfNeeded(exp.sinfo, fulltype, infertype, iipack);
            }

            if (hasNoneCheck && scflows.length !== 0) {
                const doneblck = this.m_emitter.createNewBlock("Lelvis_done");

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(noneblck);
                const convarg = this.emitInlineConvertIfNeeded(exp.sinfo, new MIRConstantNone(), this.m_assembly.getSpecialNoneType(), fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, convarg, iipack[0]);
                this.emitConvertIfNeeded(exp.sinfo, fulltype, infertype, iipack);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);
            }

            return [...cenv, ...scflows].map((ee) => ee.setResultExpressionWVarOptNoInfer(restype, ee.getExpressionResult().expvar, ee.getExpressionResult().truthval));
        }
    }

    private checkPrefixNotOp(env: TypeEnvironment, exp: PrefixNotOp, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const etreg = this.m_emitter.generateTmpRegister();
        const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg, this.m_assembly.getSpecialBoolType(), {refok: refok, orok: false});

        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

        this.m_emitter.emitPrefixNotOp(exp.sinfo, etreg, iipack[0]);
        
        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

        const bstates = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, estates);
        const ntstates = bstates.fenvs.map((state) => state.setResultExpressionWVarOptNoInfer(restype, state.getExpressionResult().expvar, FlowTypeTruthValue.False));
        const nfstates = bstates.tenvs.map((state) => state.setResultExpressionWVarOptNoInfer(restype, state.getExpressionResult().expvar, FlowTypeTruthValue.True));

        return [...ntstates, ...nfstates];
    }

    private checkBinEq(env: TypeEnvironment, exp: BinEqExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg, undefined);

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg, undefined);

        const action = this.checkValueEq(exp.lhs, lhs.getExpressionResult().exptype, exp.rhs, rhs.getExpressionResult().exptype);
        if(action === "truealways" || action === "falsealways") {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitLoadConstBool(exp.sinfo, action === "truealways" ? true : false, iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
            return [env.setResultExpression(restype, action === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone" || action === "rhsnone") {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);
            
            if(action === "lhsnone") {
                this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().exptype));
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().exptype));
            }

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const eevs = (action === "lhsnone") ? rhs : lhs;
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [eevs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOpt(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False))),
            ];
        }
        else {
            let olhsreg = lhsreg;
            let olhs = lhs.getExpressionResult().exptype;

            let orhsreg = rhsreg;
            let orhs = rhs.getExpressionResult().exptype;

            if (action === "stringof" || action === "datastring") {
                const sstr = this.m_assembly.getSpecialStringType();
                const mirstr = this.m_emitter.registerResolvedTypeReference(sstr);

                const sobj = olhs.options[0] as ResolvedEntityAtomType;
                const ikey = this.m_emitter.registerMethodCall(sobj.object, sobj.object.memberMethods.get("string") as MemberMethodDecl, sobj.binds, "string", new Map<string, ResolvedType>(), [], []);

                olhsreg = this.m_emitter.generateTmpRegister();
                olhs = sstr;
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ikey, [lhsreg], undefined, mirstr, olhsreg);

                orhsreg = this.m_emitter.generateTmpRegister();
                orhs = sstr;
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ikey, [rhsreg], undefined, mirstr, orhsreg);
            }

            const eargs = [
                { name: undefined, argtype: olhs, ref: undefined, expando: false, pcode: undefined, treg: olhsreg },
                { name: undefined, argtype: orhs, ref: undefined, expando: false, pcode: undefined, treg: orhsreg }
            ];

            const opns = this.m_assembly.getNamespace("NSMain") as NamespaceDeclaration;
            const opdecls = (opns.operators.get(exp.op) as NamespaceOperatorDecl[]).filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
            this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

            const rargs = this.checkArgumentsWOperator(exp.sinfo, env, ["a", "b"], false, eargs);

            const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
            const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types, isigs);

            this.raiseErrorIf(exp.sinfo, opidx !== -1, "Cannot resolve operator");
            const opdecl = opdecls[opidx];
            
            return this.checkNamespaceOperatorInvoke(exp.sinfo, env, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, new PragmaArguments("no", []), trgt, false, infertype);
        }
    }

    private checkBinCmp(env: TypeEnvironment, exp: BinCmpExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg, undefined);

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg, undefined);

        const action = this.checkValueLess(lhs.getExpressionResult().exptype, rhs.getExpressionResult().exptype);
        if(action === "truealways" || action === "falsealways") {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitLoadConstBool(exp.sinfo, action === "truealways" ? true : false, iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
            return [env.setResultExpression(restype, action === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else {
            let olhsreg = lhsreg;
            let olhs = lhs.getExpressionResult().exptype;

            let orhsreg = rhsreg;
            let orhs = rhs.getExpressionResult().exptype;

            if (action === "stringof" || action === "datastring") {
                const sstr = this.m_assembly.getSpecialStringType();
                const mirstr = this.m_emitter.registerResolvedTypeReference(sstr);

                const sobj = olhs.options[0] as ResolvedEntityAtomType;
                const ikey = this.m_emitter.registerMethodCall(sobj.object, sobj.object.memberMethods.get("string") as MemberMethodDecl, sobj.binds, "string", new Map<string, ResolvedType>(), [], []);

                olhsreg = this.m_emitter.generateTmpRegister();
                olhs = sstr;
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ikey, [lhsreg], undefined, mirstr, olhsreg);

                orhsreg = this.m_emitter.generateTmpRegister();
                orhs = sstr;
                this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ikey, [rhsreg], undefined, mirstr, orhsreg);
            }

            const eargs = [
                { name: undefined, argtype: olhs, ref: undefined, expando: false, pcode: undefined, treg: olhsreg },
                { name: undefined, argtype: orhs, ref: undefined, expando: false, pcode: undefined, treg: orhsreg }
            ];

            const opns = this.m_assembly.getNamespace("NSMain") as NamespaceDeclaration;
            const opdecls = (opns.operators.get(exp.op) as NamespaceOperatorDecl[]).filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
            this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

            const rargs = this.checkArgumentsWOperator(exp.sinfo, env, ["a", "b"], false, eargs);

            const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
            const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types, isigs);

            this.raiseErrorIf(exp.sinfo, opidx !== -1, "Cannot resolve operator");
            const opdecl = opdecls[opidx];
            
            return this.checkNamespaceOperatorInvoke(exp.sinfo, env, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, new PragmaArguments("no", []), trgt, false, infertype);
        }
    }

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, this.m_assembly.getSpecialBoolType());
        this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().exptype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        if (exp.op === "||") {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.True)) {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitLoadConstBool(exp.sinfo, true, iipack[0]);

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
                return lhs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_or_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_or_rest");

                const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitTempRegisterAssign(exp.sinfo, lhsreg, iipack[0]);
                this.m_emitter.emitBoolJump(exp.sinfo, lhsreg, doneblck, restblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, iipack[0], this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });
                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().exptype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);
                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

                const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
            }
        }
        else if (exp.op === "&&") {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitLoadConstBool(exp.sinfo, false, iipack[0]);

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
                return lhs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_and_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_and_rest");

                const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitTempRegisterAssign(exp.sinfo, lhsreg, iipack[0]);
                this.m_emitter.emitBoolJump(exp.sinfo, lhsreg, restblck, doneblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, iipack[0], this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });
                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().exptype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);
                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

                const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
            }
        }
        else {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitLoadConstBool(exp.sinfo, false, iipack[0]);

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
                return lhs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_imply_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_imply_rest");

                const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                this.m_emitter.emitPrefixNotOp(exp.sinfo, lhsreg, iipack[0]);
                this.m_emitter.emitBoolJump(exp.sinfo, lhsreg, restblck, doneblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, iipack[0], this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });
                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().exptype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);
                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

                const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
            }
        }
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const itype = infertype !== undefined ? infertype.tryGetInferrableTupleConstructorType(true) : undefined;
        const metype = (itype !== undefined && itype.types.length === 2 && itype.types.every((ee) => !ee.isOptional)) ? itype : undefined;

        const kreg = this.m_emitter.generateTmpRegister();
        const kinfer = metype !== undefined ? metype.types[0].type : undefined;
        const ktype = this.checkExpression(env, exp.kexp, kreg, kinfer).getExpressionResult().exptype;

        this.raiseErrorIf(exp.kexp.sinfo, !this.m_assembly.subtypeOf(ktype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.isGroundedType(), "Key must be a grounded KeyType value");

        const vreg = this.m_emitter.generateTmpRegister();
        const vinfer = metype !== undefined ? metype.types[1].type : undefined;
        const vtype = this.checkExpression(env, exp.vexp, vreg, vinfer).getExpressionResult().exptype;

        const mtype = ResolvedType.createSingle(ResolvedTupleAtomType.create(true, [new ResolvedTupleAtomTypeEntry(ktype, false), new ResolvedTupleAtomTypeEntry(vtype, false)]));

        const [restype, iipack] = this.genInferInfo(exp.sinfo, mtype, infertype, trgt);

        this.m_emitter.emitConstructorTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(mtype), [kreg, vreg], iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, mtype, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkNonecheck(env: TypeEnvironment, exp: NonecheckExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, undefined);

        if (lhs.every((ee) => ee.getExpressionResult().exptype.isNoneType())) {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, trgt);

            this.m_emitter.emitLoadConstNone(exp.sinfo, iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, iipack);
            return lhs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar));
        }
        else {
            const doneblck = this.m_emitter.createNewBlock("Lnonecheck_done");
            const restblck = this.m_emitter.createNewBlock("Lnonecheck_rest");

            xxxx;
            const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitTempRegisterAssign(exp.sinfo, lhsreg, iipack[0]);
            this.m_emitter.emitBoolJump(exp.sinfo, lhsreg, doneblck, restblck);
            this.m_emitter.setActiveBlock(restblck);

            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, iipack[0], this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().exptype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.setActiveBlock(doneblck);
            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const oflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
            return [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
        }







        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

        if (exp.lhs instanceof AccessVariableExpression) {
            const vname = (exp.lhs as AccessVariableExpression).name;
            enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
            esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
        }

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, scblck, restblck);

            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...esome), exp.rhs, trgt);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return [...enone, ...rhs];
    }

    private checkCoalesce(env: TypeEnvironment, exp: CoalesceExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

        if (exp.lhs instanceof AccessVariableExpression) {
            const vname = (exp.lhs as AccessVariableExpression).name;
            enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
            esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
        }

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, restblck, scblck);

            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, lhsreg, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...enone), exp.rhs, trgt);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return [...esome, ...rhs];
    }

    private checkSelect(env: TypeEnvironment, exp: SelectExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg);

        this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_done");
        const trueblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_true");
        const falseblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_false");
        if (this.m_emitEnabled) {
            const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
            this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, isstrict, trueblck, falseblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
        }

        const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.option1, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
        }

        const falsestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...falseflow), exp.option2, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        const rtype = this.m_assembly.typeUpperBound([truestate.getExpressionResult().etype, falsestate.getExpressionResult().etype]);
        return [env.setExpressionResult(rtype)];
    }

    private checkOrExpression(env: TypeEnvironment, exp: ExpOrExpression, trgt: MIRTempRegister, extraok: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !extraok.orok, "Or expression is not valid in this position");

        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_return");
        const regularblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_regular");

        let evalue = this.checkExpressionMultiFlow(env, exp.exp, trgt, {refok: extraok.refok, orok: false});

        let normaltype: ResolvedType = this.m_assembly.typeUpperBound(evalue.map((ev) => ev.getExpressionResult().etype));
        let normalexps: TypeEnvironment[] = [];
        let terminaltype: ResolvedType = this.m_assembly.getSpecialAnyConceptType();
        let terminalexps: TypeEnvironment[] = [];

        if (exp.cond !== undefined || exp.result !== undefined) {
            evalue = evalue.map((ev) => ev.pushLocalScope().addVar("$value", true, ev.getExpressionResult().etype, true, ev.getExpressionResult().etype));
            if (this.m_emitEnabled) {
                const vtype = TypeEnvironment.join(this.m_assembly, ...evalue).getExpressionResult().etype;
                this.m_emitter.bodyEmitter.localLifetimeStart(exp.sinfo, "$value", this.m_emitter.registerResolvedTypeReference(vtype).trkey);
                this.m_emitter.bodyEmitter.emitVarStore(exp.sinfo, trgt, "$value");
            }
        }

        if (exp.cond === undefined) {
            if (normaltype.options.every((opt) => this.m_assembly.isResultConceptType(opt) || this.m_assembly.isResultEntityType(opt))) {
                normaltype = TypeEnvironment.join(this.m_assembly, ...evalue).getExpressionResult().etype;
                terminaltype = TypeEnvironment.join(this.m_assembly, ...evalue).getExpressionResult().etype;
    
                if (this.m_emitEnabled) {
                    const treg = this.m_emitter.bodyEmitter.generateTmpRegister();

                    const infertype = this.m_emitter.registerResolvedTypeReference(normaltype).trkey;
                    const ttype = (normaltype.options[0] as ResolvedEntityAtomType).binds.get("T") as ResolvedType;
                    const etype = (normaltype.options[0] as ResolvedEntityAtomType).binds.get("E") as ResolvedType;

                    const robj = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result") as EntityTypeDecl;
                    const rbinds = new Map<string, ResolvedType>().set("T", ttype).set("E", etype);
                    const rtype = ResolvedType.createSingle(ResolvedEntityAtomType.create(robj, rbinds));

                    this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(normaltype, rtype), "Result types do not match");

                    const errobj = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Err") as EntityTypeDecl;
                    const errbinds = new Map<string, ResolvedType>().set("T", ttype).set("E", etype);
                    const errtype = ResolvedType.createSingle(ResolvedEntityAtomType.create(errobj, errbinds));

                    const chktype = this.m_emitter.registerResolvedTypeReference(errtype).trkey;

                    this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, treg, chktype, infertype, trgt);
                    this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, treg, true, scblck, regularblck);
                    this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                }
    
                normalexps = evalue;
                terminalexps = evalue;
            }
            else {
                this.raiseErrorIf(exp.sinfo, normaltype.options.some((opt) => this.m_assembly.isResultConceptType(opt) || this.m_assembly.isResultEntityType(opt)), "Cannot mix Result and None types");

                let [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, evalue);
                this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
                this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

                if (exp.exp instanceof AccessVariableExpression) {
                    const vname = (exp.exp as AccessVariableExpression).name;
                    enone = enone.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
                    esome = esome.map((opt) => opt.assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype));
                }

                normaltype = TypeEnvironment.join(this.m_assembly, ...esome).getExpressionResult().etype;
                terminaltype = TypeEnvironment.join(this.m_assembly, ...enone).getExpressionResult().etype;

                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, trgt, scblck, regularblck);
                    this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                }

                normalexps = esome;
                terminalexps = enone;
            }
        }
        else {
            const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const tvalue = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...evalue), exp.cond, treg);

            this.raiseErrorIf(exp.sinfo, tvalue.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, tvalue);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            normaltype = (TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("$value") as VarInfo).flowType;
            terminaltype = (TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("$value") as VarInfo).flowType;

            if (this.m_emitEnabled) {
                const isstrict = tvalue.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, treg, isstrict, scblck, regularblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            }

            normalexps = falseflow.map((ev) => ev.popLocalScope());
            terminalexps = trueflow.map((ev) => ev.popLocalScope());
        }

        let rreg = trgt;
        if (exp.result !== undefined) {
            const tenv = TypeEnvironment.join(this.m_assembly, ...terminalexps);
            const rvalue = this.checkExpression(tenv, exp.result, rreg);
            terminaltype = rvalue.getExpressionResult().etype;
        }

        if (exp.cond !== undefined || exp.result !== undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, "$value");
            }
        }

        if (exp.action === "return") {
            this.raiseErrorIf(exp.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, rreg);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "returnassign");

                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }

            return [...(normalexps.map((ev) => ev.setExpressionResult(normaltype))), env.setReturn(this.m_assembly, terminaltype)];
        }
        else {
            this.raiseErrorIf(exp.sinfo, !env.isInYieldBlock(), "Cannot use yield statment unless inside and expression block");

            if (this.m_emitEnabled) {
                const yinfo = env.getYieldTargetInfo();
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rreg, yinfo[0]);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, yinfo[1]);

                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }

            return [...(normalexps.map((ev) => ev.setExpressionResult(normaltype))), env.setYield(this.m_assembly, terminaltype)];
        }
    }

    private checkBlockExpression(env: TypeEnvironment, exp: BlockStatementExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const yblck = this.m_emitter.bodyEmitter.createNewBlock("Lyield");
        let cenv = env.freezeVars().pushLocalScope().pushYieldTarget(trgt, yblck);

        for (let i = 0; i < exp.ops.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, exp.ops[i]);
        }

        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.setActiveBlock(yblck);

            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
            }
        }

        this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
        this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");

        const ytype = cenv.yieldResult as ResolvedType;
        return [env.setExpressionResult(ytype)];
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifexp_done");

        let cenv = env;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < exp.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg);

            this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}true`);
            const falseblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}false`);
            if (this.m_emitEnabled) {
                const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, isstrict, trueblck, falseblck);
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }

            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow.conds[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }

            results.push(truestate);
            cenv = TypeEnvironment.join(this.m_assembly, ...falseflow);
        }

        const aenv = this.checkExpression(cenv, exp.flow.elseAction as Expression, trgt);
        results.push(aenv);

        if (this.m_emitEnabled && aenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return results;
    }

    private checkMatchExpression(env: TypeEnvironment, exp: MatchExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg);

        const svname = exp.sval instanceof AccessVariableExpression ? exp.sval.name : undefined;

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchexp_done");

        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < exp.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, i, vreg, vtype, cenv, exp.flow[i].check, nextlabel, actionlabel, svname, i === exp.flow.length - 1);

            vtype = test.nexttype;
            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== exp.flow.length - 1) , "Expression is always true/false expression test is redundant");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }

            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }

            results.push(truestate);
            cenv = falseflow.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }

        //do an exhaustive check in one case we know
        if (!exp.flow.some((gc) => gc.check instanceof WildcardMatchGuard)) {
            this.m_exhaustiveChecks.push({file: this.m_file, sinfo: exp.sinfo, vtype: vtype, chk: exp.flow.map((cc) => cc.check)});
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(exp.sinfo, "exhaustive");
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return results;
    }

    private checkExpression(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment {
        const res = this.checkExpressionMultiFlow(env, exp, trgt, extraok);
        this.raiseErrorIf(exp.sinfo, res.length === 0, "No feasible flow for expression");

        return TypeEnvironment.join(this.m_assembly, ...res);
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression, trgt);
            case ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression, trgt);
            case ExpressionTag.LiteralIntegerExpression:
                return this.checkLiteralIntegerExpression(env, exp as LiteralIntegerExpression, trgt);
            case ExpressionTag.LiteralBigIntegerExpression:
                return this.checkLiteralBigIntegerExpression(env, exp as LiteralBigIntegerExpression, trgt);
            case ExpressionTag.LiteralFloatExpression:
                return this.checkLiteralFloat64Expression(env, exp as LiteralFloatExpression, trgt);
            case ExpressionTag.LiteralRegexExpression:
                return this.checkLiteralRegexExpression(env, exp as LiteralRegexExpression, trgt);
            case ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression, trgt);
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt);
            case ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkTypedStringConstructor(env, exp as LiteralTypedStringConstructorExpression, trgt);
            case ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression, trgt);
            case ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression, trgt);
            case ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp as AccessVariableExpression, trgt);
            case ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression, trgt);
            case ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt);
            case ExpressionTag.ConstructorEphemeralValueList:
                return this.checkConstructorEphemeralValueList(env, exp as ConstructorEphemeralValueList, trgt);
            case ExpressionTag.ResultExpression:
                return this.checkResultExpression(env, exp as ResultExpression, trgt);
            case ExpressionTag.CallNamespaceFunctionExpression:
                return this.checkCallNamespaceFunctionExpression(env, exp as CallNamespaceFunctionExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.CallStaticFunctionExpression:
                return this.checkCallStaticFunctionExpression(env, exp as CallStaticFunctionExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.PCodeInvokeExpression:
                return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.PostfixOpExpression:
                return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false);
            case ExpressionTag.PrefixOpExpression:
                return this.checkPrefixOp(env, exp as PrefixOp, trgt);
            case ExpressionTag.TailTypeExpression:
                return this.checkTailTypeExpression(env, exp as TailTypeExpression, trgt);
            case ExpressionTag.BinOpExpression:
                return this.checkBinOp(env, exp as BinOpExpression, trgt);
            case ExpressionTag.BinEqExpression:
                return this.checkBinEq(env, exp as BinEqExpression, trgt);
            case ExpressionTag.BinCmpExpression:
                return this.checkBinCmp(env, exp as BinCmpExpression, trgt);
            case ExpressionTag.BinLogicExpression:
                return this.checkBinLogic(env, exp as BinLogicExpression, trgt);
            case ExpressionTag.MapEntryConstructorExpression:
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, trgt);
            case ExpressionTag.NonecheckExpression:
                return this.checkNonecheck(env, exp as NonecheckExpression, trgt);
            case ExpressionTag.CoalesceExpression:
                return this.checkCoalesce(env, exp as CoalesceExpression, trgt);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt);
            case ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp as ExpOrExpression, trgt, extraok || { refok: false, orok: false });
            case ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp as BlockStatementExpression, trgt);
            case ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp as IfExpression, trgt);
            default:
                this.raiseErrorIf(exp.sinfo, exp.tag !== ExpressionTag.MatchExpression, "Unknown expression");
                return this.checkMatchExpression(env, exp as MatchExpression, trgt);
        }
    }

    private checkDeclareSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, venv: { etype: ResolvedType, etreg: MIRTempRegister } | undefined): TypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), "Cannot shadow previous definition");

        this.raiseErrorIf(sinfo, venv === undefined && isConst, "Must define const var at declaration site");
        this.raiseErrorIf(sinfo, venv === undefined && decltype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? (venv as { etype: ResolvedType, etreg: MIRTempRegister }).etype : this.resolveAndEnsureTypeOnly(sinfo, decltype, env.terms);
        this.raiseErrorIf(sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.etype, vtype), "Expression is not of declared type");

        if (this.m_emitEnabled) {
            const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype);
            this.m_emitter.bodyEmitter.localLifetimeStart(sinfo, vname, mirvtype.trkey);

            if (venv !== undefined) {
                this.m_emitter.bodyEmitter.emitVarStore(sinfo, venv.etreg, vname);
            }
        }

        return env.addVar(vname, isConst, vtype, venv !== undefined, venv !== undefined ? venv.etype : vtype);
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true }) : undefined;

        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().etype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        const vv = venv !== undefined ? { etype: venv.getExpressionResult().etype, etreg: etreg } : undefined;
        return this.checkDeclareSingleVariable(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, vv);
    }

    private checkVariablePackDeclarationStatement(env: TypeEnvironment, stmt: VariablePackDeclarationStatement): TypeEnvironment {
        let cenv = env;
        if (stmt.exp === undefined) {
            for (let i = 0; i < stmt.vars.length; ++i) {
                cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, undefined);
            }
        }
        else {
            if (stmt.exp.length === 1) {
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                const ve = this.checkExpression(env, stmt.exp[0], etreg, { refok: true, orok: true }).getExpressionResult().etype;

                this.raiseErrorIf(stmt.sinfo, ve.options.length !== 1 || !(ve.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

                const elt = ve.options[0] as ResolvedEphemeralListType;
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== elt.types.length, "Missing initializers for variables");

                for (let i = 0; i < stmt.vars.length; ++i) {
                    const tlreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    if (this.m_emitEnabled) {
                        const eltkey = this.m_emitter.registerResolvedTypeReference(ve).trkey;
                        const rtype = this.m_emitter.registerResolvedTypeReference(elt.types[i]).trkey;
                        this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, rtype, eltkey, i, tlreg);
                    }

                    cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: elt.types[i], etreg: tlreg });
                }
            }
            else {
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== stmt.exp.length, "Missing initializers for variables");

                for (let i = 0; i < stmt.vars.length; ++i) {
                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const venv = this.checkExpression(env, stmt.exp[i], etreg).getExpressionResult().etype;

                    cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: venv, etreg: etreg });
                }
            }
        }

        return cenv;
    }

    private checkAssignSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, etype: ResolvedType, etreg: MIRTempRegister): TypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(etype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitVarStore(sinfo, etreg, vname);
        }

        return env.setVar(vname, etype);
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true });
       
        return this.checkAssignSingleVariable(stmt.sinfo, env, stmt.name, venv.getExpressionResult().etype, etreg);
    }

    private checkVariablePackAssignmentStatement(env: TypeEnvironment, stmt: VariablePackAssignmentStatement): TypeEnvironment {
        let cenv = env;

        if (stmt.exp.length === 1) {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const ve = this.checkExpression(env, stmt.exp[0], etreg, { refok: true, orok: true }).getExpressionResult().etype;

            this.raiseErrorIf(stmt.sinfo, ve.options.length !== 1 || !(ve.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

            const elt = ve.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== elt.types.length, "Missing initializers for variables");

            for (let i = 0; i < stmt.names.length; ++i) {
                const tlreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                if (this.m_emitEnabled) {
                    const eltkey = this.m_emitter.registerResolvedTypeReference(ve).trkey;
                    const rtype = this.m_emitter.registerResolvedTypeReference(elt.types[i]).trkey;
                    this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, rtype, eltkey, i, tlreg);
                }

                cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], elt.types[i], tlreg);
            }
        }
        else {
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== stmt.exp.length, "Missing initializers for variables");

            for (let i = 0; i < stmt.names.length; ++i) {
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.exp[i], etreg).getExpressionResult().etype;

                cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], venv, etreg);
            }
        }

        return cenv;
    }

    private checkStructuredAssign(sinfo: SourceInfo, env: TypeEnvironment, isopt: boolean, cpath: StructuredAssignmentPathStep[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][], allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][]) {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const itype = this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms);
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, itype), "Ignore type is not a subtype of declared type");
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseError(sinfo, "Cannot use constants in structured assignment");
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const vtype = (assign.vtype instanceof AutoTypeSignature)
                ? expt
                : (assign.isOptional
                    ? this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, vtype), "Expression is not of declared type");

            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], expt]);
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

            allAssigned.push([assign.vname, [...cpath], expt]);
        }
        else if (assign instanceof ValueListStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, expt.options.length !== 1 || !(expt.options[0] instanceof ResolvedEphemeralListType), "Assign value is not subtype of declared variable type");
            
            const eltype = expt.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(sinfo, eltype.types.length !== assign.assigns.length, "More values in ephemeral list than assignment");

            for (let i = 0; i < assign.assigns.length; ++i) {
                const step = createEphemeralStructuredAssignmentPathStep(expt, eltype.types[i], i);
                this.checkStructuredAssign(sinfo, env, false, [...cpath, step], assign.assigns[i], eltype.types[i], allDeclared, allAssigned);
            }
        }
        else if (assign instanceof NominalStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");

            const ntype = this.resolveAndEnsureTypeOnly(sinfo, assign.atype, env.terms);
            this.raiseErrorIf(sinfo, ntype.options.length !== 1 || !(ntype.options[0] instanceof ResolvedEntityAtomType || ntype.options[0] instanceof ResolvedConceptAtomType));
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, ntype), "Assign value is not subtype of declared variable type");

            const fieldkeys = assign.assigns.map((asn) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(ntype, "field", asn[0]);
                this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const ffdecl = (fdeclinfo.decl as MemberFieldDecl);
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, ffdecl.declaredType, fdeclinfo.binds);
                return { key: MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, asn[0]), ftype: ftype };
            });

            const ptype = ntype.options[0];
            let fields = new Set<string>();
            if (ptype instanceof ResolvedEntityAtomType) {
                const fmap = this.m_assembly.getAllOOFields(ptype.object, ptype.binds);
                fmap.forEach((v, k) => fields.add(k));
            }
            else {
                (ptype as ResolvedConceptAtomType).conceptTypes.forEach((concept) => {
                    const fmap = this.m_assembly.getAllOOFields(concept.concept, concept.binds);
                    fmap.forEach((v, k) => fields.add(k));
                });
            }
            this.raiseErrorIf(sinfo, fields.size > assign.assigns.length, "More fields in type that assignment");

            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = fieldkeys[i].ftype;
                const step = createNominalStructuredAssignmentPathStep(expt, ttype, fieldkeys[i].key);
                this.checkStructuredAssign(sinfo, env, false, [...cpath, step], assign.assigns[i], ttype, allDeclared, allAssigned);
            }
        }
        else if (assign instanceof TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialTupleConceptType()), "Assign value is not subtype of declared variable type");
            
            const tuptype = ResolvedType.create(expt.options.map((opt) => {
                this.raiseErrorIf(sinfo, !(opt instanceof ResolvedTupleAtomType), "Cannot use 'Tuple' type in structured assignment");
                return opt as ResolvedTupleAtomType;
            }));
            this.raiseErrorIf(sinfo, tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length > assign.assigns.length), "More values in tuple that assignment");

            for (let i = 0; i < assign.assigns.length; ++i) {
                const aopt = tuptype.options.some((atom) => (atom as ResolvedTupleAtomType).types.length < i || (atom as ResolvedTupleAtomType).types[i].isOptional);
                const ttype = this.getInfoForLoadFromIndex(sinfo, tuptype, i);
                const step = createTupleStructuredAssignmentPathStep(expt, ttype, i);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, step], assign.assigns[i], ttype, allDeclared, allAssigned);
            }
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialRecordConceptType()), "Assign value is not subtype of declared variable type");
            
            const rectype = ResolvedType.create(expt.options.map((opt) =>  {
                this.raiseErrorIf(sinfo, !(opt instanceof ResolvedRecordAtomType), "Cannot use 'Record' type in structured assignment");
                return opt as ResolvedRecordAtomType;
            }));

            const rassign = assign as RecordStructuredAssignment;

            this.raiseErrorIf(sinfo, rectype.options.some((atom) => {
                return (atom as ResolvedRecordAtomType).entries.some((re) => {
                    const entry = rassign.assigns.find((e) => e[0] === re.name);
                    return entry === undefined;
                });
            }), "More values in record that assignment");

            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const aopt = rectype.options.some((atom) => {
                    const entry = (atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname);
                    return (entry === undefined || entry.isOptional);
                });
                const ttype = this.getInfoForLoadFromPropertyName(sinfo, rectype, pname);
                const step = createRecordStructuredAssignmentPathStep(expt, ttype, pname);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, step], rassign.assigns[i][1], ttype, allDeclared, allAssigned);
            }
        }
    }

    private generateAssignOps(sinfo: SourceInfo, ereg: MIRTempRegister, assign: StructuredAssignmentPathStep[]): MIRTempRegister {
        let creg = ereg;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const infertype = this.m_emitter.registerResolvedTypeReference(assign[i].fromtype).trkey;
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;

            if(assign[i].step === "tuple") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, infertype, assign[i].ival, nreg);
            }
            else if(assign[i].step === "record") {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else if(assign[i].step === "nominal") {
                this.m_emitter.bodyEmitter.emitLoadField(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(sinfo, creg, lt, infertype, assign[i].ival, nreg);
            }

            creg = nreg;
        }
        return creg;
    }

    private generateEqualityOps(env: TypeEnvironment, sinfo: SourceInfo, ergtype: ResolvedType, ereg: MIRTempRegister, assign: StructuredAssignmentPathStep[], value: Expression): MIRTempRegister {
        let creg = ereg;
        let ctype = ergtype;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const infertype = this.m_emitter.registerResolvedTypeReference(assign[i].fromtype).trkey;
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;

            if(assign[i].step === "tuple") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, infertype, assign[i].ival, nreg);
            }
            else if(assign[i].step === "record") {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else if(assign[i].step === "nominal") {
                this.m_emitter.bodyEmitter.emitLoadField(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(sinfo, creg, lt, infertype, assign[i].ival, nreg);
            }
            
            creg = nreg;
            ctype = assign[i].t;
        }

        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const vrenv = this.checkExpression(env, value, vreg);
        const vtype = vrenv.getExpressionResult().etype;

        const isstrictlhs = ctype.options.length === 1 && ctype.options[0] instanceof ResolvedEntityAtomType;
        const isstrictrhs = vtype.options.length === 1 && vtype.options[0] instanceof ResolvedEntityAtomType;
        const isstrict = isstrictlhs && isstrictrhs && ctype.idStr === vtype.idStr;

        const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.m_emitter.bodyEmitter.emitBinEq(sinfo, this.m_emitter.registerResolvedTypeReference(ctype).trkey, creg, "==", this.m_emitter.registerResolvedTypeReference(vtype).trkey, vreg, rreg, !isstrict);

        return rreg;
    }

    private generateTypeofOps(sinfo: SourceInfo, ergtype: ResolvedType, ereg: MIRTempRegister, assign: StructuredAssignmentPathStep[], oftype: ResolvedType): MIRTempRegister {
        let creg = ereg;
        let ctype = ergtype;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const infertype = this.m_emitter.registerResolvedTypeReference(assign[i].fromtype).trkey;
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;

            if(assign[i].step === "tuple") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, infertype, assign[i].ival, nreg);
            }
            else if(assign[i].step === "record") {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else if(assign[i].step === "nominal") {
                this.m_emitter.bodyEmitter.emitLoadField(sinfo, lt, creg, infertype, assign[i].nval, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(sinfo, creg, lt, infertype, assign[i].ival, nreg);
            }
            
            creg = nreg;
            ctype = assign[i].t;
        }

        const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.m_emitter.bodyEmitter.emitTypeOf(sinfo, rreg, this.m_emitter.registerResolvedTypeReference(oftype).trkey, this.m_emitter.registerResolvedTypeReference(ctype).trkey, creg);

        return rreg;
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const expreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, { refok: true, orok: true });

        let allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][] = [];
        let allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][] = [];
        this.checkStructuredAssign(stmt.sinfo, env, false, [], stmt.assign, eenv.getExpressionResult().etype, allDeclared, allAssigned);

        if (this.m_emitEnabled) {
            for (let i = 0; i < allDeclared.length; ++i) {
                const declv = allDeclared[i];

                const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                this.m_emitter.bodyEmitter.localLifetimeStart(stmt.sinfo, declv[1], mirvtype.trkey);

                const treg = this.generateAssignOps(stmt.sinfo, expreg, declv[3]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, declv[1]);
            }

            for (let i = 0; i < allAssigned.length; ++i) {
                const assignv = allAssigned[i];

                const treg = this.generateAssignOps(stmt.sinfo, expreg, assignv[1]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, assignv[0]);
            }
        }

        return eenv.multiVarUpdate(allDeclared, allAssigned);
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifstmt_done");

        let cenv = env;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, stmt.flow.conds[i].cond, testreg);

            this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");

            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}true`);
            const falseblck = (i < stmt.flow.conds.length - 1 || stmt.flow.elseAction !== undefined) ? this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}false`) : doneblck;
            if (this.m_emitEnabled) {
                const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType())); 
                this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, isstrict, trueblck, falseblck);
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }

            const truestate = this.checkBlock(TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow.conds[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }

            results.push(truestate);
            cenv = TypeEnvironment.join(this.m_assembly, ...falseflow);
        }

        if (stmt.flow.elseAction === undefined) {
            results.push(cenv);
        }
        else {
            const aenv = this.checkStatement(cenv, stmt.flow.elseAction);
            results.push(aenv);

            if (this.m_emitEnabled && aenv.hasNormalFlow()) {
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
            }
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkStructuredMatch(sinfo: SourceInfo, env: TypeEnvironment, cpath: StructuredAssignmentPathStep[], assign: StructuredAssignment, expt: ResolvedType, allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][], allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][], allChecks: [StructuredAssignmentPathStep[], Expression | ResolvedType][]): [ResolvedType, boolean] {
        if (assign instanceof IgnoreTermStructuredAssignment) {
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms), assign.isOptional];
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            allChecks.push([[...cpath], assign.constValue]);

            const emitRestore = this.m_emitEnabled;
            this.m_emitEnabled = false;

            let ctype = this.checkExpression(env, assign.constValue, this.m_emitter.bodyEmitter.generateTmpRegister()).getExpressionResult().etype;

            this.m_emitEnabled = emitRestore && true;

            return [ctype, false];
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vtype = (assign.isOptional
                    ? this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));

            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], vtype]);
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms), assign.isOptional];
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            allAssigned.push([assign.vname, [...cpath], (vinfo as VarInfo).declaredType]);
            return [(vinfo as VarInfo).declaredType, assign.isOptional];
        }
        else if (assign instanceof NominalStructuredAssignment) {
            const ntype = this.resolveAndEnsureTypeOnly(sinfo, assign.atype, env.terms);
            this.raiseErrorIf(sinfo, ntype.options.length !== 1 || !(ntype.options[0] instanceof ResolvedEntityAtomType || ntype.options[0] instanceof ResolvedConceptAtomType));
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, ntype), "Assign value is not subtype of declared variable type");

            const fieldkeys = assign.assigns.map((asn) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(ntype, "field", asn[0]);
                this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const ffdecl = (fdeclinfo.decl as MemberFieldDecl);
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, ffdecl.declaredType, fdeclinfo.binds);
                return { key: MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, asn[0]), ftype: ftype };
            });

            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = fieldkeys[i].ftype;
                const step = createNominalStructuredAssignmentPathStep(expt, ttype, fieldkeys[i].key);

                let childchecks: [StructuredAssignmentPathStep[], Expression | ResolvedType][] = [];
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, step], assign.assigns[i], ttype, allDeclared, allAssigned, childchecks);

                allChecks.push([[...cpath], einfo[0]])
                allChecks.push(...childchecks);
            }

            return [ntype, false];
        }
        else if (assign instanceof ValueListStructuredAssignment) {
            const eltype = expt.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(sinfo, eltype.types.length !== assign.assigns.length, "Mismatch values in ephemeral list and assignment");
            this.raiseErrorIf(sinfo, expt.options.length !== 1 || !(expt.options[0] instanceof ResolvedEphemeralListType), "Assign value is not subtype of declared variable type");
            
            for (let i = 0; i < assign.assigns.length; ++i) {
                const step = createEphemeralStructuredAssignmentPathStep(expt, eltype.types[i], i);
                this.checkStructuredMatch(sinfo, env, [...cpath, step], assign.assigns[i], eltype.types[i], allDeclared, allAssigned, allChecks);
            }

            return [expt, false];
        }
        else if (assign instanceof TupleStructuredAssignment) {
            const tupopts = expt.options.filter((opt) => opt instanceof ResolvedTupleAtomType);
            this.raiseErrorIf(sinfo, tupopts.length === 0, "Check will always fail");

            const tuptype = ResolvedType.create(tupopts);
            const tupcheck: ResolvedTupleAtomTypeEntry[] = [];
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = this.getInfoForLoadFromIndex(sinfo, tuptype, i);
                const step = createTupleStructuredAssignmentPathStep(expt, ttype, i);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, step], assign.assigns[i], ttype, allDeclared, allAssigned, allChecks);
                tupcheck.push(new ResolvedTupleAtomTypeEntry(...einfo));
            }

            return [ResolvedType.createSingle(ResolvedTupleAtomType.create(tupcheck)), false];
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof RecordStructuredAssignment), "Unknown structured assignment type");

            const recopts = expt.options.filter((opt) => opt instanceof ResolvedRecordAtomType);
            this.raiseErrorIf(sinfo, recopts.length === 0, "Check will always fail");

            const rassign = assign as RecordStructuredAssignment;
            const rectype = ResolvedType.create(recopts);
            const reccheck: ResolvedRecordAtomTypeEntry[] = [];
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const ttype = this.getInfoForLoadFromPropertyName(sinfo, rectype, pname);
                const step = createRecordStructuredAssignmentPathStep(expt, ttype, pname);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, step], rassign.assigns[i][1], ttype, allDeclared, allAssigned, allChecks);
                reccheck.push(new ResolvedRecordAtomTypeEntry(pname, ...einfo));
            }

            return [ResolvedType.createSingle(ResolvedRecordAtomType.create(reccheck)), false];
        }
    }

    private checkMatchGuard(sinfo: SourceInfo, midx: number, vreg: MIRTempRegister, sexp: ResolvedType, env: TypeEnvironment, guard: MatchGuard, nextlabel: string, actionlabel: string, svname: string | undefined, lastoption: boolean): { envinfo: TypeEnvironment[], nexttype: ResolvedType } {
        let opts: TypeEnvironment[] = [];
        let nexttype = sexp;
        let mreg = this.m_emitter.bodyEmitter.generateTmpRegister();

        if (guard instanceof WildcardMatchGuard) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);
            }

            opts = [env.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);

            if (this.m_emitEnabled) {
                const mt = this.m_emitter.registerResolvedTypeReference(tmatch);
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, mreg, mt.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);
            }

            if (svname === undefined) {
                opts = [env.setExpressionResult(this.m_assembly.getSpecialBoolType())];
            }
            else {
                //TODO: we have cases like this where we may want to have these checked in the "live programming env" but not block compilation as dead flow when template specializing
                //this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, tmatch).isEmptyType(), "Value is never of type");
                this.raiseErrorIf(sinfo, !lastoption && this.m_assembly.restrictNotT(sexp, tmatch).isEmptyType(), "Value is always of type");

                const tval = env
                    .assumeVar(svname, this.m_assembly.restrictT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True);

                const ntval = env
                    .assumeVar(svname, this.m_assembly.restrictNotT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False);

                opts = [tval, ntval];
            }

            if(guard.optionalWhen === undefined) {
                nexttype = this.m_assembly.restrictNotT(sexp, tmatch);
            }
        }
        else {
            const sguard = guard as StructureMatchGuard;

            let allDeclared: [boolean, string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][] = [];
            let allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][] = [];
            let allChecks: [StructuredAssignmentPathStep[], Expression | ResolvedType][] = [];
            const oftype = this.checkStructuredMatch(sinfo, env, [], sguard.match, sexp, allDeclared, allAssigned, allChecks)[0];

            if (this.m_emitEnabled) {
                const oft = this.m_emitter.registerResolvedTypeReference(oftype);
                const tcreg = this.m_emitter.bodyEmitter.generateTmpRegister();

                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, tcreg, oft.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);

                const filllabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_scfill`);
                if (allChecks.length === 0) {
                    this.m_emitter.bodyEmitter.emitRegAssign(sinfo, tcreg, mreg);
                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }
                else {
                    const eqlabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_sceq`);
                    this.m_emitter.bodyEmitter.emitBoolJump(sinfo, tcreg, true, eqlabel, nextlabel);

                    this.m_emitter.bodyEmitter.setActiveBlock(eqlabel);
                    this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);

                    for (let i = 0; i < allChecks.length; ++i) {
                        const nexttestlabel = this.m_emitter.bodyEmitter.createNewBlock(`match${i}_test`);

                        if (allChecks[i][1] instanceof Expression) {
                            const eqreg = this.generateEqualityOps(env, sinfo, sexp, vreg, allChecks[i][0], allChecks[i][1] as Expression);
                            this.m_emitter.bodyEmitter.emitRegAssign(sinfo, eqreg, mreg);
                        }
                        else {
                            const okreg = this.generateTypeofOps(sinfo, sexp, vreg, allChecks[i][0], allChecks[i][1] as ResolvedType);
                            this.m_emitter.bodyEmitter.emitRegAssign(sinfo, okreg, mreg);
                        }

                        this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, true, nexttestlabel, filllabel);
                        this.m_emitter.bodyEmitter.setActiveBlock(nexttestlabel);
                    }

                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(filllabel);
                for (let i = 0; i < allDeclared.length; ++i) {
                    const declv = allDeclared[i];

                    const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                    this.m_emitter.bodyEmitter.localLifetimeStart(sinfo, declv[1], mirvtype.trkey);

                    const treg = this.generateAssignOps(sinfo, vreg, declv[3]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, declv[1]);
                }

                for (let i = 0; i < allAssigned.length; ++i) {
                    const assignv = allAssigned[i];

                    const treg = this.generateAssignOps(sinfo, vreg, assignv[1]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, assignv[0]);
                }
            }

            if (svname === undefined) {
                opts = [
                    env.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                    env.multiVarUpdate(allDeclared, allAssigned).setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
                ];
            }
            else {
                this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, oftype).isEmptyType(), "Value is never of type");

                const tval = env
                        .assumeVar(svname, this.m_assembly.restrictT(sexp, oftype))
                        .multiVarUpdate(allDeclared, allAssigned)
                        .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True);

                const ntval = env.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False);

                opts = [tval, ntval];
            }

            if(oftype.isNoneType()) {
                nexttype = this.m_assembly.restrictSome(sexp);
            }
            else {
                nexttype = sexp;
            }
        }

        if (guard.optionalWhen === undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, true, actionlabel, nextlabel);
            }

            return { envinfo: opts, nexttype: nexttype };
        }
        else {
            const [gtrueflow, gfalseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, opts);

            if (this.m_emitEnabled) {
                const whenblck = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_when`);
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, true, whenblck, nextlabel);

                this.m_emitter.bodyEmitter.setActiveBlock(whenblck);
            }

            let wreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const wopts = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...gtrueflow), guard.optionalWhen, wreg);

            const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
            this.raiseErrorIf(sinfo, wopts.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                const isstrict = wopts.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, wreg, isstrict, actionlabel, nextlabel);
            }

            const [wtrueflow, wfalseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, wopts);

            return { envinfo: [...wtrueflow, ...gfalseflow, ...wfalseflow], nexttype: nexttype };
        }
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg);

        const svname = stmt.sval instanceof AccessVariableExpression ? stmt.sval.name : undefined;

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchstmt_done");

        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, i, vreg, vtype, cenv, stmt.flow[i].check, nextlabel, actionlabel, svname, i === stmt.flow.length - 1);

            vtype = test.nexttype;
            const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== stmt.flow.length - 1) , "Expression is always true/false expression test is redundant");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }

            const truestate = this.checkBlock(TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }

                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }

            results.push(truestate);
            cenv = falseflow.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }

        //do an exhaustive check in one case we know
        if (!stmt.flow.some((gc) => gc.check instanceof WildcardMatchGuard)) {
            this.m_exhaustiveChecks.push({file: this.m_file, sinfo: stmt.sinfo, vtype: vtype, chk: stmt.flow.map((cc) => cc.check)});
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, "exhaustive");
        }

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkNakedCallStatement(env: TypeEnvironment, stmt: NakedCallStatement): TypeEnvironment {
        const rdiscard = this.m_emitter.bodyEmitter.generateTmpRegister();

        if(stmt.call instanceof CallNamespaceFunctionExpression) {
            const cenv = this.checkCallNamespaceFunctionExpression(env, stmt.call as CallNamespaceFunctionExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
        else { 
            const cenv = this.checkCallStaticFunctionExpression(env, stmt.call as CallStaticFunctionExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

        if (stmt.values.length === 1) {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.values[0], etreg, { refok: true, orok: false });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, etreg);
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "returnassign");
            }

            return env.setReturn(this.m_assembly, venv.getExpressionResult().etype);
        }
        else {
            let regs: MIRTempRegister[] = [];
            let rtypes: ResolvedType[] = [];
            for (let i = 0; i < stmt.values.length; ++i) {
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg);

                regs.push(etreg);
                rtypes.push(venv.getExpressionResult().etype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            if (this.m_emitEnabled) {
                const elreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype).trkey, regs, elreg);
                
                this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, elreg);
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "returnassign");
            }

            return env.setReturn(this.m_assembly, etype);
        }
    }

    private checkYieldStatement(env: TypeEnvironment, stmt: YieldStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");
        const yinfo = env.getYieldTargetInfo();

        if (stmt.values.length === 1) {
            const venv = this.checkExpression(env, stmt.values[0], yinfo[0], { refok: true, orok: false });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, yinfo[1]);
                this.m_emitter.bodyEmitter.setActiveBlock(yinfo[1]);
            }

            return env.setYield(this.m_assembly, venv.getExpressionResult().etype);
        }
        else {
            let regs: MIRTempRegister[] = [];
            let rtypes: ResolvedType[] = [];
            for (let i = 0; i < stmt.values.length; ++i) {
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg);

                regs.push(etreg);
                rtypes.push(venv.getExpressionResult().etype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype).trkey, regs, yinfo[0]);
                
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, yinfo[1]);
                this.m_emitter.bodyEmitter.setActiveBlock(yinfo[1]);
            }

            return env.setYield(this.m_assembly, etype);
        }
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, "abort");
        }

        return env.setAbort();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const trueflow = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test)[0];
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0, "Expression is always true/false assert is redundant");

        if (this.m_emitEnabled && isBuildLevelEnabled(stmt.level, this.m_buildLevel)) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_fail");
            const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, isstrict, doneblck, failblck);

            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, "assert fail");

            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...trueflow);
    }

    private checkCheckStatement(env: TypeEnvironment, stmt: CheckStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const trueflow = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test)[0];
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0, "Expression is always true/false check is redundant");

        if (this.m_emitEnabled) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_fail");
            const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, isstrict, doneblck, failblck);

            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, "check fail");

            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...trueflow);
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        if (stmt.value === undefined) {
            if (this.m_emitEnabled && this.m_buildLevel === "debug") {
                this.m_emitter.bodyEmitter.emitDebugBreak(stmt.sinfo);
            }
        }
        else {
            const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.checkExpression(env, stmt.value, vreg);

            if (this.m_emitEnabled && this.m_buildLevel !== "release") {
                this.m_emitter.bodyEmitter.emitDebugPrint(stmt.sinfo, vreg);
            }
        }

        return env;
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const [trueflow, errorflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0, "Expression is always true/false check is redundant");

        this.raiseErrorIf(stmt.sinfo, env.result.options.length !== 1 && !env.result.options[0].idStr.startsWith("NSCore::Result<"), "Return type must be Result<T, E> when using validate");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_done");
        const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_fail");
        if (this.m_emitEnabled) {
            const isstrict = test.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, isstrict, doneblck, failblck);
            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
        }

        const errreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const errflow = TypeEnvironment.join(this.m_assembly, ...errorflow.map((te) => te.setReturn(this.m_assembly, env.result)));
        const errenv = this.checkExpression(errflow, stmt.err, errreg);

        const errres = errenv.getExpressionResult().etype;
        if (this.m_emitEnabled) {
            if (stmt.err instanceof LiteralNoneExpression) {
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(this.m_assembly.getSpecialNoneType(), env.result));
            }
            else {
                this.raiseErrorIf(stmt.sinfo, errres.options.length !== 1 && !(errres.options[0].idStr.startsWith("NSCore::Result<") || errres.options[0].idStr.startsWith("NSCore::Err<")));
            }

            this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, errreg);
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "returnassign");

            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }

        return TypeEnvironment.join(this.m_assembly, ...trueflow, errenv.setReturn(this.m_assembly, errenv.getExpressionResult().etype));
    }

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");

        switch (stmt.tag) {
            case StatementTag.EmptyStatement:
                return env;
            case StatementTag.VariableDeclarationStatement:
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement);
            case StatementTag.VariablePackDeclarationStatement:
                return this.checkVariablePackDeclarationStatement(env, stmt as VariablePackDeclarationStatement);
            case StatementTag.VariableAssignmentStatement:
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement);
            case StatementTag.VariablePackAssignmentStatement:
                return this.checkVariablePackAssignmentStatement(env, stmt as VariablePackAssignmentStatement);
            case StatementTag.StructuredVariableAssignmentStatement:
                return this.checkStructuredVariableAssignmentStatement(env, stmt as StructuredVariableAssignmentStatement);
            case StatementTag.IfElseStatement:
                return this.checkIfElseStatement(env, stmt as IfElseStatement);
            case StatementTag.MatchStatement:
                return this.checkMatchStatement(env, stmt as MatchStatement);
            case StatementTag.NakedCallStatement:
                return this.checkNakedCallStatement(env, stmt as NakedCallStatement);
            case StatementTag.ReturnStatement:
                return this.checkReturnStatement(env, stmt as ReturnStatement);
            case StatementTag.YieldStatement:
                return this.checkYieldStatement(env, stmt as YieldStatement);
            case StatementTag.AbortStatement:
                return this.checkAbortStatement(env, stmt as AbortStatement);
            case StatementTag.AssertStatement:
                return this.checkAssertStatement(env, stmt as AssertStatement);
            case StatementTag.CheckStatement:
                return this.checkCheckStatement(env, stmt as CheckStatement);
            case StatementTag.DebugStatement:
                return this.checkDebugStatement(env, stmt as DebugStatement);
            case StatementTag.ValidateStatement:
                return this.checkValidateStatement(env, stmt as ValidateStatement);
            default:
                this.raiseErrorIf(stmt.sinfo, stmt.tag !== StatementTag.BlockStatement, "Unknown statement");
                return this.checkBlock(env, stmt as BlockStatement);
        }
    }

    private checkBlock(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        let cenv = env.pushLocalScope();

        for (let i = 0; i < stmt.statements.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, stmt.statements[i]);
        }

        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(stmt.sinfo, deadvars[i]);
            }
        }

        return cenv.popLocalScope();
    }

    private emitPrelogForRefParamsAndPostCond(sinfo: SourceInfo, env: TypeEnvironment): string[] {
        let rpnames: string[] = [];

        for(let i = 0; i < env.refparams.length; ++i) {
            rpnames.push(`$_orig_$${env.refparams[i]}`);
            this.m_emitter.bodyEmitter.emitArgVarStore(sinfo, env.refparams[i], `$_orig_$${env.refparams[i]}`);
        }

        return rpnames;
    }

    private emitPrologForReturn(sinfo: SourceInfo, rrinfo: [MIRType, MIRType, number, [string, MIRType][]], wpost: boolean): {unpack: MIRArgument[], orefs: MIRArgument[]} {
        if(wpost) {
            this.m_emitter.bodyEmitter.emitVarMove(sinfo, "$__ir_ret__", "$$__post_arg__");
        }

        let rargs: MIRArgument[] = [new MIRVariable("$$__post_arg__")];
        let orefs: MIRArgument[] = rrinfo[3].map((rv) => new MIRVariable(`$_orig_$${rv}`));
        if(rrinfo[3].length === 0) {
            this.m_emitter.bodyEmitter.emitVarMove(sinfo, "$__ir_ret__", "$$return");
        }
        else {
            const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();

            if(rrinfo[2] === -1) {
                let args = [new MIRVariable("$__ir_ret__"), ...rrinfo[3].map((rv) => new MIRVariable(rv[0]))];
                this.m_emitter.bodyEmitter.emitConstructorValueList(sinfo, rrinfo[1].trkey, args, rreg);
            }
            else {
                if (wpost) {
                    rargs = [];
                    const elreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitAccessLocalVariable(sinfo, "$__ir_ret__", elreg);
                    for (let i = 0; i < rrinfo[2]; ++i) {
                        const tlreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        const lt = (rrinfo[0].options[0] as MIREphemeralListType).entries[i];
                        this.m_emitter.bodyEmitter.emitLoadFromEpehmeralList(sinfo, elreg, lt.trkey, rrinfo[1].trkey, i, tlreg);

                        rargs.push(tlreg);
                    }
                }
                
                let args: MIRArgument[] = [new MIRVariable("$__ir_ret__")];
                for(let i = 0; i < rrinfo[3].length; ++i) {
                    args.push(new MIRVariable(rrinfo[3][i][0]));
                }

                this.m_emitter.bodyEmitter.emitMIRPackExtend(sinfo, new MIRVariable("$__ir_ret__"), args, rrinfo[1].trkey, rreg);
            }

            this.m_emitter.bodyEmitter.emitVarStore(sinfo, rreg, "$$return");
        }

        return {unpack: rargs, orefs: orefs};
    }

    private checkBody(env: TypeEnvironment, body: BodyImplementation, args: Map<string, MIRType>, declaredResultType: ResolvedType, preject: [MIRInvokeKey, MIRArgument[]] | undefined, postject: [MIRInvokeKey, MIRArgument[]] | undefined): MIRBody | undefined {
        if (body.body instanceof Expression) {
            this.raiseErrorIf(body.body.sinfo, env.refparams.length !== 0, "Ref params on expression bodies are not allowed");

            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();

                if(preject !== undefined) {
                    const prereg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const prefail = this.m_emitter.bodyEmitter.createNewBlock("prefail");
                    const preok = this.m_emitter.bodyEmitter.createNewBlock("preok");

                    const mirbool = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType());
                    this.m_emitter.bodyEmitter.emitInvokeFixedFunction(body.body.sinfo, preject[0], preject[1], [mirbool, mirbool, -1, []], prereg);
                    this.m_emitter.bodyEmitter.emitBoolJump(body.body.sinfo, prereg, true, preok, prefail);

                    this.m_emitter.bodyEmitter.setActiveBlock(prefail);
                    this.m_emitter.bodyEmitter.emitAbort(body.body.sinfo, "Fail pre-condition");

                    this.m_emitter.bodyEmitter.setActiveBlock(preok);
                }
            }

            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const evalue = this.checkExpression(env, body.body, etreg);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitReturnAssign(body.body.sinfo, etreg);
                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "returnassign");

                this.m_emitter.bodyEmitter.setActiveBlock("returnassign");
                
                const rrinfo = this.generateRefInfoForReturnEmit(body.body.sinfo, evalue.getExpressionResult().etype, env);
                const postvar = this.emitPrologForReturn(body.body.sinfo, rrinfo, postject !== undefined);

                if (postject !== undefined) {
                    const postreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const postfail = this.m_emitter.bodyEmitter.createNewBlock("postfail");
                    const postok = this.m_emitter.bodyEmitter.createNewBlock("postok");

                    const mirbool = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType());
                    const postargs = [...postvar.unpack, ...postvar.orefs, ...postject[1]];

                    this.m_emitter.bodyEmitter.emitInvokeFixedFunction(body.body.sinfo, postject[0], postargs, [mirbool, mirbool, -1, []], postreg);
                    this.m_emitter.bodyEmitter.emitBoolJump(body.body.sinfo, postreg, true, postok, postfail);

                    this.m_emitter.bodyEmitter.setActiveBlock(postfail);
                    this.m_emitter.bodyEmitter.emitAbort(body.body.sinfo, "Fail post-condition");

                    this.m_emitter.bodyEmitter.setActiveBlock(postok);
                }
                
                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "exit");
            }
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, declaredResultType), "Did not produce the expected return type");

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, args) : undefined;
        }
        else if (body.body instanceof BlockStatement) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();

                if(preject !== undefined) {
                    const prereg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const prefail = this.m_emitter.bodyEmitter.createNewBlock("prefail");
                    const preok = this.m_emitter.bodyEmitter.createNewBlock("preok");

                    const mirbool = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType());
                    this.m_emitter.bodyEmitter.emitInvokeFixedFunction(body.body.sinfo, preject[0], preject[1], [mirbool, mirbool, -1, []], prereg);
                    this.m_emitter.bodyEmitter.emitBoolJump(body.body.sinfo, prereg, true, preok, prefail);

                    this.m_emitter.bodyEmitter.setActiveBlock(prefail);
                    this.m_emitter.bodyEmitter.emitAbort(body.body.sinfo, "Fail pre-condition");

                    this.m_emitter.bodyEmitter.setActiveBlock(preok);
                }
            }

            if(postject !== undefined) {
                this.emitPrelogForRefParamsAndPostCond(body.body.sinfo, env);
            }

            const renv = this.checkBlock(env, body.body);
            this.raiseErrorIf(body.body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(renv.returnResult as ResolvedType, declaredResultType), "Did not produce the expected return type");

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock("returnassign");

                const rrinfo = this.generateRefInfoForReturnEmit(body.body.sinfo, renv.returnResult as ResolvedType, env);
                const postvar = this.emitPrologForReturn(body.body.sinfo, rrinfo, postject !== undefined);

                if (postject !== undefined) {
                    const postreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const postfail = this.m_emitter.bodyEmitter.createNewBlock("postfail");
                    const postok = this.m_emitter.bodyEmitter.createNewBlock("postok");

                    const mirbool = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType());
                    const postargs = [...postvar.unpack, ...postvar.orefs, ...postject[1]];

                    this.m_emitter.bodyEmitter.emitInvokeFixedFunction(body.body.sinfo, postject[0], postargs, [mirbool, mirbool, -1, []], postreg);
                    this.m_emitter.bodyEmitter.emitBoolJump(body.body.sinfo, postreg, true, postok, postfail);

                    this.m_emitter.bodyEmitter.setActiveBlock(postfail);
                    this.m_emitter.bodyEmitter.emitAbort(body.body.sinfo, "Fail post-condition");

                    this.m_emitter.bodyEmitter.setActiveBlock(postok);
                }

                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "exit");
            }

            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, args) : undefined;
        }
        else {
            return undefined;
        }
    }

    private abortIfTooManyErrors() {
        if (this.m_errors.length > 20) {
            throw new Error("More than 20 errors ... halting type checker");
        }
    }

    private processPragmas(sinfo: SourceInfo, pragmas: [TypeSignature, string][]): [MIRType, string][] {
        const emptybinds = new Map<string, ResolvedType>();

        return pragmas.map((prg) => {
            const ptype = this.resolveAndEnsureTypeOnly(sinfo, prg[0], emptybinds);
            const pkey = this.m_emitter.registerResolvedTypeReference(ptype);
            return [pkey, prg[1]] as [MIRType, string];
        });
    }

    private processGenerateSpecialExpFunction(fkey: MIRInvokeKey, iname: string, binds: Map<string, ResolvedType>, exp: Expression, rtype: TypeSignature, srcFile: string, sinfo: SourceInfo) {
        try {
            const body = new BodyImplementation(`${srcFile}::${sinfo.pos}`, srcFile, exp);
            const resultType = this.m_assembly.normalizeTypeOnly(rtype, binds);

            const invinfo = this.processInvokeInfo_Simplified(undefined, iname, fkey, sinfo, srcFile, [], [], resultType, new Map<string, VarInfo>(), new Map<string, MIRType>(), body, binds);
            this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processGenerateSpecialInvariantDirectFunction(fkey: MIRInvokeKey, iname: string, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>, exps: Expression[], srcFile: string, sinfo: SourceInfo) {
        try {
            let bexp = exps[0];
            for(let i = 1; i < exps.length; ++i) {
                bexp = new BinLogicExpression(sinfo, bexp, "&&", exps[i]);
            }

            const fields = this.m_assembly.getAllOOFields(tdecl, binds);
            let fps: MIRFunctionParameter[] = [];
            let cargs = new Map<string, VarInfo>();
            let argTypes = new Map<string, MIRType>();
            [...fields].forEach((finfo) => {
                    const fname = `$${finfo[1][1].name}`;
                    const ftype = this.m_assembly.normalizeTypeOnly(finfo[1][1].declaredType, finfo[1][2]);
                    const mirftype = this.m_emitter.registerResolvedTypeReference(ftype);

                    fps.push(new MIRFunctionParameter(fname, mirftype.trkey));
                    cargs.set(fname, new VarInfo(ftype, true, false, true, ftype));
                    argTypes.set(fname, mirftype);
                });

            const body = new BodyImplementation(`${srcFile}::${sinfo.pos}`, srcFile, bexp);
            const invinfo = this.processInvokeInfo_Simplified(undefined, iname, fkey, sinfo, srcFile, [], fps, this.m_assembly.getSpecialBoolType(), cargs, argTypes, body, binds);
            this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processGenerateSpecialInvariantFunction(sinfo: SourceInfo, srcFile: string, iname: string, ikey: MIRInvokeKey, mirthistype: MIRType, fields: [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>][], callkeys: {ivk: MIRInvokeKey, args: {name: string, t: ResolvedType}[]}[]) {
        const be = new MIRBodyEmitter();
        be.initialize();
        const failblock = be.createNewBlock("failure");

        const mirbooltype = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType());
        const etreg = be.generateTmpRegister();
        be.emitLoadConstBool(sinfo, true, etreg);

        for (let i = 0; i < callkeys.length; ++i) {
            const args = callkeys[i].args.map((arg) => new MIRVariable(arg.name));
            be.emitInvokeFixedFunction(sinfo, callkeys[i].ivk, args, [mirbooltype, mirbooltype, -1, []], etreg);

            const nexttest = be.createNewBlock("next");
            be.emitBoolJump(sinfo, etreg, true, nexttest, failblock);

            be.setActiveBlock(nexttest);
        }

        be.emitReturnAssign(sinfo, etreg);
        be.emitDirectJump(sinfo, "returnassign");

        be.setActiveBlock(failblock);
        be.emitReturnAssign(sinfo, etreg);
        be.emitDirectJump(sinfo, "returnassign");

        be.setActiveBlock("returnassign");
        be.emitVarMove(sinfo, "$__ir_ret__", "$$return");
        be.emitDirectJump(sinfo, "exit");

        let mirparams: MIRFunctionParameter[] = [];
        let argTypes = new Map<string, MIRType>();
        fields.forEach((finfo) => {
                const fname = `$${finfo[1].name}`;
                const ftype = this.m_assembly.normalizeTypeOnly(finfo[1].declaredType, finfo[2]);
                const mirftype = this.m_emitter.registerResolvedTypeReference(ftype);

                mirparams.push(new MIRFunctionParameter(fname, mirftype.trkey));
                argTypes.set(fname, mirftype);
            });
        
        
        const mirbody = be.getBody(this.m_file, sinfo, argTypes);
        const ibody = new MIRInvokeBodyDecl(mirthistype.trkey, "[SPECIAL]", iname, ikey, [], false, [], sinfo, srcFile, mirparams, mirbooltype.trkey, undefined, undefined, mirbody as MIRBody);

        this.m_emitter.masm.invokeDecls.set(ikey, ibody);
    }

    private processGenerateSpecialPreFunction_FailFast(fkey: MIRInvokeKey, iname: string, args: FunctionParameter[], declbinds: Map<string, ResolvedType>, exps: PreConditionDecl[], bodybinds: Map<string, ResolvedType>, srcFile: string, sinfo: SourceInfo) {
        if(this.m_emitter.masm.invokeDecls.has(fkey)) {
            return;
        }

        try {
            let bexp = exps[0].exp;
            for(let i = 1; i < exps.length; ++i) {
                bexp = new BinLogicExpression(sinfo, bexp, "&&", exps[i].exp);
            }

            let fps: MIRFunctionParameter[] = [];
            let cargs = new Map<string, VarInfo>();
            let argTypes = new Map<string, MIRType>();
            args.forEach((arg) => {
                    //
                    //TODO: we are skipping the case of Lambda bindings in the precondition
                    //      need to support this later
                    //
                    if (!(arg.type instanceof FunctionTypeSignature)) {
                        const pdecltype = this.m_assembly.normalizeTypeOnly(arg.type, declbinds);
                        const ptype = arg.isOptional ? this.m_assembly.typeUpperBound([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                        const mirptype = this.m_emitter.registerResolvedTypeReference(ptype);

                        fps.push(new MIRFunctionParameter(arg.name, mirptype.trkey));
                        cargs.set(arg.name, new VarInfo(ptype, true, false, true, ptype));
                        argTypes.set(arg.name, mirptype);
                    }
                });

            const body = new BodyImplementation(`${srcFile}::${sinfo.pos}`, srcFile, bexp);

            const invinfo = this.processInvokeInfo_Simplified(undefined, iname, fkey, sinfo, srcFile, [], fps, this.m_assembly.getSpecialBoolType(), cargs, argTypes, body, bodybinds);
            this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processGenerateSpecialPreFunction_ResultT(sinfo: SourceInfo, exps: PreConditionDecl[], body: BodyImplementation): BodyImplementation {
        if (body.body instanceof Expression) {
            const ops = exps.map((pc) => {
                return new CondBranchEntry<Expression>(new PrefixOp(pc.sinfo, "!", pc.exp), pc.err as Expression);
            });
            const ite = new IfExpression(sinfo, new IfElse<Expression>(ops, body.body as Expression));

            return new BodyImplementation(body.id, body.file, ite);
        }
        else {
            const ops = exps.map((pc) => {
                return new CondBranchEntry<BlockStatement>(new PrefixOp(pc.sinfo, "!", pc.exp), new BlockStatement((pc.err as Expression).sinfo, [new ReturnStatement((pc.err as Expression).sinfo, [pc.err as Expression])]));
            });
            const ite = new IfElseStatement(sinfo, new IfElse<BlockStatement>(ops, body.body as BlockStatement));

            return new BodyImplementation(body.id, body.file, new BlockStatement(sinfo, [ite]));
        }
    }

    private processGenerateSpecialPostFunction(fkey: MIRInvokeKey, iname: string, args: FunctionParameter[], resultType: ResolvedType, declbinds: Map<string, ResolvedType>, exps: PostConditionDecl[], bodybinds: Map<string, ResolvedType>, srcFile: string, sinfo: SourceInfo) {
        if(this.m_emitter.masm.invokeDecls.has(fkey)) {
            return;
        }

        try {
            let bexp = exps[0].exp;
            for(let i = 1; i < exps.length; ++i) {
                bexp = new BinLogicExpression(sinfo, bexp, "&&", exps[i].exp);
            }
            
            let fps: MIRFunctionParameter[] = [];
            let cargs = new Map<string, VarInfo>();
            let argTypes = new Map<string, MIRType>();
            args.forEach((arg) => {
                    //
                    //TODO: we are skipping the case of Lambda bindings in the precondition
                    //      need to support this later
                    //
                    if (!(arg.type instanceof FunctionTypeSignature)) {
                        const pdecltype = this.m_assembly.normalizeTypeOnly(arg.type, declbinds);
                        const ptype = arg.isOptional ? this.m_assembly.typeUpperBound([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                        const mirptype = this.m_emitter.registerResolvedTypeReference(ptype);

                        fps.push(new MIRFunctionParameter(arg.name, mirptype.trkey));
                        cargs.set(arg.name, new VarInfo(ptype, true, false, true, ptype));
                        argTypes.set(arg.name, mirptype);
                    }
                });

            let rprs: MIRFunctionParameter[] = [];
            if (resultType.options.length === 1 && !(resultType.options[0] instanceof ResolvedEphemeralListType)) {
                const rtype = this.m_emitter.registerResolvedTypeReference(resultType);

                rprs.push(new MIRFunctionParameter("$return", rtype.trkey));
                cargs.set("$return", new VarInfo(resultType, true, false, true, resultType));
                argTypes.set("$return", rtype);
            }
            else {
                const epl = (resultType.options[0] as ResolvedEphemeralListType)
                for(let i = 0; i < epl.types.length; ++i) {
                    const ritype = this.m_emitter.registerResolvedTypeReference(epl.types[i]);

                    rprs.push(new MIRFunctionParameter(`$return_${i}`, ritype.trkey));
                    cargs.set(`$return_${i}`, new VarInfo(epl.types[i], true, false, true, epl.types[i]));
                    argTypes.set(`$return_${i}`, ritype);
                }
            }

            let rreforig: MIRFunctionParameter[] = [];
            args.forEach((arg) => {
                if (arg.isRef) {
                    const pdecltype = this.m_assembly.normalizeTypeOnly(arg.type, declbinds);
                    const ptype = arg.isOptional ? this.m_assembly.typeUpperBound([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                    const mirptype = this.m_emitter.registerResolvedTypeReference(ptype);

                    const oname = `$${arg.name}`;
                    rreforig.push(new MIRFunctionParameter(oname, mirptype.trkey));
                    cargs.set(oname, new VarInfo(ptype, true, false, true, ptype));
                    argTypes.set(oname, mirptype);
                }
            });
            
            const body = new BodyImplementation(`${srcFile}::${sinfo.pos}`, srcFile, bexp);

            const invinfo = this.processInvokeInfo_Simplified(undefined, iname, fkey, sinfo, srcFile, [], [...rprs, ...rreforig, ...fps], this.m_assembly.getSpecialBoolType(), cargs, argTypes, body, bodybinds);
            this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processOOType(tkey: MIRNominalTypeKey, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = this.m_assembly.resolveProvides(tdecl, binds).map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new SourceInfo(0, 0, 0, 0), provide, binds);
                const cpt = ((ptype.options[0]) as ResolvedConceptAtomType).conceptTypes[0];

                this.m_emitter.registerTypeInstantiation(cpt.concept, cpt.binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).trkey;
            });

            if(tdecl.invariants.length !== 0) {
                const fkey = MIRKeyGenerator.generateStaticKey(tdecl, "@invariant_direct", binds, []);
                this.processGenerateSpecialInvariantDirectFunction(fkey, `${tkey}::invariant_direct`, tdecl, binds, tdecl.invariants.map((inv) => inv.exp), tdecl.srcFile, tdecl.sourceLocation);
            }

            let allinvariants = this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds);
            let allinvariantcalls = allinvariants.map((iinfo) => MIRKeyGenerator.generateStaticKey(iinfo[1], "@invariant_direct", iinfo[2], []))
            if(allinvariants.length !== 0 && tdecl instanceof EntityTypeDecl) {
                const fkey = MIRKeyGenerator.generateStaticKey(tdecl, "@@invariant", binds, []);
                const mirthistype = this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(ResolvedEntityAtomType.create(tdecl, binds)));
                
                const fields = this.m_assembly.getAllOOFields(tdecl, binds);
                const allfields = [...fields].map((field) => field[1]);

                const invcallinfo = allinvariants.map((invinfo) => {
                    const icall =  MIRKeyGenerator.generateStaticKey(invinfo[1], "@invariant_direct", invinfo[2], []);

                    const fields = [...this.m_assembly.getAllOOFields(tdecl, binds)];
                    const cargs = fields.map((finfo) => ({name: `$${finfo[1][1].name}`, t: this.m_assembly.normalizeTypeOnly(finfo[1][1].declaredType, finfo[1][2])}));

                    return {ivk: icall, args: cargs};
                });

                this.processGenerateSpecialInvariantFunction(tdecl.sourceLocation, tdecl.srcFile, `${tkey}::invariant`, fkey, mirthistype, allfields, invcallinfo);
                allinvariantcalls.push(fkey);
            }
            
            //
            //TODO: we need to check inheritance and provides rules here -- diamonds, virtual/abstract/override use, etc.
            //

            const fields: MIRFieldDecl[] = [];
            const finfos = [...this.m_assembly.getAllOOFields(tdecl, binds)];
            finfos.forEach((ff) => {
                const fi = ff[1];
                const f = fi[1];

                const fkey = MIRKeyGenerator.generateFieldKey(fi[0], fi[2], f.name);
                if (!this.m_emitter.masm.fieldDecls.has(fkey)) {
                    let dkey: string | undefined = undefined;

                    //only generate this if this is the declaring (enclosing) type
                    if (f.value !== undefined && fi[0].ns === tdecl.ns && fi[0].name === tdecl.name) {
                        dkey = MIRKeyGenerator.generateStaticKey(fi[0], `${f.name}@@cons`, fi[2], []);
                        const iname = `${MIRKeyGenerator.generateTypeKey(fi[0], fi[2])}::${f.name}@@cons`;
                        this.processGenerateSpecialExpFunction(dkey, iname, new Map<string, ResolvedType>(), f.value as Expression, f.declaredType, f.srcFile, f.sourceLocation);
                    }


                    const fpragmas = this.processPragmas(f.sourceLocation, f.pragmas);
                    const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                    const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);

                    const fname = `${fi[0].ns}::${fi[0].name}.${f.name}`;
                    const mfield = new MIRFieldDecl(tkey, f.attributes, fname, f.sourceLocation, f.srcFile, fkey, fpragmas, f.name, dtype.trkey, dkey);
                    this.m_emitter.masm.fieldDecls.set(fkey, mfield);
                }

                fields.push(this.m_emitter.masm.fieldDecls.get(fkey) as MIRFieldDecl);
            });

            const ooname = `${tdecl.ns}::${tdecl.name}`;
            const pragmas = this.processPragmas(tdecl.sourceLocation, tdecl.pragmas);

            if (tdecl instanceof EntityTypeDecl) {
                const mirentity = new MIREntityTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, allinvariantcalls, fields);
                this.m_emitter.masm.entityDecls.set(tkey, mirentity);
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, allinvariantcalls, fields);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processGlobal(gkey: MIRConstantKey, gdecl: NamespaceConstDecl) {
        try {
            const fkey = MIRKeyGenerator.generateFunctionKey(gdecl.ns, `${gdecl.name}@@cons`, new Map<string, ResolvedType>(), []);
            const iname = `${gdecl.ns}::${gdecl.name}@@cons`;

            this.processGenerateSpecialExpFunction(fkey, iname, new Map<string, ResolvedType>(), gdecl.value, gdecl.declaredType, gdecl.srcFile, gdecl.sourceLocation);

            const pragmas = this.processPragmas(gdecl.sourceLocation, gdecl.pragmas);
            const ddecltype = this.resolveAndEnsureTypeOnly(gdecl.sourceLocation, gdecl.declaredType, new Map<string, ResolvedType>());
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const mirglobal = new MIRConstantDecl(undefined, `${gdecl.ns}::${gdecl.name}`, gkey, pragmas, gdecl.sourceLocation, gdecl.srcFile, dtype.trkey, fkey);

            this.m_emitter.masm.constantDecls.set(gkey, mirglobal);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processConst(ckey: MIRConstantKey, containingDecl: OOPTypeDecl, cdecl: StaticMemberDecl, binds: Map<string, ResolvedType>) {
        try {
            const fkey = MIRKeyGenerator.generateStaticKey(containingDecl, `${cdecl.name}@@cons`, binds, []);
            const iname = `${MIRKeyGenerator.generateTypeKey(containingDecl, binds)}::${cdecl.name}@@cons`;

            this.processGenerateSpecialExpFunction(fkey, iname, new Map<string, ResolvedType>(), cdecl.value as Expression, cdecl.declaredType, cdecl.srcFile, cdecl.sourceLocation);

            const pragmas = this.processPragmas(cdecl.sourceLocation, cdecl.pragmas);
            const enclosingType = MIRKeyGenerator.generateTypeKey(containingDecl, binds);
            const ddecltype = this.resolveAndEnsureTypeOnly(cdecl.sourceLocation, cdecl.declaredType, binds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const mirconst = new MIRConstantDecl(enclosingType, `${enclosingType}::${cdecl.name}`, ckey, pragmas, cdecl.sourceLocation, cdecl.srcFile, dtype.trkey, fkey);

            this.m_emitter.masm.constantDecls.set(ckey, mirconst);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    private processInvokeInfo_Simplified(enclosingDecl: MIRNominalTypeKey | undefined, iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, srcFile: string,
        attributes: string[], params: MIRFunctionParameter[], resolvedResult: ResolvedType,  cargs: Map<string, VarInfo>, argTypes: Map<string, MIRType>, 
        bbody: BodyImplementation, bodybinds: Map<string, ResolvedType>): MIRInvokeDecl {
        
        let resultType = this.m_emitter.registerResolvedTypeReference(resolvedResult);
        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodybinds, [], new Map<string, { pcode: PCode, captured: string[] }>(), cargs, resolvedResult);

        const mirbody = this.checkBody(env, bbody as BodyImplementation, argTypes, resolvedResult, undefined, undefined);
        return new MIRInvokeBodyDecl(enclosingDecl, "[SPECIAL]", iname, ikey, attributes, false, [], sinfo, srcFile, params, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    private processInvokeInfo(fname: string, enclosingDecl: [MIRNominalTypeKey, OOPTypeDecl, Map<string, ResolvedType>] | undefined, kind: "namespace" | "static" | "member", iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkInvokeDecl(sinfo, invoke, binds, pcodes);

        let terms = new Map<string, MIRType>();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && pcodes.some((pc) => pc.code.recursive === "yes"));
        const pragmas = this.processPragmas(invoke.sourceLocation, invoke.pragmas);

        let cargs = new Map<string, VarInfo>();
        let fargs = new Map<string, { pcode: PCode, captured: string[] }>();
        let argTypes: Map<string, MIRType> = new Map<string, MIRType>();
        let refNames: string[] = [];
        let params: MIRFunctionParameter[] = [];

        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedFunctionType) {
                const pcarg = { pcode: pcodes[fargs.size], captured: [...pcodes[fargs.size].captured].map((cc) => cc[0]).sort() };
                fargs.set(p.name, pcarg);
            }
            else {
                const ptype = p.isOptional ? this.m_assembly.typeUpperBound([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                cargs.set(p.name, new VarInfo(ptype, !p.isRef, false, true, ptype));

                if (p.isRef) {
                    refNames.push(p.name);
                }

                const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
                argTypes.set(p.name, mtype);
                params.push(new MIRFunctionParameter(p.name, mtype.trkey));
            }
        });

        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            argTypes.set(invoke.optRestName as string, resttype);
            params.push(new MIRFunctionParameter(invoke.optRestName as string, resttype.trkey));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        const declaredResult = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, binds);
        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invoke.params, binds);

        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, refNames, fargs, cargs, declaredResult);

        //
        //TODO: we are skipping the case of Lambda bindings in the precondition
        //      need to support this later
        //
        const prepostargs = invoke.params
            .filter((param) => !(param.type instanceof FunctionTypeSignature))
            .map((param) => new MIRVariable(param.name));
        
        let preject: [MIRInvokeKey, MIRArgument[]] | undefined = undefined;
        let postject: [MIRInvokeKey, MIRArgument[]] | undefined = undefined;
        let realbody = invoke.body;
        if(kind === "namespace") {
            this.raiseErrorIf(sinfo, invoke.preconditions.some((pre) => pre.isvalidate) && !invoke.preconditions.some((pre) => pre.isvalidate), "Cannot mix terminal and validate preconditions");
            this.raiseErrorIf(sinfo, invoke.preconditions.some((pre) => pre.isvalidate) && !invoke.attributes.includes("entrypoint"), "Cannot use validate preconditions on non-entrypoint functions");

            let preconds = invoke.preconditions.filter((pre) => isBuildLevelEnabled(pre.level, this.m_buildLevel));
            if(preconds.length !== 0) {
                if (preconds.every((pre) => pre.isvalidate)) {
                    realbody = this.processGenerateSpecialPreFunction_ResultT(sinfo, preconds, invoke.body as BodyImplementation);
                }
                else {
                    const fkey = `${ikey}@@pre`;
                    this.processGenerateSpecialPreFunction_FailFast(fkey, `${iname}@@pre`, invoke.params, binds, preconds, binds, invoke.srcFile, invoke.sourceLocation);

                    preject = [fkey, prepostargs];
                }
            }

            let postconds = invoke.postconditions.filter((post) => isBuildLevelEnabled(post.level, this.m_buildLevel));
            if(postconds.length !== 0) {
                const fkey = `${ikey}@@post`;
                const retv = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, binds);
                this.processGenerateSpecialPostFunction(fkey, `${iname}@@post`, [...invoke.params], retv, binds, postconds, binds, invoke.srcFile, invoke.sourceLocation);

                postject = [fkey, prepostargs];
            }
        }
        else {
            const ootype = (enclosingDecl as [MIRNominalTypeKey, OOPTypeDecl, Map<string, ResolvedType>])[1];
            const oobinds = (enclosingDecl as [MIRNominalTypeKey, OOPTypeDecl, Map<string, ResolvedType>])[2];
            const absconds = this.m_assembly.getAbstractPrePostConds(fname as string, ootype, oobinds, binds);

            this.raiseErrorIf(sinfo, invoke.preconditions.some((pre) => pre.isvalidate) || (absconds !== undefined && absconds.pre[0].some((pre) => pre.isvalidate)), "Cannot use validate preconditions on non-entrypoint functions");

            let preconds = (absconds !== undefined ? absconds.pre[0] : invoke.preconditions).filter((pre) => isBuildLevelEnabled(pre.level, this.m_buildLevel));
            if(preconds.length !== 0) {
                const prebinds = absconds !== undefined ? absconds.pre[1] : binds;
                const fkey = `${ikey}@@pre`;
                this.processGenerateSpecialPreFunction_FailFast(fkey, `${iname}@@pre`, invoke.params, binds, preconds, prebinds, invoke.srcFile, invoke.sourceLocation);

                preject = [fkey, prepostargs];
            }

            let postconds = (absconds !== undefined ? absconds.post[0] : invoke.postconditions).filter((post) => isBuildLevelEnabled(post.level, this.m_buildLevel));
            if(postconds.length !== 0) {
                const postbinds = absconds !== undefined ? absconds.post[1] : binds;
                const fkey = `${ikey}@@post`;
                const retv = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, binds);
                this.processGenerateSpecialPostFunction(fkey, `${iname}@@post`, [...invoke.params], retv, binds, postconds, postbinds, invoke.srcFile, invoke.sourceLocation);

                postject = [fkey, prepostargs];
            }
        }

        const encdecl = enclosingDecl !== undefined ? enclosingDecl[0] : undefined;
        if (typeof ((invoke.body as BodyImplementation).body) === "string") {
            let mpc = new Map<string, MIRPCode>();
            fargs.forEach((v, k) => mpc.set(k, { code: MIRKeyGenerator.generatePCodeKey(v.pcode.code), cargs: [...v.captured].map((cname) => this.m_emitter.bodyEmitter.generateCapturedVarName(cname)) }));

            let mbinds = new Map<string, MIRResolvedTypeKey>();
            binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).trkey));

            return new MIRInvokePrimitiveDecl(encdecl, fname, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, mbinds, params, resultType.trkey, (invoke.body as BodyImplementation).body as string, mpc);
        }
        else {
            const mirbody = this.checkBody(env, realbody as BodyImplementation, argTypes, declaredResult, preject, postject);
            return new MIRInvokeBodyDecl(encdecl, fname, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, params, resultType.trkey, preject !== undefined ? preject[0] : undefined, postject !== undefined ? postject[0] : undefined, mirbody as MIRBody);
        }
    }

    private processPCodeInfo(iname: string, ikey: MIRInvokeKey, sinfo: SourceInfo, pci: InvokeDecl, binds: Map<string, ResolvedType>, fsig: ResolvedFunctionType, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkPCodeDecl(sinfo, fsig, pci.recursive);

        const pragmas = this.processPragmas(pci.sourceLocation, pci.pragmas);

        let cargs = new Map<string, VarInfo>();
        let argTypes: Map<string, MIRType> = new Map<string, MIRType>();
        let refNames: string[] = [];
        let params: MIRFunctionParameter[] = [];

        for (let i = 0; i < pci.params.length; ++i) {
            const p = fsig.params[i];
            const ptype = p.isOptional ? this.m_assembly.typeUpperBound([p.type as ResolvedType, this.m_assembly.getSpecialNoneType()]) : p.type as ResolvedType;
            cargs.set(pci.params[i].name, new VarInfo(ptype, !p.isRef, false, true, ptype));

            if (p.isRef) {
                refNames.push(p.name);
            }

            const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
            argTypes.set(pci.params[i].name, mtype);
            params.push(new MIRFunctionParameter(pci.params[i].name, mtype.trkey));
        }

        if (fsig.optRestParamType !== undefined) {
            cargs.set(pci.optRestName as string, new VarInfo(fsig.optRestParamType, true, false, true, fsig.optRestParamType));

            const resttype = this.m_emitter.registerResolvedTypeReference(fsig.optRestParamType);
            argTypes.set(pci.optRestName as string, resttype);
            params.push(new MIRFunctionParameter(pci.optRestName as string, resttype.trkey));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }

        let resolvedResult = fsig.resultType;
        const resultType = this.generateExpandedReturnSig(sinfo, resolvedResult, fsig.params, binds);

        const env = TypeEnvironment.createInitialEnvForCall(ikey, binds, refNames, new Map<string, { pcode: PCode, captured: string[] }>(), cargs, fsig.resultType);
        const mirbody = this.checkBody(env, pci.body as BodyImplementation, argTypes, resolvedResult, undefined, undefined);
        return new MIRInvokeBodyDecl(undefined, "[PCODE]", iname, ikey, pci.attributes, pci.recursive === "yes", pragmas, sinfo, pci.srcFile, params, resultType.trkey, undefined, undefined, mirbody as MIRBody);
    }

    processNamespaceFunction(fkey: MIRInvokeKey, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = f.srcFile;
            const iname = `${f.ns}::${f.name}`;
            const invinfo = this.processInvokeInfo(f.name, undefined, "namespace", iname, fkey, f.sourceLocation, f.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(fkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
            }

            if (f.attributes.includes("entrypoint")) {
                this.m_emitter.masm.entryPoints.push(invinfo.key);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processLambdaFunction(lkey: MIRInvokeKey, invoke: InvokeDecl, sigt: ResolvedFunctionType, binds: Map<string, ResolvedType>, cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const iname = `fn::${invoke.sourceLocation.line}##${invoke.sourceLocation.pos}`;
            const invinfo = this.processPCodeInfo(iname, lkey, invoke.sourceLocation, invoke, binds, sigt, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(lkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(lkey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processStaticFunction(skey: MIRInvokeKey, ctype: OOPTypeDecl, cbinds: Map<string, ResolvedType>, sfdecl: StaticFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = sfdecl.srcFile;
            const enclosingdecl = [MIRKeyGenerator.generateTypeKey(ctype, cbinds), ctype, cbinds] as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
            const iname = `${ctype.ns}::${ctype.name}::${sfdecl.name}`;
            const invinfo = this.processInvokeInfo(sfdecl.name, enclosingdecl, "static", iname, skey, sfdecl.sourceLocation, sfdecl.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(skey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(skey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processMethodFunction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, ctype: OOPTypeDecl, cbinds: Map<string, ResolvedType>, mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        if (this.m_emitter.masm.primitiveInvokeDecls.has(mkey) || this.m_emitter.masm.invokeDecls.has(mkey)) {
            return;
        }

        try {
            this.m_file = mdecl.srcFile;
            const enclosingdecl = [MIRKeyGenerator.generateTypeKey(ctype, cbinds), ctype, cbinds] as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
            const iname = `${ctype.ns}::${ctype.name}->${mdecl.name}`;
            const invinfo = this.processInvokeInfo(mdecl.name, enclosingdecl, "member", iname, mkey, mdecl.sourceLocation, mdecl.invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(mkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);
            }

            const tkey = MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            if (ctype instanceof EntityTypeDecl) {
                (this.m_emitter.masm.entityDecls.get(tkey) as MIROOTypeDecl).vcallMap.set(vkey, mkey);
            }
            else {
                (this.m_emitter.masm.conceptDecls.get(tkey) as MIROOTypeDecl).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }

    processRegexInfo() {
        //TODO: check regexs here and convert to MIRRegex IR too!!!

        this.m_assembly.getAllLiteralRegexs().forEach((lre) => {
            this.m_emitter.masm.literalRegexs.set(lre, new MIRRegex(lre));
        })

        this.m_assembly.getAllValidators().forEach((vre) => {
            const vkey = MIRKeyGenerator.generateTypeKey(vre[0].object, vre[0].binds);
            this.m_emitter.masm.validatorRegexs.set(vkey, vre[1]);
        });
    }

    runFinalExhaustiveChecks() {
        this.m_exhaustiveChecks.forEach((ec) => {
            try {
                //TODO: we need to do this!!!!
            }
            catch (ex) {
                this.m_emitEnabled = false;
                this.abortIfTooManyErrors();
            }
        });
    }
}

export { TypeError, TypeChecker };
