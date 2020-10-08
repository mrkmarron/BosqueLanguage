//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedFunctionTypeParam, ResolvedEphemeralListType, ResolvedConceptAtomTypeEntry, ResolvedLiteralAtomType } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, BuildLevel, isBuildLevelEnabled, PreConditionDecl, PostConditionDecl, TypeConditionRestriction, ConceptTypeDecl, SpecialTypeCategory, TemplateTermSpecialRestriction, NamespaceOperatorDecl, StaticOperatorDecl, NamespaceDeclaration } from "../ast/assembly";
import { TypeEnvironment, VarInfo, FlowTypeTruthValue, StructuredAssignmentPathStep, StructuredAssignmentCheck } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature, FunctionParameter, FunctionTypeSignature, TupleTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixModifyWithIndecies, PostfixModifyWithNames, PrefixNotOp, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ConstructorEphemeralValueList, VariablePackDeclarationStatement, VariablePackAssignmentStatement, NominalStructuredAssignment, ValueListStructuredAssignment, NakedCallStatement, ValidateStatement, IfElse, CondBranchEntry, MapEntryConstructorExpression, SpecialConstructorExpression, PragmaArguments, PostfixIs, PostfixHasIndex, PostfixHasProperty, PostfixAs, BinEqExpression, BinCmpExpression, LiteralParamerterValueExpression, LiteralTypedNumericConstructorExpression, OfTypeConvertExpression, LiteralIntegralExpression, LiteralRationalExpression, LiteralFloatPointExpression, LiteralExpressionValue, PostfixGetIndexOrNone, PostfixGetIndexTry, PostfixGetPropertyOrNone, PostfixGetPropertyTry, ConstantExpressionValue } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator } from "../compiler/mir_emitter";
import { MIRTempRegister, MIRArgument, MIRConstantNone, MIRBody, MIRVirtualMethodKey, MIRConstantKey, MIRInvokeKey, MIRResolvedTypeKey, MIRFieldKey, MIRConstantString, MIRParameterVariable, MIRVariableArgument, MIRLocalVariable, MIRRegisterArgument, MIRConstantInt, MIRConstantNat, MIRConstantBigNat, MIRConstantBigInt, MIRConstantRational, MIRConstantDecmial, MIRConstantFloat } from "../compiler/mir_ops";
import { SourceInfo, unescapeLiteralString } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIROOTypeDecl, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIRRegex, MIREphemeralListType } from "../compiler/mir_assembly";
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
    ref: ["ref" | "out" | "out?", MIRVariableArgument] | undefined,
    pcode: PCode | undefined,
    treg: MIRTempRegister | undefined
};

type FilledLocation = {
    vtype: ResolvedType | ResolvedFunctionType,
    mustDef: boolean,
    fflagchk: boolean,
    ref: ["ref" | "out" | "out?", MIRVariableArgument] | undefined,
    pcode: PCode | undefined,
    trgt: MIRArgument | undefined
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

function createTerminalEqCheck(srctype: ResolvedType, exp: ConstantExpressionValue): StructuredAssignmentCheck {
    return { action: "eqchk", srctype: srctype, oftype: undefined, isoptional: false, eqvalue: exp };
}

function createOfTypeCheck(srctype: ResolvedType, oftype: ResolvedType, isoptional: boolean): StructuredAssignmentCheck {
    return { action: "typechk", srctype: srctype, oftype: oftype, isoptional: isoptional, eqvalue: undefined };
}

class TypeChecker {
    private readonly m_assembly: Assembly;

    private readonly m_buildLevel: BuildLevel;
    private readonly m_doLiteralStringValidate: boolean;

    private m_file: string;
    private m_errors: [string, number, string][];

    private readonly m_emitter: MIREmitter;

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

    private doConstantExpressionTypeInferNoEmit(env: TypeEnvironment, srcFile: string, cexp: ConstantExpressionValue, args: Map<string, VarInfo>): ResolvedType {
        const oldenable = this.m_emitter.getEmitEnabled();
        this.m_emitter.setEmitEnabled(false);

        const ccall = `ConstExprEval@@${srcFile}#${cexp.exp.sinfo.pos}`;
        const cenv = TypeEnvironment.createInitialEnvForCall(ccall, new Map<string, ResolvedType>(env.terms), [], new Map<string, { pcode: PCode, captured: string[] }>(), args, undefined);

        const junkreg = this.m_emitter.generateTmpRegister();
        const etype = this.checkExpression(cenv, cexp.exp, junkreg, undefined).getExpressionResult().exptype;

        this.m_emitter.setEmitEnabled(oldenable);

        return etype;
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

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): { chk: "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "stringof" | "datastring" | "keytuple"  | "keyrecord" | "operator", lnotnonechk: boolean, rnotnonechk: boolean } {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return { chk: "truealways", lnotnonechk: false, rnotnonechk: false };
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return { chk: rhs.options.some((opt) => opt.idStr === "NSCore::None") ? "lhsnone" : "falsealways", lnotnonechk: false, rnotnonechk: false };
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return { chk: lhs.options.some((opt) => opt.idStr === "NSCore::None") ? "rhsnone" : "falsealways", lnotnonechk: false, rnotnonechk: false };
        }
        
        const lhsnone = lhs.options.some((opt) => opt.idStr == "NSCore::None");
        const simplelhsopts = lhs.options.filter((opt) => opt.idStr == "NSCore::None");

        const rhsnone = rhs.options.some((opt) => opt.idStr == "NSCore::None");
        const simplerhsopts = rhs.options.filter((opt) => opt.idStr == "NSCore::None");

        const lnotnonechk = lhsnone && !rhsnone;
        const simplelhs = simplelhsopts.length !== 0 && lnotnonechk ? ResolvedType.create(simplelhsopts) : lhs;

        const rnotnonechk = !lhsnone && rhsnone;
        const simplerhs = simplerhsopts.length !== 0 && rnotnonechk ? ResolvedType.create(simplerhsopts) : rhs;

        if((simplelhs.isUniqueCallTargetType() && simplelhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl)) 
            && (simplerhs.isUniqueCallTargetType() && simplerhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl))) {
            return { chk: !simplelhs.isSameType(simplerhs) ? "falsealways" : "stringof", lnotnonechk: lnotnonechk, rnotnonechk: rnotnonechk };
        }

        if((simplelhs.isUniqueCallTargetType() && simplelhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl)) 
            && (simplerhs.isUniqueCallTargetType() && simplerhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl))) {
            return { chk: !simplelhs.isSameType(simplerhs) ? "falsealways" : "datastring", lnotnonechk: lnotnonechk, rnotnonechk: rnotnonechk };
        }

        if ((simplelhs.isUniqueTupleTargetType() && this.m_assembly.subtypeOf(simplelhs, this.m_assembly.getSpecialKeyTypeConceptType())) 
            && (simplerhs.isUniqueTupleTargetType() && this.m_assembly.subtypeOf(simplerhs, this.m_assembly.getSpecialKeyTypeConceptType()))) {
            return { chk: !simplelhs.isSameType(simplerhs) ? "falsealways" : "keytuple", lnotnonechk: lnotnonechk, rnotnonechk: rnotnonechk };
        }

        if ((simplelhs.isUniqueRecordTargetType() && this.m_assembly.subtypeOf(simplelhs, this.m_assembly.getSpecialKeyTypeConceptType())) 
            && (simplerhs.isUniqueRecordTargetType() && this.m_assembly.subtypeOf(simplerhs, this.m_assembly.getSpecialKeyTypeConceptType()))) {
            return { chk: !simplelhs.isSameType(simplerhs) ? "falsealways" : "keyrecord", lnotnonechk: lnotnonechk, rnotnonechk: rnotnonechk };
        }
        
        return { chk: "operator", lnotnonechk: lnotnonechk, rnotnonechk: rnotnonechk };
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
        
        //We need to ensure in operator checking that users do not override operations for core types
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
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => (atom as ResolvedTupleAtomType).types[idx].type));
    }

    private getInfoForLoadFromSafeIndexOnly(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedTupleAtomType).types.length > idx)
            .map((atom) => (atom as ResolvedTupleAtomType).types[idx].type)
        );
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
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) as ResolvedRecordAtomTypeEntry).type));
    }

    private getInfoForLoadFromSafePropertyOnly(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) !== undefined)
            .map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.name === pname) as ResolvedRecordAtomTypeEntry).type)
        );
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
        let reqNames = new Set<string>();
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                allNames.add(re.name);

                if (re.isOptional) {
                    reqNames.add(re.name);
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
            cargs.set(exp.invoke.params[i].name, new VarInfo(p.type as ResolvedType, p.refKind === undefined, false, true, p.type as ResolvedType, FlowTypeTruthValue.Unknown));

            if (p.refKind !== undefined) {
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
                eargs.push({ name: "this", argtype: earg.declaredType, ref: ["ref", new MIRParameterVariable(rvname)], expando: false, pcode: undefined, treg: optSelfValue[2] });
            }
        }

        const ridx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof PositionalArgument) || !arg.isSpread);
        
        this.raiseErrorIf(sinfo, !refallowed && ((optSelfValue !== undefined && optSelfValue[1] !== undefined) || args.argList.some((arg) => arg.ref !== undefined)), "Cannot use ref params in this call position");

        //
        //TODO: we only end up doing type inference for calls that are simple (no expandos)
        //      we may want to fix this by augmenting our template type inference to do more!!!
        //

        if (noExpando) {
            let fillednames = new Set<string>();

            for (let i = 0; i < args.argList.length; ++i) {
                const isref = args.argList[i].ref !== undefined;
                this.raiseErrorIf(args.argList[i].value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");

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
                    this.raiseErrorIf(narg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, narg.value, sigbinds, param.type as ResolvedFunctionType);
                    eargs[i] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (narg.value instanceof AccessVariableExpression && env.pcodes.has(narg.value.name)) {
                    this.raiseErrorIf(narg.value.sinfo, !(param.type instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(narg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(narg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i] = { name: narg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (isref) {
                        this.raiseErrorIf(narg.value.sinfo, !(narg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (narg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(narg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        let refreg: MIRTempRegister | undefined = undefined;
                        if(narg.ref === "ref") {
                            this.checkExpression(env, narg.value, treg, param.type as ResolvedType);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        eargs[i] = { name: narg.name, argtype: earg.declaredType, ref: [narg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg };
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
                const isref = parg.ref !== undefined;

                while(sigidx < sig.params.length && fillednames.has(sig.params[sigidx].name)) {
                    sigidx++;
                }

                const oftypett = (sigidx < sig.params.length) ? sig.params[sigidx].type : sig.optRestParamType;
                this.raiseErrorIf(sinfo, oftypett === undefined, "Too many parameters for call");
                const oftype = oftypett as ResolvedFunctionType | ResolvedType;

                const treg = this.m_emitter.generateTmpRegister();
                if (parg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = this.checkPCodeExpression(env, parg.value, sigbinds, oftype as ResolvedFunctionType);
                    eargs[i] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else if (parg.value instanceof AccessVariableExpression && env.pcodes.has(parg.value.name)) {
                    this.raiseErrorIf(parg.value.sinfo, !(oftype instanceof ResolvedFunctionType), "Must have function type for function arg");
                    this.raiseErrorIf(parg.value.sinfo, isref, "Cannot use ref params on function argument");

                    const pcode = (env.pcodes.get(parg.value.name) as { pcode: PCode, captured: string[] }).pcode;
                    eargs[i] = { name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg };
                }
                else {
                    if (isref) {
                        this.raiseErrorIf(parg.value.sinfo, !(parg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (parg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(parg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, parg.value, treg, oftype as ResolvedType);

                        let refreg: MIRTempRegister | undefined = undefined;
                        if(parg.ref === "ref") {
                            this.checkExpression(env, parg.value, treg, oftype as ResolvedType);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        eargs[i] = { name: undefined, argtype: earg.declaredType, ref: [parg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg };
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
                const isref = arg.ref !== undefined;

                const treg = this.m_emitter.generateTmpRegister();

                this.raiseErrorIf(arg.value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");
                this.raiseErrorIf(arg.value.sinfo, isref && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

                if (arg.value instanceof ConstructorPCodeExpression) {
                    this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

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
                    this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

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
                    if (isref) {
                        this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                        const rvname = (arg.value as AccessVariableExpression).name;
                        this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                        this.checkExpression(env, arg.value, treg, undefined);

                        let refreg: MIRTempRegister | undefined = undefined;
                        if(arg.ref === "ref") {
                            this.checkExpression(env, arg.value, treg, undefined);
                            refreg = treg;
                        }

                        const earg = (env.lookupVar(rvname) as VarInfo);
                        const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                        if (arg instanceof NamedArgument) {
                            eargs.push({ name: arg.name, argtype: earg.declaredType, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                        }
                        else {
                            eargs.push({ name: undefined, argtype: earg.declaredType, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
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

        this.m_emitter.setEmitEnabled(oldenable);

        this.checkTemplateTypes(sinfo, invk.terms, rrbinds);

        const fsig = this.m_assembly.normalizeTypeFunction(invk.generateSig(), rrbinds);
        this.raiseErrorIf(sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(sinfo, env, fsig as ResolvedFunctionType, rrbinds, args, optSelfValue, refallowed);

        return [fsig as ResolvedFunctionType, rrbinds, eargs];
    }

    private checkArgumentsEvaluationWOperator(sinfo: SourceInfo, env: TypeEnvironment, binds: Map<string, ResolvedType>, args: Arguments, refallowed: boolean): ExpandedArgument[] {
        let eargs: ExpandedArgument[] = [];
        
        this.raiseErrorIf(sinfo, !refallowed && args.argList.some((arg) => arg.ref !== undefined), "Cannot use ref params in this call position");

        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const isref = arg.ref !== undefined;

            const treg = this.m_emitter.generateTmpRegister();

            this.raiseErrorIf(arg.value.sinfo, isref && !refallowed, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, isref && arg instanceof PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");

            if (arg.value instanceof ConstructorPCodeExpression) {
                this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

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
                this.raiseErrorIf(arg.value.sinfo, isref, "Cannot use ref params on function argument");

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
                if (isref) {
                    this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof AccessVariableExpression), "Can only ref on variable names");

                    const rvname = (arg.value as AccessVariableExpression).name;
                    this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");

                    let refreg: MIRTempRegister | undefined = undefined;
                    if(arg.ref === "ref") {
                        this.checkExpression(env, arg.value, treg, undefined);
                        refreg = treg;
                    }

                    const earg = (env.lookupVar(rvname) as VarInfo);
                    const refv = env.getLocalVarInfo(rvname) !== undefined ? new MIRLocalVariable(rvname) : new MIRParameterVariable(rvname);

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg.declaredType, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg.declaredType, ref: [arg.ref as "ref" | "out" | "out?", refv], expando: false, pcode: undefined, treg: refreg });
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
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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
            this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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
                this.raiseErrorIf(args.argList[i].value.sinfo, args.argList[i].ref !== undefined, "Cannot use ref params in this call position");

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
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");

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

                filledLocations[fidx] = { vtype: arg.argtype as ResolvedType, mustDef: true, fflagchk: false, trgt: arg.treg as MIRTempRegister };
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
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[fidx][1];
                        this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[fidx]}" is required and must be assigned a value in constructor`);
                        
                        this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), arg.treg as MIRTempRegister);
                        this.m_emitter.emitCheckedLoadProperty(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
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
                filledLocations[ii] = { vtype: arg.argtype as ResolvedType, mustDef: true, fflagchk: false, trgt: arg.treg as MIRTempRegister };
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
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: lvtype, mustDef: true, fflagchk: false, trgt: etreg };
                    }
                    else {
                        const field = flatfinfo[ii][1];
                        this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[ii]}" is required and must be assigned a value in constructor`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), arg.treg as MIRTempRegister);
                        this.m_emitter.emitCheckedLoadTupleIndex(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
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

            if (filledLocations[i] === undefined) {
                this.raiseErrorIf(sinfo, field[1].value === undefined, `Field ${field[1].name} is required and must be assigned a value in constructor`);

                const emptyreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(fieldtype), emptyreg);
                this.m_emitter.emitSetHasFlagConstant(fflag, i - optfirst, false);
                filledLocations[i] = { vtype: fieldtype, mustDef: false, fflagchk: true, trgt: emptyreg };
            }

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

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, name: string, sig: ResolvedFunctionType, args: ExpandedArgument[]): { args: MIRArgument[], fflag: string, refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
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
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                        filledLocations[fidx] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[fidx];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), arg.treg as MIRTempRegister);
                        this.m_emitter.emitCheckedLoadProperty(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
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
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                        filledLocations[ii] = { vtype: lvtype, mustDef: true, fflagchk: false, ref: undefined, pcode: undefined, trgt: etreg };
                    }
                    else {
                        const param = sig.params[ii];
                        this.raiseErrorIf(sinfo, !param.isOptional, `Parameter "${param.name}" is required and must be assigned a value in call`);

                        this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), arg.treg as MIRTempRegister);
                        this.m_emitter.emitCheckedLoadTupleIndex(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
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
        let pcodes: PCode[] = [];
        let refs: MIRVariableArgument[] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;

            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                const emptyreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(paramtype as ResolvedType), emptyreg);
                this.m_emitter.emitSetHasFlagConstant(fflag, j - optfirst, false);
                filledLocations[j] = { vtype: paramtype, mustDef: false, fflagchk: true, ref: undefined, pcode: undefined, trgt: emptyreg };
            }

            if (sig.params[j].type instanceof ResolvedFunctionType) {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode === undefined, `Parameter ${sig.params[j].name} expected a function`);
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype as ResolvedFunctionType, paramtype as ResolvedFunctionType), `Parameter ${sig.params[j].name} expected function of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                pcodes.push(filledLocations[j].pcode as PCode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);

                if (sig.params[j].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, !(filledLocations[j].vtype as ResolvedType).isSameType(paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);

                    refs.push((filledLocations[j].ref as ["ref" | "out" | "out?", MIRVariableArgument])[1]);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype as ResolvedType, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                }


                if (sig.params[j].refKind === undefined || sig.params[j].refKind === "ref") {
                    let narg = filledLocations[j].trgt as MIRArgument;
                    if (filledLocations[j].fflagchk) {
                        narg = this.emitCheckedInlineConvertIfNeeded(sinfo, narg, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType, fflag, j - optfirst);
                    }
                    else {
                        narg = this.emitInlineConvertIfNeeded(sinfo, narg, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType);
                    }

                    margs.push(narg);
                }
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

                    cinfo.push([cnames[i], tinfo.flowType]);
                }
                else {
                    if(env.getLocalVarInfo(cnames[i]) !== undefined) {
                        margs.push(new MIRLocalVariable(cnames[i]));
                    }
                    else {
                        margs.push(new MIRParameterVariable(vinfo.isCaptured ? this.m_emitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                    }

                    cinfo.push([cnames[i], vinfo.flowType]);
                }
            }
        }

        return { args: margs, fflag: fflag, refs: refs, pcodes: pcodes, cinfo: cinfo };
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

                    this.m_emitter.emitLoadProperty(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
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
                   
                    this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg as MIRTempRegister, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
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
                    this.raiseErrorIf(sinfo, (filledLocations[j].ref as ["ref" | "out" | "out?", MIRVariableArgument])[0] !== "ref" , "'out' and 'out?' refs are not supported on operators (yet)");

                    refs.push((filledLocations[j].ref as ["ref" | "out" | "out?", MIRVariableArgument])[1]);
                }

                margs.push(filledLocations[j].trgt as MIRArgument);
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
        const rr = params.filter((fp) => fp.refKind !== undefined).map((fp) => this.resolveAndEnsureTypeOnly(sinfo, fp.type, binds));
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

    private checkLiteralIntegralExpression(env: TypeEnvironment, exp: LiteralIntegralExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const itype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.itype, env.terms);
        const [restype, iipack] = this.genInferInfo(exp.sinfo, itype, infertype, trgt);

        this.m_emitter.emitLoadConstIntegralValue(exp.sinfo, this.m_emitter.registerResolvedTypeReference(itype), exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialIntType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralRationalExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialRationalType(), infertype, trgt);

        this.m_emitter.emitLoadConstRational(exp.sinfo, exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialRationalType(), infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkLiteralFloatExpression(env: TypeEnvironment, exp: LiteralFloatPointExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const fptype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.fptype, env.terms);
        const [restype, iipack] = this.genInferInfo(exp.sinfo, fptype, infertype, trgt);

        this.m_emitter.emitLoadConstFloatPoint(exp.sinfo, this.m_emitter.registerResolvedTypeReference(fptype), exp.value, iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialFloatType(), infertype, iipack);
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

    private checkLiteralParameterValeExpression(env: TypeEnvironment, exp: LiteralParamerterValueExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const vv = (env.terms.get(exp.ltype.name) as ResolvedType).options[0] as ResolvedLiteralAtomType;
        return [this.checkExpression(env, vv.vexp, trgt, infertype)];
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
                this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, tmpokt);
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
        this.m_emitter.emitCheckNoError(exp.sinfo, tmps, presult, tmpokt);
        this.m_emitter.emitAssertCheck(exp.sinfo, "String not parsable as given type", tmpokt);

        const convt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitConvertDown(exp.sinfo, presult, rok, tmps, convt);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, aoftype.stringtype, infertype, trgt);
        this.m_emitter.emitExtractResult(exp.sinfo, convt, rok, iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, this.getResultBinds(aoftype.parsetype).T, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkTypedTypedNumericConstructor(env: TypeEnvironment, exp: LiteralTypedNumericConstructorExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const tntt = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.vtype, env.terms);
        const oftype = (tntt.options[0] as ResolvedEntityAtomType).object;
        const ofbinds = (tntt.options[0] as ResolvedEntityAtomType).binds;

        const consf = oftype.staticFunctions.get("create");
        this.raiseErrorIf(exp.sinfo, consf === undefined, "Missing static function 'create'");

        let nval: MIRArgument = new MIRConstantNone();
        const ntype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ntype, new Map<string, ResolvedType>());
        if(ntype.isSameType(this.m_assembly.getSpecialIntType())) {
            nval = new MIRConstantInt(exp.value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialNatType())) {
            nval = new MIRConstantNat(exp.value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialBigIntType())) {
            nval = new MIRConstantBigInt(exp.value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialBigNatType())) {
            nval = new MIRConstantBigNat(exp.value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialRationalType())) {
            nval = new MIRConstantRational(exp.value);
        }
        else if(ntype.isSameType(this.m_assembly.getSpecialFloatType())) {
            nval = new MIRConstantFloat(exp.value);
        }
        else {
            nval = new MIRConstantDecmial(exp.value);
        }

        if(oftype.invariants.length !== 0) {
            const fkey = MIRKeyGenerator.generateFunctionKey(`${oftype.ns}::${oftype.name}`, "@@invariant", ofbinds, []);
        
            const tmps = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, fkey, [nval], undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), tmps);
            this.m_emitter.emitAssertCheck(exp.sinfo, "Number does not satisfy requirements for type", tmps);    
        }

        const [restype, iipack] = this.genInferInfo(exp.sinfo, tntt, infertype, trgt);

        const skey = this.m_emitter.registerStaticCall(oftype, ofbinds, consf as StaticFunctionDecl, "create", new Map<string, ResolvedType>(), [], []);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [nval], undefined, this.m_emitter.registerResolvedTypeReference(tntt), iipack[0]);

        this.emitConvertIfNeeded(exp.sinfo, tntt, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessNamespaceConstant(env: TypeEnvironment, exp: AccessNamespaceConstantExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        this.raiseErrorIf(exp.sinfo, cdecl.value.captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.m_assembly.compileTimeReduceConstantExpression(cdecl.value.exp, env.terms);
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map<string, ResolvedType>());

        if (cexp !== undefined) {
            return [this.checkExpression(env, cexp, trgt, infertype)];
        }
        else {
            const gkey = this.m_emitter.registerPendingGlobalProcessing(cdecl);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, rtype, infertype, trgt);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, gkey, [], undefined, this.m_emitter.registerResolvedTypeReference(rtype), iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, rtype, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkAccessStaticField(env: TypeEnvironment, exp: AccessStaticFieldExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);

        const cdecltry = this.m_assembly.tryGetConstMemberUniqueDeclFromType(oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined (or not uniquely defined) for type '${oftype.idStr}'`);

        const cdecl = cdecltry as OOMemberLookupInfo<StaticMemberDecl>;
        
        this.raiseErrorIf(exp.sinfo, (cdecl.decl.value as ConstantExpressionValue).captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.m_assembly.compileTimeReduceConstantExpression((cdecl.decl.value as ConstantExpressionValue).exp, env.terms);
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.decl.declaredType, cdecl.binds);
        
        if (cexp !== undefined) {
            return [this.checkExpression(env, cexp, trgt, infertype)];
        }
        else {
            const rctype = this.resolveOOTypeFromDecls(cdecl.contiainingType, cdecl.binds);
            const skey = this.m_emitter.registerPendingConstProcessing(this.m_emitter.registerResolvedTypeReference(rctype), cdecl.contiainingType, cdecl.decl, cdecl.binds);

            const [restype, iipack] = this.genInferInfo(exp.sinfo, rtype, infertype, trgt);
            this.m_emitter.emitInvokeFixedFunction(exp.sinfo, skey, [], undefined, this.m_emitter.registerResolvedTypeReference(rtype), iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, rtype, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
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
                if(fsig.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !refok, "ref argument not supported in this call position");
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(opdecl.invoke.params[i].litexp !== undefined) {
                    const mirargtype = this.m_emitter.registerResolvedTypeReference(argtypes[argidx]);

                    const lccall = MIRKeyGenerator.generateFunctionKey(opkey, `@@literalkey${i}`, new Map<string, ResolvedType>(), []);
                    const litenv = TypeEnvironment.createInitialEnvForCall(lccall, new Map<string, ResolvedType>(), [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>(), undefined);

                    const oldenable = this.m_emitter.getEmitEnabled();
                    this.m_emitter.setEmitEnabled(false);
                    const junkreg = this.m_emitter.generateTmpRegister();
                    const eetype = this.checkExpression(litenv, (opdecl.invoke.params[i].litexp as LiteralExpressionValue).exp, junkreg, undefined).getExpressionResult().exptype;
                    this.m_emitter.setEmitEnabled(oldenable);

                    const lcreg = this.m_emitter.generateTmpRegister();    
                    this.m_emitter.emitInvokeFixedFunction(sinfo, lccall, [], undefined, this.m_emitter.registerResolvedTypeReference(eetype), lcreg);

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
                if(opdecl.invoke.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(opdecl.invoke.params[i].type as ResolvedType));
                }
            }

            const opkey = this.m_emitter.registerVirtualNamespaceOperatorCall(opdecl.ns, opdecl.name, opdecl, pcodes, cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, refs);
            this.m_emitter.emitInvokeVirtualOperator(sinfo, opkey, cargs, refinfo, iipack[0]);
        }

        this.emitConvertIfNeeded(sinfo, fsig.resultType, infertype, iipack);
        return [env.setResultExpression(restype)];
    }

    private checkStaticOperatorInvoke(sinfo: SourceInfo, env: TypeEnvironment, oodecl: OOPTypeDecl, oobinds: Map<string, ResolvedType>, opdecl: StaticOperatorDecl, args: MIRArgument[], argtypes: ResolvedType[], refs: MIRVariableArgument[], pcodes: PCode[], cinfo: [string, ResolvedType][], pragmas: PragmaArguments, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const fsig = this.m_assembly.normalizeTypeFunction(opdecl.invoke.generateSig(), oobinds) as ResolvedFunctionType;
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
                if(fsig.params[i].refKind !== undefined) {
                    this.raiseErrorIf(sinfo, !refok, "ref argument not supported in this call position");
                    this.raiseErrorIf(sinfo, !argtypes[argidx].isSameType(fsig.params[i].type as ResolvedType));
                }
                cargs.push(this.emitInlineConvertIfNeeded(sinfo, args[argidx], argtypes[argidx], fsig.params[i].type as ResolvedType));

                if(opdecl.invoke.params[i].litexp !== undefined) {
                    const mirargtype = this.m_emitter.registerResolvedTypeReference(argtypes[argidx]);

                    const lccall = MIRKeyGenerator.generateFunctionKey(opkey, `@@literalkey${i}`, new Map<string, ResolvedType>(), []);
                    const litenv = TypeEnvironment.createInitialEnvForCall(lccall, new Map<string, ResolvedType>(oobinds), [], new Map<string, { pcode: PCode, captured: string[] }>(), new Map<string, VarInfo>(), undefined);

                    const oldenable = this.m_emitter.getEmitEnabled();
                    this.m_emitter.setEmitEnabled(false);
                    const junkreg = this.m_emitter.generateTmpRegister();
                    const eetype = this.checkExpression(litenv, (opdecl.invoke.params[i].litexp as LiteralExpressionValue).exp, junkreg, undefined).getExpressionResult().exptype;
                    this.m_emitter.setEmitEnabled(oldenable);

                    const lcreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitInvokeFixedFunction(sinfo, lccall, [], undefined, this.m_emitter.registerResolvedTypeReference(eetype), lcreg);

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
                if(opdecl.invoke.params[i].refKind !== undefined) {
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
            const ktype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.terms.targs[0], env.terms);
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(ktype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.isGroundedType(), "Invalid argument");

            const lhsexp = exp.args.argList[0].value;
            const lhsreg = this.m_emitter.generateTmpRegister();
            const tlhs = this.checkExpression(env, lhsexp, lhsreg, undefined).getExpressionResult().exptype;

            const rhsexp = exp.args.argList[1].value;
            const rhsreg = this.m_emitter.generateTmpRegister();
            const trhs = this.checkExpression(env, rhsexp, rhsreg, undefined).getExpressionResult().exptype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(tlhs, ktype), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(trhs, ktype), "Invalid argument");


            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);
            if(exp.name === "equal") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs), lhsreg, this.m_emitter.registerResolvedTypeReference(tlhs), rhsreg, iipack[0]);
            }
            else {
                this.m_emitter.emitBinKeyLess(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs), lhsreg, this.m_emitter.registerResolvedTypeReference(tlhs), rhsreg, iipack[0]);
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
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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
                this.raiseErrorIf(arg.value.sinfo, arg.ref !== undefined, "Cannot use ref params in this call position");
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

        const cargs = [...exp.args.argList, ...captured.map((cv) => new PositionalArgument(undefined, false, new AccessVariableExpression(exp.sinfo, cv)))];
        const eargs = this.checkArgumentsEvaluationWSig(exp.sinfo, env, pcode.ftype, new Map<string, ResolvedType>(), new Arguments(cargs), undefined, refok);

        //A little strange since we don't expand captured args on the signature yet and don't expand/rest/etc -- slice them off for the checking
        const margs = this.checkArgumentsSignature(exp.sinfo, env, "pcode", pcode.ftype, eargs.slice(0, exp.args.argList.length));
        const cargsext = eargs.slice(exp.args.argList.length).map((ea) => ea.treg as MIRTempRegister);

        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.pragmas.recursive);

        const [restype, iipack] = this.genInferInfo(exp.sinfo, pcode.ftype.resultType, infertype, trgt);

        const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), [...margs.args, ...cargsext], undefined, refinfo, iipack[0]);        
        this.emitConvertIfNeeded(exp.sinfo, pcode.ftype.resultType, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkOfTypeConvertExpression(env: TypeEnvironment, exp: OfTypeConvertExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const treg = this.m_emitter.generateTmpRegister();
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        const fenv = this.checkExpression(env, exp.arg, treg, oftype, { refok: refok, orok: false });

        const tsplits = this.m_assembly.splitTypes(fenv.getExpressionResult().exptype, oftype);
        if(tsplits.tp.isEmptyType()) {
            return [];
        }
        else {
            if (!tsplits.fp.isEmptyType()) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(exp.sinfo, creg, this.m_emitter.registerResolvedTypeReference(oftype), treg, this.m_emitter.registerResolvedTypeReference(fenv.getExpressionResult().exptype));
                this.m_emitter.emitAssertCheck(exp.sinfo, "Failed type conversion", creg);
            }

            const [restype, iipack] = this.genInferInfo(exp.sinfo, oftype, infertype, trgt);

            this.emitAssignToTempAndConvertIfNeeded_KnownSafe(exp.sinfo, fenv.getExpressionResult().exptype, oftype, treg, iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, oftype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
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
                eev = env.addVar(`$${update.index}_#${op.sinfo.pos}`, true, itype, true, itype);

                this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.index}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(itype));
                this.m_emitter.localLifetimeStart(op.sinfo, `$${update.index}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(itype));
            }

            const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().exptype;

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.index}_#${op.sinfo.pos}`);
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
                    eev = env.addVar(`$${update.name}_#${op.sinfo.pos}`, true, itype, true, itype);

                    this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.name}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(itype));
                    this.m_emitter.localLifetimeStart(op.sinfo, `$${update.name}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(itype));
                }

                const utype = this.checkExpression(eev, update.value, etreg, itype).getExpressionResult().exptype;

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}_#${op.sinfo.pos}`);
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
                    eev = env.addVar(`$${update.name}_#${op.sinfo.pos}`, true, ftype, true, ftype);

                    this.m_emitter.emitLocalVarStore(op.sinfo, etreg, `$${update.name}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(ftype));
                    this.m_emitter.localLifetimeStart(op.sinfo, `$${update.name}_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(ftype));
                }

                const utype = this.checkExpression(eev, update.value, etreg, ftype).getExpressionResult().exptype;

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$${update.name}_#${op.sinfo.pos}`);
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
            ...(renvs.tenvs.map((eev) => eev.setResultExpression(restype, FlowTypeTruthValue.True))), 
            ...(renvs.fenvs.map((eev) => eev.setResultExpression(restype, FlowTypeTruthValue.False)))
        ];
    }

    private checkPostfixAs(env: TypeEnvironment, op: PostfixAs, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        const astype = this.resolveAndEnsureTypeOnly(op.sinfo, op.astype, env.terms);

        const tsplits = this.m_assembly.splitTypes(texp, astype);
        if(tsplits.tp.isEmptyType()) {
            return [];
        }
        else {
            if (!tsplits.fp.isEmptyType()) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(op.sinfo, creg, this.m_emitter.registerResolvedTypeReference(astype), arg, this.m_emitter.registerResolvedTypeReference(texp));
                this.m_emitter.emitAssertCheck(op.sinfo, "Failed type conversion", creg);
            }

            const [restype, iipack] = this.genInferInfo(op.sinfo, astype, infertype, trgt);

            this.emitAssignToTempAndConvertIfNeeded_KnownSafe(op.sinfo, texp, astype, arg, iipack[0]);

            this.emitConvertIfNeeded(op.sinfo, astype, infertype, iipack);
            return [env.setResultExpression(restype)];
        }
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
            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const renvs = TypeEnvironment.convertToHasIndexNotHasIndexFlowsOnResult(this.m_assembly, op.idx, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False))),
            ];
        }
    }

    private checkPostfixGetIndexOrNone(env: TypeEnvironment, op: PostfixGetIndexOrNone, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp, op.idx);
        if(hpi === "no") {
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialNoneType(), infertype, trgt);

            this.m_emitter.emitLoadConstNone(op.sinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialNoneType(), infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, op.idx);
            const [restype, iipack] = this.genInferInfo(op.sinfo, linfo, infertype, trgt);

            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, linfo, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else {
            const ttype = this.getInfoForLoadFromSafeIndexOnly(op.sinfo, texp, op.idx);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), ttype]);
            const [restype, iipack] = this.genInferInfo(op.sinfo, linfo, infertype, trgt);

            this.m_emitter.emitTempRegisterAssign(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), this.m_assembly.getSpecialNoneType(), linfo), iipack[0]);
            const hasblock = this.m_emitter.createNewBlock("hasindex");
            const doneblock = this.m_emitter.createNewBlock("donecheckedload");

            const hasreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), hasreg);
            this.m_emitter.emitBoolJump(op.sinfo, hasreg, hasblock, doneblock);

            this.m_emitter.setActiveBlock(hasblock);
            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(ttype), lreg);
            this.m_emitter.emitTempRegisterAssign(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, lreg, ttype, linfo), iipack[0]);
            this.m_emitter.emitDirectJump(op.sinfo, doneblock);

            this.m_emitter.setActiveBlock(doneblock);
            this.emitConvertIfNeeded(op.sinfo, linfo, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkPostfixGetIndexTry(env: TypeEnvironment, op: PostfixGetIndexTry, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp, op.idx);
        if(hpi === "no") {
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitLoadConstBool(op.sinfo, false, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, op.idx);
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, linfo, lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [aenv.setResultExpression(restype, FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp, op.idx);
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            const hasblock = this.m_emitter.createNewBlock("hasindex");
            const doneblock = this.m_emitter.createNewBlock("doneloadtry");

            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), iipack[0]);
            this.m_emitter.emitBoolJump(op.sinfo, iipack[0], hasblock, doneblock);

            this.m_emitter.setActiveBlock(hasblock);
            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.idx, !texp.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, linfo, lreg);
            this.m_emitter.emitDirectJump(op.sinfo, doneblock);

            this.m_emitter.setActiveBlock(doneblock);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False), aenv.setResultExpression(restype, FlowTypeTruthValue.True)];
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
                ...(renvs.tenvs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, FlowTypeTruthValue.False))),
            ];
        }
    }

    private checkPostfixGetPropertyOrNone(env: TypeEnvironment, op: PostfixGetPropertyOrNone, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp, op.pname);
        if(hpi === "no") {
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialNoneType(), infertype, trgt);

            this.m_emitter.emitLoadConstNone(op.sinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialNoneType(), infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp, op.pname);
            const [restype, iipack] = this.genInferInfo(op.sinfo, linfo, infertype, trgt);

            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, linfo, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
        else {
            const rtype = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp, op.pname);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), rtype]);
            const [restype, iipack] = this.genInferInfo(op.sinfo, linfo, infertype, trgt);

            this.m_emitter.emitTempRegisterAssign(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), this.m_assembly.getSpecialNoneType(), linfo), iipack[0]);
            const hasblock = this.m_emitter.createNewBlock("hasproperty");
            const doneblock = this.m_emitter.createNewBlock("donecheckedload");

            const hasreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitRecordHasProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), hasreg);
            this.m_emitter.emitBoolJump(op.sinfo, hasreg, hasblock, doneblock);

            this.m_emitter.setActiveBlock(hasblock);
            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(rtype), lreg);
            this.m_emitter.emitTempRegisterAssign(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, lreg, rtype, linfo), iipack[0]);
            this.m_emitter.emitDirectJump(op.sinfo, doneblock);

            this.m_emitter.setActiveBlock(doneblock);
            this.emitConvertIfNeeded(op.sinfo, linfo, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkPostfixGetPropertyTry(env: TypeEnvironment, op: PostfixGetPropertyTry, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;
        this.raiseErrorIf(op.sinfo, !texp.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp, op.pname);
        if(hpi === "no") {
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitLoadConstBool(op.sinfo, false, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp, op.pname);
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, linfo, lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [aenv.setResultExpression(restype, FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp, op.pname);
            const [restype, iipack] = this.genInferInfo(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            const hasblock = this.m_emitter.createNewBlock("hasproperty");
            const doneblock = this.m_emitter.createNewBlock("doneloadtry");

            this.m_emitter.emitRecordHasProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), iipack[0]);
            this.m_emitter.emitBoolJump(op.sinfo, iipack[0], hasblock, doneblock);

            this.m_emitter.setActiveBlock(hasblock);
            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp), op.pname, !texp.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, linfo, lreg);
            this.m_emitter.emitDirectJump(op.sinfo, doneblock);

            this.m_emitter.setActiveBlock(doneblock);
            this.emitConvertIfNeeded(op.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            return [env.setResultExpression(restype, FlowTypeTruthValue.False), aenv.setResultExpression(restype, FlowTypeTruthValue.True)];
        }
    }

    private checkInvoke(env: TypeEnvironment, op: PostfixInvoke, arg: MIRTempRegister, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        const resolvefrom = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp;
        const knownimpl = this.m_assembly.tryGetMethodUniqueConcreteDeclFromType(resolvefrom, op.name);

        if (knownimpl !== undefined) {
            let eev = env;
            if (op.isBinder) {
                eev = env.addVar(`$this_#${op.sinfo.pos}`, true, texp, true, texp);

                this.m_emitter.emitLocalVarStore(op.sinfo, arg, `$this_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(texp));
                this.m_emitter.localLifetimeStart(op.sinfo, `$this_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(texp));
            }

            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, [texp, env.getExpressionResult().expvar, arg], refok);
            this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

            const [restype, iipack] = this.genInferInfo(op.sinfo, fsig.resultType, infertype, trgt);
            const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.pragmas.recursive);

            const ckey = this.m_emitter.registerMethodCall(knownimpl.contiainingType, knownimpl.decl, knownimpl.binds, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, fsig.resultType, infertype, iipack);

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
            }

            return [env.setResultExpression(restype)];
        }
        else {
            const vinfo = this.m_assembly.tryGetMethodUniqueRootDeclFromType(texp, op.name);
            this.raiseErrorIf(op.sinfo, vinfo === undefined, `Missing (or multiple possible) declarations of "${op.name}" method`);

            let eev = env;
            if (op.isBinder) {
                eev = env.addVar(`$this_#${op.sinfo.pos}`, true, texp, true, texp);

                this.m_emitter.emitLocalVarStore(op.sinfo, arg, `$this_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(texp));
                this.m_emitter.localLifetimeStart(op.sinfo, `$this_#${op.sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(texp));
            }

            const minfo = vinfo as OOMemberLookupInfo<MemberMethodDecl>;
            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, minfo.decl.invoke, op.terms.targs, minfo.binds, env.terms, [texp, env.getExpressionResult().expvar, arg], refok);
            this.checkTemplateTypes(op.sinfo, minfo.decl.invoke.terms, callbinds, minfo.decl.invoke.termRestrictions);

            const [restype, iipack] = this.genInferInfo(op.sinfo, fsig.resultType, infertype, trgt);
            const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.pragmas.recursive);

            const ckey = this.m_emitter.registerVirtualMethodCall(minfo.contiainingType, minfo.binds, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeVirtualFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, iipack[0]);
            this.emitConvertIfNeeded(op.sinfo, fsig.resultType, infertype, iipack);

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$this_#${op.sinfo.pos}`)
            }

            return [env.setResultExpression(restype)];
        }
    }

    private checkElvisAction(sinfo: SourceInfo, env: TypeEnvironment[], elvisEnabled: boolean, customCheck: Expression | undefined, etrgt: MIRTempRegister, etrgttype: ResolvedType, bailblck: string): [TypeEnvironment[], TypeEnvironment[]] {
        if(!elvisEnabled) {
            return [env, []];
        }

        if (customCheck === undefined) {
            const paths = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), env);

            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always some just keep going on current block emit
            }
            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always none
                this.m_emitter.emitDirectJump(sinfo, bailblck);
            }
            else {
                const nextblk = this.m_emitter.createNewBlock("Lelvis");
                this.m_emitter.emitNoneJump(sinfo, etrgt, bailblck, nextblk);
                this.m_emitter.setActiveBlock(nextblk);
            }

            return [paths.fenvs, paths.tenvs];
        }
        else {
            const eev = TypeEnvironment.join(this.m_assembly, ...env).addVar(`$chkval_#${sinfo.pos}`, true, etrgttype, true, etrgttype);
            this.m_emitter.emitLocalVarStore(sinfo, etrgt, `$chkval_#${sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(etrgttype));
            this.m_emitter.localLifetimeStart(sinfo, `$chkval_#${sinfo.pos}`, this.m_emitter.registerResolvedTypeReference(etrgttype));

            const ctrgt = this.m_emitter.generateTmpRegister();
            const cenv = this.checkExpressionMultiFlow(eev, customCheck, ctrgt, this.m_assembly.getSpecialBoolType());
            const paths = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, cenv);

            this.m_emitter.localLifetimeEnd(sinfo, `$chkval_#${sinfo.pos}`)

            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always some just keep going on current block emit
            }
            if (paths.tenvs.length === 0 && paths.fenvs.length !== 0) {
                //always none
                this.m_emitter.emitDirectJump(sinfo, bailblck);
            }
            else {
                const nextblk = this.m_emitter.createNewBlock("Lelvis");
                this.m_emitter.emitBoolJump(sinfo, etrgt, bailblck, nextblk);
                this.m_emitter.setActiveBlock(nextblk);
            }

            const eresultvar = eev.getExpressionResult().expvar;
            const eresultflow = eev.getExpressionResult().truthval;
            return [paths.fenvs.map((ee) => ee.setResultExpressionWVarOptNoInfer(etrgttype, eresultvar, eresultflow)), paths.tenvs.map((ee) => ee.setResultExpressionWVarOptNoInfer(etrgttype, eresultvar, eresultflow))];
        }
    }

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck ? this.m_emitter.createNewBlock("Lelvis_none") : "INVALID";

        let etgrt = this.m_emitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt, undefined, {refok: refok, orok: false});

        let scflows: TypeEnvironment[] = [];
        let cenv = eenv;
        for (let i = 0; i < exp.ops.length; ++i) {
            const etrgttype = this.m_assembly.typeUpperBound(cenv.map((ee) => ee.getExpressionResult().exptype));
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, exp.ops[i].customCheck, etgrt, etrgttype, noneblck);
            scflows = [...scflows, ...scflow];

            const itype = (i + 1 === exp.ops.length) ? infertype : undefined;

            if(fflow.length === 0) {
                cenv = [];
                break;
            }
            const nflow = TypeEnvironment.join(this.m_assembly, ...fflow);

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
                case PostfixOpTag.PostfixGetIndexOrNone:
                    cenv = this.checkPostfixGetIndexOrNone(nflow, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixGetIndexTry:
                    cenv = this.checkPostfixGetIndexTry(nflow, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixGetPropertyOrNone:
                    cenv = this.checkPostfixGetPropertyOrNone(nflow, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt, itype);
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    cenv = this.checkPostfixGetPropertyTry(nflow, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt, itype);
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
        if(action.chk === "truealways" || action.chk === "falsealways") {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

            this.m_emitter.emitLoadConstBool(exp.sinfo, action.chk === "truealways" ? true : false, iipack[0]);

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
            return [env.setResultExpression(restype, action.chk === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action.chk === "lhsnone" || action.chk === "rhsnone") {
            const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);
            
            if(action.chk === "lhsnone") {
                this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().exptype));
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().exptype));
            }

            this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);

            const eevs = (action.chk === "lhsnone") ? rhs : lhs;
            const renvs = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [eevs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setResultExpression(restype, FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setResultExpression(restype, FlowTypeTruthValue.False)))
            ];
        }
        else {
            let olhsreg = lhsreg;
            let olhs = lhs.getExpressionResult().exptype;

            let orhsreg = rhsreg;
            let orhs = rhs.getExpressionResult().exptype;

            let doneblock: string | undefined = undefined;
            let cenv = env;
            let fenv: TypeEnvironment[] = [];
            if(action.lnotnonechk || action.rnotnonechk) {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);
                const okblock = this.m_emitter.createNewBlock("notnone");
                doneblock = this.m_emitter.createNewBlock("doneeq");

                if(action.lnotnonechk) {
                    this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeConceptType()), olhsreg, this.m_emitter.registerResolvedTypeReference(olhs));

                    const nlhsreg = this.m_emitter.generateTmpRegister();
                    const nlhs = ResolvedType.create(olhs.options.filter((opt) => opt.idStr !== "NSCore::None"));

                    this.m_emitter.emitConvertDown(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs), 
                    this.m_emitter.registerResolvedTypeReference(nlhs), olhsreg, nlhsreg);

                    olhsreg = nlhsreg;
                    olhs = nlhs;

                    const splits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialSomeConceptType(), [lhs]);
                    cenv = TypeEnvironment.join(this.m_assembly, ...splits.tenvs);
                    splits.fenvs;
                }
                else {
                    this.m_emitter.emitTypeOf(exp.sinfo, iipack[0], this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeConceptType()), orhsreg, this.m_emitter.registerResolvedTypeReference(orhs));

                    const nrhsreg = this.m_emitter.generateTmpRegister();
                    const nrhs = ResolvedType.create(orhs.options.filter((opt) => opt.idStr !== "NSCore::None"));

                    this.m_emitter.emitConvertDown(exp.sinfo, this.m_emitter.registerResolvedTypeReference(orhs), 
                    this.m_emitter.registerResolvedTypeReference(nrhs), olhsreg, nrhsreg);

                    orhsreg = nrhsreg;
                    orhs = nrhs;

                    const splits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialSomeConceptType(), [rhs]);
                    cenv = TypeEnvironment.join(this.m_assembly, ...splits.tenvs);
                    fenv = splits.fenvs;
                }

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
                this.m_emitter.emitBoolJump(exp.sinfo, iipack[0], okblock, doneblock);
                this.m_emitter.setActiveBlock(doneblock);

                fenv = fenv.map((eev) => eev.setResultExpression(restype, FlowTypeTruthValue.False));
            }

            if (action.chk === "stringof" || action.chk === "datastring") {
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
            
            if(action.chk === "keytuple" || action.chk === "keyrecord") {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, trgt);

                if(exp.op === "==") {
                    this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs), olhsreg, this.m_emitter.registerResolvedTypeReference(orhs), orhsreg, iipack[0]);
                }
                if(exp.op === "!=") {
                    const treg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(olhs), olhsreg, this.m_emitter.registerResolvedTypeReference(orhs), orhsreg, treg);
                    this.m_emitter.emitPrefixNotOp(exp.sinfo, treg, iipack[0]);
                }

                if(doneblock !== undefined) {
                    this.m_emitter.emitDirectJump(exp.sinfo, doneblock);
                    this.m_emitter.setActiveBlock(doneblock);
                }

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialBoolType(), infertype, iipack);
                return [cenv.setResultExpression(restype), ...fenv];
            }
            else {
                const eargs = [
                    { name: undefined, argtype: olhs, ref: undefined, expando: false, pcode: undefined, treg: olhsreg },
                    { name: undefined, argtype: orhs, ref: undefined, expando: false, pcode: undefined, treg: orhsreg }
                ];

                const opns = this.m_assembly.getNamespace("NSMain") as NamespaceDeclaration;
                const opdecls = (opns.operators.get(exp.op) as NamespaceOperatorDecl[]).filter((nso) => !OOPTypeDecl.attributeSetContains("abstract", nso.attributes));
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

                const rargs = this.checkArgumentsWOperator(exp.sinfo, cenv, ["a", "b"], false, eargs);

                const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types, isigs);

                this.raiseErrorIf(exp.sinfo, opidx !== -1, "Cannot resolve operator");
                const opdecl = opdecls[opidx];

                const renv = this.checkNamespaceOperatorInvoke(exp.sinfo, cenv, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, new PragmaArguments("no", []), trgt, false, infertype);

                if(doneblock !== undefined) {
                    this.m_emitter.emitDirectJump(exp.sinfo, doneblock);
                    this.m_emitter.setActiveBlock(doneblock);
                }

                return [...renv, ...fenv];
            }
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

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });
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

    private checkNonecheck(env: TypeEnvironment, exp: NonecheckExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, infertype, { refok: refok, orok: false });

        if (exp.customCheck === undefined) {
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), lhs);
            if (fflows.fenvs.length === 0) {
                const [restype, iipack] = this.genInferInfo(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, trgt);

                this.m_emitter.emitLoadConstNone(exp.sinfo, iipack[0]);

                this.emitConvertIfNeeded(exp.sinfo, this.m_assembly.getSpecialNoneType(), infertype, iipack);
                return lhs.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar));
            }
            else {
                const noneblck = this.m_emitter.createNewBlock("Lnonecheck_none");
                const doneblck = this.m_emitter.createNewBlock("Lnonecheck_done");
                const restblck = this.m_emitter.createNewBlock("Lnonecheck_rest");

                this.m_emitter.emitNoneJump(exp.sinfo, lhsreg, noneblck, restblck);

                this.m_emitter.setActiveBlock(restblck);
                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, rhsreg, infertype, { refok: refok, orok: false });

                const oflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), rhs);
                const rflows = [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs];

                const resttype = this.m_assembly.typeUpperBound([...oflows.fenvs, ...oflows.tenvs].map((eev) => eev.getExpressionResult().exptype));
                const fulltype = this.m_assembly.typeUpperBound([...rflows].map((eev) => eev.getExpressionResult().exptype));

                const [restype, iipack] = this.genInferInfo(exp.sinfo, fulltype, infertype, trgt);

                const rcarg = this.emitInlineConvertIfNeeded(exp.sinfo, rhsreg, resttype, fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, rcarg, iipack[0]);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(noneblck);
                const convreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadConstNone(exp.sinfo, convreg);
                const convarg = this.emitInlineConvertIfNeeded(exp.sinfo, convreg, this.m_assembly.getSpecialNoneType(), fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, convarg, iipack[0]);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);
                this.emitConvertIfNeeded(exp.sinfo, fulltype, infertype, iipack);

                return [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar));
            }
        }
        else {
            //
            //TODO: Implement this path
            //
            this.raiseError(exp.sinfo, "checkNonecheck with custom op is not implemented!!!");
            return [];
        }
    }

    private checkCoalesce(env: TypeEnvironment, exp: CoalesceExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, infertype, { refok: refok, orok: false });

        if (exp.customCheck === undefined) {
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), lhs);

            if (fflows.tenvs.length === 0) {
                return this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, trgt, infertype, { refok: refok, orok: false });
            }
            else {
                const someblck = this.m_emitter.createNewBlock("Lcoalesce_some");
                const doneblck = this.m_emitter.createNewBlock("Lcoalesce_done");
                const restblck = this.m_emitter.createNewBlock("Lcoalesce_rest");

                this.m_emitter.emitNoneJump(exp.sinfo, lhsreg, restblck, someblck);

                this.m_emitter.setActiveBlock(restblck);
                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, infertype, { refok: refok, orok: false });

                const oflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), rhs);
                const rflows = [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs];

                const sometype = this.m_assembly.typeUpperBound([...oflows.fenvs, ...oflows.tenvs].map((eev) => eev.getExpressionResult().exptype));
                const fulltype = this.m_assembly.typeUpperBound([...rflows].map((eev) => eev.getExpressionResult().exptype));

                const [restype, iipack] = this.genInferInfo(exp.sinfo, fulltype, infertype, trgt);

                const rcarg = this.emitInlineConvertIfNeeded(exp.sinfo, rhsreg, sometype, fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, rcarg, iipack[0]);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(someblck);
                const convarg = this.emitInlineConvertIfNeeded(exp.sinfo, lhsreg, this.m_assembly.typeUpperBound([...fflows.fenvs].map((eev) => eev.getExpressionResult().exptype)), fulltype);
                this.m_emitter.emitTempRegisterAssign(exp.sinfo, convarg, iipack[0]);
                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.setActiveBlock(doneblck);
                this.emitConvertIfNeeded(exp.sinfo, fulltype, infertype, iipack);

                return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar));
            }
        }
        else {
            //
            //TODO: Implement this path
            //
            this.raiseError(exp.sinfo, "checkCoalesce with custom op is not implemented!!!");
            return [];
        }
    }

    private checkSelect(env: TypeEnvironment, exp: SelectExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg, this.m_assembly.getSpecialBoolType(), { refok: refok, orok: false });

        const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        
        if(fflows.tenvs.length === 0) {
            return [this.checkExpression(env, exp.option2, trgt, infertype)];
        }
        else if (fflows.fenvs.length === 0) {
            return [this.checkExpression(env, exp.option1, trgt, infertype)];
        }
        else {
            const doneblck = this.m_emitter.createNewBlock("Lselect_done");
            const trueblck = this.m_emitter.createNewBlock("Lselect_true");
            const falseblck = this.m_emitter.createNewBlock("Lselect_false");

            this.m_emitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);

            this.m_emitter.setActiveBlock(trueblck);
            const truereg = this.m_emitter.generateTmpRegister();
            const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.option1, truereg, infertype);
            //note jump isn't set yet

            this.m_emitter.setActiveBlock(falseblck);
            const falsereg = this.m_emitter.generateTmpRegister();
            const falsestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.option2, falsereg, infertype);
            //note jump isn't set yet

            const fulltype = this.m_assembly.typeUpperBound([truestate.getExpressionResult().exptype, falsestate.getExpressionResult().exptype]);
            const [restype, iipack] = this.genInferInfo(exp.sinfo, fulltype, infertype, trgt);

            //set the assigns and jumps
            this.m_emitter.setActiveBlock(trueblck);
            const trueconv = this.emitInlineConvertIfNeeded(exp.sinfo, truereg, truestate.getExpressionResult().exptype, fulltype);
            this.m_emitter.emitTempRegisterAssign(exp.sinfo, trueconv, iipack[0]);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(falseblck);
            const falseconv = this.emitInlineConvertIfNeeded(exp.sinfo, falsereg, falsestate.getExpressionResult().exptype, fulltype);
            this.m_emitter.emitTempRegisterAssign(exp.sinfo, falseconv, iipack[0]);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(doneblck);
            this.emitConvertIfNeeded(exp.sinfo, fulltype, infertype, iipack);

            return [env.setResultExpression(restype)];
        }
    }

    private checkOrExpression(env: TypeEnvironment, exp: ExpOrExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined, extraok: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !extraok.orok, "Or expression is not valid in this position");

        const scblck = this.m_emitter.createNewBlock("Lorcheck_return");
        const regularblck = this.m_emitter.createNewBlock("Lorcheck_regular");

        let normalexps: TypeEnvironment[] = [];
        let terminalexps: TypeEnvironment[] = [];

        if((exp.cond !== "none" && exp.cond !== "err") || exp.result !== undefined) {
            const eereg = this.m_emitter.generateTmpRegister();
            let evalue = this.checkExpressionMultiFlow(env, exp.exp, eereg, undefined, {refok: extraok.refok, orok: false});

            evalue = evalue.map((ev) => ev.pushLocalScope().addVar("$value", true, ev.getExpressionResult().exptype, true, ev.getExpressionResult().exptype));
            const etype = this.m_assembly.typeUpperBound(evalue.map((eev) => eev.getExpressionResult().exptype));

            this.m_emitter.localLifetimeStart(exp.sinfo, "$value", this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitLocalVarStore(exp.sinfo, eereg, "$value", this.m_emitter.registerResolvedTypeReference(etype));
            
            //
            //TODO: these cases need to be implemented!!!
            //
            this.raiseError(exp.sinfo, "NOT IMPLEMENTED!!!");

            return [env];
        }
        else {
            let eeinfer: ResolvedType | undefined = undefined;
            if (exp.cond === "none") {
                eeinfer = infertype !== undefined ? this.m_assembly.typeUpperBound([infertype, this.m_assembly.getSpecialNoneType()]) : undefined;
            }
            else {
                let iitype = exp.action === "return" ? env.inferResult : env.inferYield[env.inferYield.length - 1];
                eeinfer = iitype !== undefined && iitype.isResultGeneralType() ? iitype : undefined;
            }

            const eereg = this.m_emitter.generateTmpRegister();
            const evalue = this.checkExpressionMultiFlow(env, exp.exp, eereg, eeinfer, {refok: extraok.refok, orok: false});
            const etype = this.m_assembly.typeUpperBound(evalue.map((eev) => eev.getExpressionResult().exptype));

            //do test for return or normal result
            if (exp.cond === "none") {
                const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), evalue);
                normalexps = flows.fenvs
                terminalexps = flows.tenvs;

                if (normalexps.length === 0 || terminalexps.length === 0) {
                    this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
                }
                else {
                    this.m_emitter.emitNoneJump(exp.sinfo, eereg, scblck, regularblck);
                }
            }
            else {
                const oktype = this.getResultSubtypes(etype)[0];
                const flows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oktype, evalue);
                normalexps = flows.tenvs
                terminalexps = flows.fenvs;

                if (normalexps.length === 0 || terminalexps.length === 0) {
                    this.m_emitter.emitDirectJump(exp.sinfo, normalexps.length !== 0 ? regularblck : scblck);
                }
                else {
                    const treg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitCheckNoError(exp.sinfo, eereg, this.m_emitter.registerResolvedTypeReference(etype), treg);

                    this.m_emitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
                }
            }

            //load early return block and process
            let terminalenvironments: TypeEnvironment[] = [];
            if (terminalexps.length !== 0) {
                const terminaltype = this.m_assembly.typeUpperBound(terminalexps.map((eev) => eev.getExpressionResult().exptype));

                this.m_emitter.setActiveBlock(scblck);
                if (exp.action === "return") {
                    this.raiseErrorIf(exp.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

                    this.m_emitter.getActiveReturnSet().push([this.m_emitter.getActiveBlockName(), eereg, terminaltype]);
                    terminalenvironments = [env.setReturn(this.m_assembly, terminaltype)];
                }
                else {
                    this.raiseErrorIf(exp.sinfo, !env.isInYieldBlock(), "Cannot use yield statment unless inside and expression block");

                    this.m_emitter.getActiveYieldSet().push([this.m_emitter.getActiveBlockName(), eereg, terminaltype]);
                    terminalenvironments = [env.setYield(this.m_assembly, terminaltype)];
                }
            }

            //load normal block and process
            let normalenvironments: TypeEnvironment[] = [];
            this.m_emitter.setActiveBlock(regularblck);
            if (normalexps.length !== 0) {
                if (exp.cond === "none") {
                    const stype = this.m_assembly.splitTypes(etype, this.m_assembly.getSpecialNoneType()).fp;

                    const [restype, iipack] = this.genInferInfo(exp.sinfo, stype, infertype, trgt);
                    this.m_emitter.emitTempRegisterAssign(exp.sinfo, eereg, iipack[0]);
                    this.emitConvertIfNeeded(exp.sinfo, stype, infertype, iipack);

                    normalenvironments = normalexps.map((eev) => eev.setResultExpression(restype));
                }
                else {
                    const rok = this.getResultSubtypes(etype)[0];
                    const convt = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitConvertDown(exp.sinfo, this.m_emitter.registerResolvedTypeReference(etype), this.m_emitter.registerResolvedTypeReference(rok), eereg, convt);

                    const [restype, iipack] = this.genInferInfo(exp.sinfo, this.getResultBinds(etype).T, infertype, trgt);
                    this.m_emitter.emitExtractResult(exp.sinfo, convt, this.m_emitter.registerResolvedTypeReference(rok), iipack[0]);
                    this.emitConvertIfNeeded(exp.sinfo, this.getResultBinds(etype).T, infertype, iipack);

                    normalenvironments = normalexps.map((eev) => eev.setResultExpression(restype));
                }
            }

            return [...normalenvironments, ...terminalenvironments];
        }
    }

    private checkBlockExpression(env: TypeEnvironment, exp: BlockStatementExpression, infertype: ResolvedType | undefined, trgt: MIRTempRegister): TypeEnvironment[] {
        try {
            this.m_emitter.processEnterYield();
            let cenv = env.freezeVars().pushLocalScope();

            for (let i = 0; i < exp.ops.length; ++i) {
                if (!cenv.hasNormalFlow()) {
                    break;
                }

                cenv = this.checkStatement(cenv, exp.ops[i]);
            }

            const yblck = this.m_emitter.createNewBlock("Lyield");
            if (cenv.hasNormalFlow()) {
                this.m_emitter.setActiveBlock(yblck);

                const deadvars = cenv.getCurrentFrameNames();
                for (let i = 0; i < deadvars.length; ++i) {
                    this.m_emitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
                }
            }

            this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
            this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");

            const ytype = cenv.yieldResult as ResolvedType;
            const [restype, iipack] = this.genInferInfo(exp.sinfo, ytype, infertype, trgt);

            const yeildcleanup = this.m_emitter.getActiveYieldSet();
            if (cenv.hasNormalFlow()) {
                for (let i = 0; i < yeildcleanup.length; ++i) {
                    const yci = yeildcleanup[i];

                    this.m_emitter.setActiveBlock(yci[0]);

                    const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, yci[1], yci[2], ytype);
                    this.m_emitter.emitTempRegisterAssign(exp.sinfo, convreg, iipack[0]);
                    this.emitConvertIfNeeded(exp.sinfo, ytype, infertype, iipack);

                    this.m_emitter.emitDirectJump(exp.sinfo, yblck);
                }
            }

            return [env.setResultExpression(restype)];
        }
        finally {
            this.m_emitter.processExitYield();
        }
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined,): TypeEnvironment[] {
        const doneblck = this.m_emitter.createNewBlock("Lifexp_done");

        let cenv = env;
        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRTempRegister, ResolvedType][] = [];

        for (let i = 0; i < exp.flow.conds.length && hasfalseflow; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg, infertype, i === 0 ? { refok: refok, orok: false } : undefined);
            this.raiseErrorIf(exp.sinfo, !test.every((eev) => eev.getExpressionResult().exptype.isSameType(this.m_assembly.getSpecialBoolType())), "If test expression must return a Bool");

            const cflow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
            
            if (cflow.tenvs.length === 0) {
                //can just keep generating tests in striaght line
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
            else if (cflow.fenvs.length === 0) {
                //go though true block (without jump) and then skip else
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                this.m_emitter.emitDirectJump(exp.sinfo, trueblck);
                this.m_emitter.setActiveBlock(trueblck);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().exptype]);
                hasfalseflow = false;
            }
            else {
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                const falseblck = this.m_emitter.createNewBlock(`Lifexp_${i}false`);
                
                this.m_emitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
                this.m_emitter.setActiveBlock(trueblck);
                
                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                this.m_emitter.setActiveBlock(falseblck);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().exptype]);
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
        }

        if(hasfalseflow) {
            const ttreg = this.m_emitter.generateTmpRegister();
            const aenv = this.checkExpression(cenv, exp.flow.elseAction as Expression, ttreg, infertype);

            results.push(aenv);
            rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, aenv.getExpressionResult().exptype]);
        }

        this.raiseErrorIf(exp.sinfo, results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const etype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().exptype));
        const [restype, iipack] = this.genInferInfo(exp.sinfo, etype, infertype, trgt);

        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], etype);
            this.m_emitter.emitTempRegisterAssign(exp.sinfo, convreg, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, etype, infertype, iipack);

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return results.map((eev) => eev.setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
    }

    private checkMatchExpression(env: TypeEnvironment, exp: MatchExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$match_#${exp.sinfo.pos}`;
        let cenv = venv.pushLocalScope().addVar(matchvar, true, venv.getExpressionResult().exptype, true, venv.getExpressionResult().exptype, venv.getExpressionResult().truthval);

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, MIRTempRegister, ResolvedType][] = [];
        for (let i = 0; i < exp.flow.length && !hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, i, cenv, matchvar, exp.flow[i].check, nextlabel, actionlabel);

            if(test.tenvs.length === 0) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = TypeEnvironment.join(this.m_assembly, ...test.fenvs);
            }
            else if(test.fenvs.length === 0) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...test.tenvs), exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().exptype]);

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(TypeEnvironment.join(this.m_assembly, ...test.tenvs), exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().exptype]);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = TypeEnvironment.join(this.m_assembly, ...test.fenvs);
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(exp.sinfo, "exhaustive");
        }

        this.raiseErrorIf(exp.sinfo, results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const etype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().exptype));
        const [restype, iipack] = this.genInferInfo(exp.sinfo, etype, infertype, trgt);

        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], etype);
            this.m_emitter.emitTempRegisterAssign(exp.sinfo, convreg, iipack[0]);
            this.emitConvertIfNeeded(exp.sinfo, etype, infertype, iipack);

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return results.map((eev) => eev.popLocalScope().setResultExpressionWVarOptNoInfer(restype, eev.getExpressionResult().expvar, eev.getExpressionResult().truthval));
    }

    private checkExpression(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment {
        const res = this.checkExpressionMultiFlow(env, exp, trgt, infertype, extraok);
        this.raiseErrorIf(exp.sinfo, res.length === 0, "No feasible flow for expression");

        return TypeEnvironment.join(this.m_assembly, ...res);
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression, trgt, infertype);
            case ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression, trgt, infertype);
            case ExpressionTag.LiteralIntegralExpression:
                return this.checkLiteralIntegralExpression(env, exp as LiteralIntegralExpression, trgt, infertype);
            case ExpressionTag.LiteralFloatPointExpression:
                return this.checkLiteralFloatExpression(env, exp as LiteralFloatPointExpression, trgt, infertype);
            case ExpressionTag.LiteralRationalExpression:
                return this.checkLiteralRationalExpression(env, exp as LiteralRationalExpression, trgt, infertype);
            case ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression, trgt, infertype);
            case ExpressionTag.LiteralRegexExpression:
                return this.checkLiteralRegexExpression(env, exp as LiteralRegexExpression, trgt, infertype);
            case ExpressionTag.LiteralParamerterValueExpression:
                return this.checkLiteralParameterValeExpression(env, exp as LiteralParamerterValueExpression, trgt, infertype);
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt, infertype);
            case ExpressionTag.LiteralTypedNumericConstructorExpression:
                return this.checkTypedTypedNumericConstructor(env, exp as LiteralTypedNumericConstructorExpression, trgt, infertype);
            case ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkDataStringConstructor(env, exp as LiteralTypedStringConstructorExpression, trgt, infertype);
            case ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression, trgt, infertype);
            case ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression, trgt, infertype);
            case ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp as AccessVariableExpression, trgt, infertype);
            case ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression, trgt, infertype);
            case ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt, infertype);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt, infertype);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt, infertype);
            case ExpressionTag.ConstructorEphemeralValueList:
                return this.checkConstructorEphemeralValueList(env, exp as ConstructorEphemeralValueList, trgt, infertype);
            case ExpressionTag.PCodeInvokeExpression:
                return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.SpecialConstructorExpression:
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, trgt, infertype);
            case ExpressionTag.CallNamespaceFunctionOrOperatorExpression:
                return this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.CallStaticFunctionOrOperatorExpression:
                return this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.OfTypeConvertExpression:
                return this.checkOfTypeConvertExpression(env, exp as OfTypeConvertExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.PostfixOpExpression:
                return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.PrefixNotOpExpression:
                return this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.BinEqExpression:
                return this.checkBinEq(env, exp as BinEqExpression, trgt, infertype);
            case ExpressionTag.BinCmpExpression:
                return this.checkBinCmp(env, exp as BinCmpExpression, trgt, infertype);
            case ExpressionTag.BinLogicExpression:
                return this.checkBinLogic(env, exp as BinLogicExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.MapEntryConstructorExpression:
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, trgt, infertype);
            case ExpressionTag.NonecheckExpression:
                return this.checkNonecheck(env, exp as NonecheckExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.CoalesceExpression:
                return this.checkCoalesce(env, exp as CoalesceExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp as ExpOrExpression, trgt, infertype, extraok || { refok: false, orok: false });
            case ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp as BlockStatementExpression, infertype, trgt);
            case ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp as IfExpression, trgt, (extraok && extraok.refok) || false, infertype);
            default:
                this.raiseErrorIf(exp.sinfo, exp.tag !== ExpressionTag.MatchExpression, "Unknown expression");
                return this.checkMatchExpression(env, exp as MatchExpression, trgt, (extraok && extraok.refok) || false, infertype);
        }
    }

    private checkDeclareSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, venv: { etype: ResolvedType, etreg: MIRTempRegister } | undefined): TypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), "Cannot shadow previous definition");

        this.raiseErrorIf(sinfo, venv === undefined && isConst, "Must define const var at declaration site");
        this.raiseErrorIf(sinfo, venv === undefined && decltype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? (venv as { etype: ResolvedType, etreg: MIRTempRegister }).etype : this.resolveAndEnsureTypeOnly(sinfo, decltype, env.terms);
        this.raiseErrorIf(sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.etype, vtype), "Expression is not of declared type");

        const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype);
        this.m_emitter.localLifetimeStart(sinfo, vname, mirvtype);

        if (venv !== undefined) {
            const convreg = this.emitInlineConvertIfNeeded(sinfo, venv.etreg, venv.etype, vtype) as MIRTempRegister;
            this.m_emitter.emitLocalVarStore(sinfo, convreg, vname, mirvtype);
        }

        return env.addVar(vname, isConst, vtype, venv !== undefined, venv !== undefined ? venv.etype : vtype);
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        const infertype = stmt.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vtype, env.terms);

        const etreg = this.m_emitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true }) : undefined;

        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().exptype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        const vv = venv !== undefined ? { etype: venv.getExpressionResult().exptype, etreg: etreg } : undefined;
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
                let infertypes = stmt.vars.map((vds) => vds.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, vds.vtype, env.terms));
                let infertype = infertypes.includes(undefined) ? undefined : ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes as ResolvedType[]));

                const etreg = this.m_emitter.generateTmpRegister();
                const ve = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true }).getExpressionResult().exptype;

                this.raiseErrorIf(stmt.sinfo, ve.options.length !== 1 || !(ve.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

                const elt = ve.options[0] as ResolvedEphemeralListType;
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== elt.types.length, "Missing initializers for variables");

                //check if all the assignments are conversion free -- if so we can do a multi-load
                const convertfree = stmt.vars.every((v, i) => {
                    const decltype = this.resolveAndEnsureTypeOnly(stmt.sinfo, v.vtype, env.terms);
                    const exptype = elt.types[i];

                    return decltype.isSameType(exptype);
                });

                if(convertfree) {
                    this.raiseErrorIf(stmt.sinfo, stmt.vars.some((vv) => env.isVarNameDefined(vv.name), "Cannot shadow previous definition"));

                    let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const decltype = this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);
                        const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);
                        this.m_emitter.localLifetimeStart(stmt.sinfo, stmt.vars[i].name, mirvtype);

                        trgts.push({ pos: i, into: new MIRLocalVariable(stmt.vars[i].name), oftype: mirvtype });
                    }

                    this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(ve), trgts);

                    cenv = cenv.multiVarUpdate(stmt.vars.map((vv) => [stmt.isConst, vv.name, this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms), [], this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms)]), []);
                }
                else {
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const tlreg = this.m_emitter.generateTmpRegister();
                        this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(ve), tlreg);

                        cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: elt.types[i], etreg: tlreg });
                    }
                }
            }
            else {
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== stmt.exp.length, "Missing initializers for variables");

                for (let i = 0; i < stmt.vars.length; ++i) {
                    const infertype = stmt.vars[i].vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype).getExpressionResult().exptype;

                    cenv = this.checkDeclareSingleVariable(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: venv, etreg: etreg });
                }
            }
        }

        return cenv;
    }

    private checkAssignSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, etype: ResolvedType, etreg: MIRTempRegister): TypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, "Variable was not previously defined");
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(etype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        const convreg = this.emitInlineConvertIfNeeded(sinfo, etreg, etype, (vinfo as VarInfo).declaredType) as MIRTempRegister;
        this.m_emitter.emitLocalVarStore(sinfo, convreg, vname, this.m_emitter.registerResolvedTypeReference((vinfo as VarInfo).declaredType));

        return env.setVar(vname, etype);
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.lookupVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfo === undefined, "Variable was not previously defined");

        const infertype = (vinfo as VarInfo).declaredType;
        const etreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true });
       
        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().exptype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        return this.checkAssignSingleVariable(stmt.sinfo, env, stmt.name, venv.getExpressionResult().exptype, etreg);
    }

    private checkVariablePackAssignmentStatement(env: TypeEnvironment, stmt: VariablePackAssignmentStatement): TypeEnvironment {
        let cenv = env;

        if (stmt.exp.length === 1) {
            let infertypes = stmt.names.map((vn) => env.lookupVar(vn));
            this.raiseErrorIf(stmt.sinfo, infertypes.includes(null), "Variable was not previously defined");
            let infertype = ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes.map((vi) => (vi as VarInfo).declaredType)));

            const etreg = this.m_emitter.generateTmpRegister();
            const ve = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true }).getExpressionResult().exptype;

            this.raiseErrorIf(stmt.sinfo, ve.options.length !== 1 || !(ve.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

            const elt = ve.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== elt.types.length, "Missing initializers for variables");

            //check if all the assignments are conversion free -- if so we can do a multi-load
            const convertfree = stmt.names.every((v, i) => {
                const decltype = (env.lookupVar(v) as VarInfo).declaredType;
                const exptype = elt.types[i];

                return decltype.isSameType(exptype);
            });

            if (convertfree) {
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => !env.isVarNameDefined(vv), "Variable was not previously defined"));
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => (env.lookupVar(vv) as VarInfo).isConst, "Variable is const"));

                let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                for (let i = 0; i < stmt.names.length; ++i) {
                    const decltype = (env.lookupVar(stmt.names[i]) as VarInfo).declaredType;
                    const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);

                    const vstore = env.getLocalVarInfo(stmt.names[i]) === undefined ? new MIRParameterVariable(stmt.names[i]) : new MIRLocalVariable(stmt.names[i]);
                    trgts.push({ pos: i, into: vstore, oftype: mirvtype });
                }

                this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(ve), trgts);

                cenv = cenv.multiVarUpdate([], stmt.names.map((vv) => [vv, [], (env.lookupVar(vv) as VarInfo).declaredType]));
            }
            else {
                for (let i = 0; i < stmt.names.length; ++i) {
                    const tlreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(ve), tlreg);

                    cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], elt.types[i], etreg);
                }
            }
        }
        else {
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== stmt.exp.length, "Missing initializers for variables");

            for (let i = 0; i < stmt.names.length; ++i) {
                const vinfo = env.lookupVar(stmt.names[i]);
                this.raiseErrorIf(stmt.sinfo, vinfo === null, "Variable was not previously defined");

                const infertype = (vinfo as VarInfo).declaredType;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype).getExpressionResult().exptype;

                cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], venv, etreg);
            }
        }

        return cenv;
    }

    private checkSimpleStructuredAssignment(sinfo: SourceInfo, env: TypeEnvironment, etype: ResolvedType,
        assign: StructuredAssignment, isoptional: boolean, cpath: StructuredAssignmentPathStep | undefined,
        allDeclared: [string, ResolvedType, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allAssigned: [string, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allChecks: [StructuredAssignmentPathStep | undefined, StructuredAssignmentCheck][]): boolean 
    {
        if(isoptional && !(assign instanceof IgnoreTermStructuredAssignment && assign.isOptional)) {
            return false;
        }

        if (assign instanceof IgnoreTermStructuredAssignment) {
            const itype = this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms);

            const optt = this.m_assembly.splitTypes(etype, itype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, itype, isoptional)]);
            }

            return true;
        }
        else if (assign instanceof ConstValueStructuredAssignment) {
            allChecks.push([cpath, createTerminalEqCheck(etype, assign.constValue)]);

            return true;
        }
        else if (assign instanceof VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[0] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vtype = (assign.vtype instanceof AutoTypeSignature) ? etype : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms);
            allDeclared.push([assign.vname, vtype, cpath, etype]);

            const optt = this.m_assembly.splitTypes(etype, vtype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, vtype, false)]);
            }

            return true;
        }
        else if (assign instanceof VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[0] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");

            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

            allAssigned.push([assign.vname, cpath, etype]);

            const optt = this.m_assembly.splitTypes(etype, (vinfo as VarInfo).declaredType);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([cpath, createOfTypeCheck(etype, (vinfo as VarInfo).declaredType, false)]);
            }

            return true;
        }
        else {
            assert(false);
            return false;
        }
    }

    private checkStructuredMatch(sinfo: SourceInfo, env: TypeEnvironment, etype: ResolvedType,
        assign: StructuredAssignment,
        allDeclared: [string, ResolvedType, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allAssigned: [string, StructuredAssignmentPathStep | undefined, ResolvedType][],
        allChecks: [StructuredAssignmentPathStep | undefined, StructuredAssignmentCheck][]): boolean {
        if (assign instanceof ValueListStructuredAssignment) {
            if (etype.options.length !== 1 || !(etype.options[0] instanceof ResolvedEphemeralListType)) {
                return false;
            }

            const eltype = etype.options[0] as ResolvedEphemeralListType;
            if (eltype.types.length !== assign.assigns.length) {
                return false;
            }

            let chksok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const step = createEphemeralStructuredAssignmentPathStep(etype, eltype.types[i], i);
                const ok = this.checkSimpleStructuredAssignment(sinfo, env, eltype.types[i], assign.assigns[i], false, step, allDeclared, allAssigned, allChecks);

                chksok = chksok && ok;
            }

            return chksok;
        }
        else if (assign instanceof NominalStructuredAssignment) {
            const ntype = this.resolveAndEnsureTypeOnly(sinfo, assign.atype, env.terms);
            if (ntype.options.length === 1 && ntype.options[0] instanceof ResolvedEntityAtomType) {
                const isstruct = OOPTypeDecl.attributeSetContains("struct", (ntype.options[0] as ResolvedEntityAtomType).object.attributes);
                this.raiseErrorIf(sinfo, isstruct !== assign.isvalue, "Mismatch in value type of Entity and match");
            }
            else {
                this.raiseErrorIf(sinfo, ntype.options.length !== 1 || !(ntype.options[0] instanceof ResolvedConceptAtomType));
                const anystructcpt = (ntype.options[0] as ResolvedConceptAtomType).conceptTypes.some((cpt) => OOPTypeDecl.attributeSetContains("struct", cpt.concept.attributes));
                this.raiseErrorIf(sinfo, anystructcpt !== assign.isvalue, "Mismatch in value type of Concept and match");
            }

            const optt = this.m_assembly.splitTypes(etype, ntype);
            if (optt.tp.isEmptyType()) {
                return false;
            }
            if (!optt.fp.isEmptyType()) {
                allChecks.push([undefined, createOfTypeCheck(etype, ntype, false)]);
            }

            const fieldkeys = assign.assigns.map((asn) => {
                const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(ntype, asn[0]);
                this.raiseErrorIf(sinfo, tryfinfo === undefined, "Field name is not defined (or is multiply) defined");

                const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
                const ffdecl = finfo.decl;
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, ffdecl.declaredType, finfo.binds);
                return { key: MIRKeyGenerator.generateFieldKey(ftype, asn[0]), ftype: ftype };
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
            this.raiseErrorIf(sinfo, fields.size !== assign.assigns.length, "Mismatch in field counts and assignment");

            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = fieldkeys[i].ftype;
                const step = createNominalStructuredAssignmentPathStep(etype, ttype, fieldkeys[i].key);
                const ok = this.checkSimpleStructuredAssignment(sinfo, env, ttype, assign.assigns[i][1], false, step, allDeclared, allAssigned, allChecks);

                chkok = chkok && ok;
            }

            return chkok;
        }
        else if (assign instanceof TupleStructuredAssignment) {
            let seenopt = false;
            let maxreq = 0;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                if(asgn instanceof IgnoreTermStructuredAssignment && asgn.isOptional) {
                    seenopt = true;
                }
                else {
                    this.raiseErrorIf(sinfo, seenopt, "Cannot have required assign after an optional assign");
                    maxreq = i;
                }
            }
            const ttype = this.m_assembly.restrictTupleBaseOnMatch(etype, assign.isvalue, maxreq, assign.assigns.length);
            
            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                const tuphasidx = this.getInfoForHasIndex(sinfo, ttype, i);
                assert(tuphasidx !== "no", "Should not happen by construction");

                let ok = true;
                if (tuphasidx === "maybe") {
                    const idxtype = this.getInfoForLoadFromSafeIndexOnly(sinfo, ttype, i);
                    const step = createTupleStructuredAssignmentPathStep(ttype, idxtype, i);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, idxtype, asgn, true, step, allDeclared, allAssigned, allChecks);
                }
                else {
                    const idxtype = this.getInfoForLoadFromSafeIndex(sinfo, ttype, i);
                    const step = createTupleStructuredAssignmentPathStep(ttype, idxtype, i);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, idxtype, asgn, false, step, allDeclared, allAssigned, allChecks);
                }

                chkok = chkok && ok;
            }

            if (!etype.isSameType(ttype)) {
                allChecks.push([undefined, createOfTypeCheck(etype, ttype, false)]);
            }

            return chkok;
        }
        else if (assign instanceof RecordStructuredAssignment) {
            let optNames = new Set<string>();
            let reqNames = new Set<string>();
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                if(asgn[1] instanceof IgnoreTermStructuredAssignment && asgn[1].isOptional) {
                    optNames.add(asgn[0]);
                }
                else {
                    reqNames.add(asgn[0]);
                }
            }
            const ttype = this.m_assembly.restrictRecordBaseOnMatch(etype, assign.isvalue, reqNames, optNames);

            let chkok = true;
            for (let i = 0; i < assign.assigns.length; ++i) {
                const asgn = assign.assigns[i];
                const rechasprop = this.getInfoForHasProperty(sinfo, ttype, asgn[0]);
                assert(rechasprop !== "no", "Should be impossible by construction");

                let ok = true;
                if (rechasprop === "maybe") {
                    const ptype = this.getInfoForLoadFromSafePropertyOnly(sinfo, ttype, asgn[0]);
                    const step = createRecordStructuredAssignmentPathStep(ttype, ptype, asgn[0]);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, ptype, assign.assigns[i], true, step, allDeclared, allAssigned, allChecks);
                }
                else {
                    const ptype = this.getInfoForLoadFromSafeProperty(sinfo, ttype, asgn[0]);
                    const step = createRecordStructuredAssignmentPathStep(ttype, ptype, asgn[0]);

                    ok = this.checkSimpleStructuredAssignment(sinfo, env, ptype, assign.assigns[i], false, step, allDeclared, allAssigned, allChecks);
                }

                chkok = chkok && ok;
            }

            if (!etype.isSameType(ttype)) {
                allChecks.push([undefined, createOfTypeCheck(etype, ttype, false)]);
            }

            return chkok;
        }
        else {
            return this.checkSimpleStructuredAssignment(sinfo, env, etype, assign, false, undefined, allDeclared, allAssigned, allChecks);
        }
    }

    private generateRootReg(sinfo: SourceInfo, path: StructuredAssignmentPathStep | undefined, ereg: MIRTempRegister, etype: ResolvedType): [MIRTempRegister, ResolvedType] {
        if (path === undefined) {
                return [ereg, etype];
        }
        else {
            const nreg = this.m_emitter.generateTmpRegister();
            const fromtype = this.m_emitter.registerResolvedTypeReference(path.fromtype);
            const loadtype = this.m_emitter.registerResolvedTypeReference(path.t);

            if (path.step === "tuple") {
                this.m_emitter.emitLoadTupleIndex(sinfo, ereg, fromtype, path.ival, path.fromtype.isUniqueTupleTargetType(), loadtype, nreg);
            }
            else if (path.step === "record") {
                this.m_emitter.emitLoadProperty(sinfo, ereg, fromtype, path.nval, path.fromtype.isUniqueRecordTargetType(), loadtype, nreg);
            }
            else if (path.step === "nominal") {
                this.m_emitter.emitLoadField(sinfo, ereg, fromtype, path.nval, path.fromtype.isUniqueCallTargetType(), loadtype, nreg);
            }
            else {
                this.m_emitter.emitLoadFromEpehmeralList(sinfo, ereg, fromtype, path.ival, loadtype, nreg);
            }

            return [nreg, path.t];
        }
    }

    private generateRootRegOptional(sinfo: SourceInfo, path: StructuredAssignmentPathStep, ereg: MIRTempRegister, etype: ResolvedType): [MIRTempRegister, MIRTempRegister, ResolvedType] {
            const nreg = this.m_emitter.generateTmpRegister();
            const greg = this.m_emitter.generateTmpRegister();
            const fromtype = this.m_emitter.registerResolvedTypeReference(path.fromtype);
            const loadtype = this.m_emitter.registerResolvedTypeReference(path.t);

            if (path.step === "tuple") {
                this.m_emitter.emitLoadTupleIndexTry(sinfo, ereg, fromtype, path.ival, path.fromtype.isUniqueTupleTargetType(), loadtype, nreg, greg);
            }
            else {
                this.m_emitter.emitLoadPropertyTry(sinfo, ereg, fromtype, path.nval, path.fromtype.isUniqueRecordTargetType(), loadtype, nreg, greg);
            }

            return [nreg, greg, path.t];
    }

    private generateMatchTestOps(env: TypeEnvironment, sinfo: SourceInfo, ereg: MIRTempRegister, etype: ResolvedType, matchvname: string | undefined, cvname: string | undefined, allChecks: [StructuredAssignmentPathStep, StructuredAssignmentCheck][], reqassigns: StructuredAssignmentPathStep[], assignregs: MIRTempRegister[], matchok: string, matchfail: string): { oktype: ResolvedType, okenvs: TypeEnvironment[], failenvs: TypeEnvironment[] } {
        //apply the root type of operation if there is one
        const roottc = allChecks.find((vv) => vv[0] === undefined && vv[1].action === "typechk");
        let oktype = etype;
        let okenvs = [env];
        let failenvs = [env];
        if(roottc !== undefined) {
            const roottest = this.m_emitter.generateTmpRegister();
            const nblock = this.m_emitter.createNewBlock("postroottest");

            this.m_emitter.emitTypeOf(sinfo, roottest, this.m_emitter.registerResolvedTypeReference(roottc[1].oftype as ResolvedType), ereg, this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitBoolJump(sinfo, roottest, nblock, matchfail);
            this.m_emitter.setActiveBlock(nblock);

            const splits = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, roottc[1].oftype as ResolvedType, [env]);
            oktype = roottc[1].oftype as ResolvedType;
            okenvs = splits.tenvs;
            failenvs = splits.fenvs;

            if(cvname !== undefined) {
                okenvs = okenvs.map((eev) => eev.setResultExpressionWVarOpt(eev.getExpressionResult().exptype, cvname));
            }

            if(matchvname !== undefined) {
                okenvs = okenvs.map((eev) => eev.setResultExpressionWVarOpt(eev.getExpressionResult().exptype, matchvname));
            }
        }

        if (okenvs.length === 0) {
            return { oktype: oktype, okenvs: [], failenvs: failenvs };
        }
        else {
            let xereg = ereg;
            let xetype = etype;
            if(roottc !== undefined) {
                xetype = roottc[1].oftype as ResolvedType;
                xereg = this.m_emitter.generateTmpRegister();

                this.m_emitter.emitConvertDown(sinfo, this.m_emitter.registerResolvedTypeReference(etype), this.m_emitter.registerResolvedTypeReference(xetype), ereg, xereg);
            }

            //apply every (conditional) type check and equality check
            const elemtc = allChecks.filter((vv) => vv[0] !== undefined);
            let results: MIRTempRegister[] = [];
            for (let i = 0; i < elemtc.length; ++i) {
                const tcc = elemtc[i];
                if (tcc[1].isoptional) {
                    const [treg, greg, ttype] = this.generateRootRegOptional(sinfo, tcc[0], xereg, xetype);

                    const ncr = this.m_emitter.generateTmpRegister();
                    results.push(ncr);
                    this.m_emitter.emitTypeOfGuarded(sinfo, ncr, this.m_emitter.registerResolvedTypeReference(tcc[1].oftype as ResolvedType), treg, this.m_emitter.registerResolvedTypeReference(ttype), greg);
                }
                else {
                    const [treg, ttype] = this.generateRootReg(sinfo, tcc[0], xereg, xetype);

                    const assignpos = reqassigns.findIndex((pth) => pth.ival === tcc[0].ival && pth.nval === tcc[0].nval);
                    if (assignpos !== -1) {
                        assignregs[assignpos] = treg;
                    }

                    const ncr = this.m_emitter.generateTmpRegister();
                    results.push(ncr);

                    if (tcc[1].action === "typechk") {
                        this.m_emitter.emitTypeOf(sinfo, ncr, this.m_emitter.registerResolvedTypeReference(tcc[1].oftype as ResolvedType), treg, this.m_emitter.registerResolvedTypeReference(ttype));
                    }
                    else {
                        let chkreg = this.m_emitter.generateTmpRegister();
                        let chktype = this.m_assembly.getSpecialNoneType();

                        const cev = (tcc[1].eqvalue as ConstantExpressionValue);
                        const cexp = this.m_assembly.compileTimeReduceConstantExpression(cev.exp, env.terms);
                        if (cexp !== undefined) {
                            chktype = this.checkExpression(env, cexp, chkreg, undefined).getExpressionResult().exptype;
                        }
                        else {
                            chktype = this.doConstantExpressionTypeInferNoEmit(env, this.m_file, cev, new Map<string, VarInfo>());

                            const skey = this.m_emitter.registerConstExpr(this.m_file, cev, env.terms, chktype);
                            this.m_emitter.emitInvokeFixedFunction(cev.exp.sinfo, skey, [], undefined, this.m_emitter.registerResolvedTypeReference(chktype), chkreg);
                          }

                        this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(chktype), chkreg, this.m_emitter.registerResolvedTypeReference(ttype), treg, ncr);
                    }
                }
            }

            const allelems = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitAllTrue(sinfo, results, allelems);
            this.m_emitter.emitBoolJump(sinfo, allelems, matchok, matchfail);

            return { oktype: oktype, okenvs: okenvs, failenvs: failenvs };
        }
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const expreg = this.m_emitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, undefined, { refok: true, orok: true });

        let allDeclared: [string, ResolvedType, StructuredAssignmentPathStep, ResolvedType][] = [];
        let allAssigned: [string, StructuredAssignmentPathStep, ResolvedType][] = [];
        let allChecks: [StructuredAssignmentPathStep, StructuredAssignmentCheck][] = [];
        const ok = this.checkStructuredMatch(stmt.sinfo, eenv, eenv.getExpressionResult().exptype, stmt.assign, allDeclared, allAssigned, allChecks);

        this.raiseErrorIf(stmt.sinfo, !ok || allChecks.length !== 0, "Structured assignment may fail");

        let fenv = eenv;
        for (let i = 0; i < allDeclared.length; ++i) {
            const declv = allDeclared[i];
            const etreg = this.generateRootReg(stmt.sinfo, declv[2], expreg, eenv.getExpressionResult().exptype)[0];
            fenv = this.checkDeclareSingleVariable(stmt.sinfo, fenv, declv[0], stmt.isConst, declv[1], { etype: declv[3], etreg: etreg });
        }

        for (let i = 0; i < allAssigned.length; ++i) {
            const assignv = allAssigned[i];

            const etreg = this.generateRootReg(stmt.sinfo, assignv[1], expreg, eenv.getExpressionResult().exptype)[0];
            fenv = this.checkAssignSingleVariable(stmt.sinfo, fenv, assignv[0], assignv[2], etreg );
        }

        return fenv;
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");

        const doneblck = this.m_emitter.createNewBlock("Lifstmt_done");

        let cenv = env;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.conds.length; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
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

    private checkMatchGuard(sinfo: SourceInfo, midx: number, env: TypeEnvironment, matchvar: string, guard: MatchGuard, nextlabel: string, actionlabel: string): { tenvs: TypeEnvironment[], fenvs: TypeEnvironment[] } {
        let opts: { tenvs: TypeEnvironment[], fenvs: TypeEnvironment[] } = { tenvs: [], fenvs: [] };
        let mreg = this.m_emitter.generateTmpRegister();

        const vspecial = new MIRLocalVariable(matchvar);
        const vspecialinfo = env.getLocalVarInfo(matchvar) as VarInfo;
        env = env.setResultExpressionWVarOptNoInfer(vspecialinfo.flowType, matchvar);

        xxxx;
        //need to ensure value is converted to restricted type for each guard check

        let lifetimes: string[] = [];
        if (guard instanceof WildcardMatchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenvs: [env.setResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)], fenvs: [] };
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(tmatch), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType));

            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, tmatch, [env]);
            opts = {
                tenvs: fflows.tenvs.map((eev) => eev.setResultExpressionWVarOpt(this.m_assembly.getSpecialBoolType(), undefined, FlowTypeTruthValue.True)),
                fenvs: fflows.fenvs.map((eev) => eev.setResultExpressionWVarOpt(this.m_assembly.getSpecialBoolType(), undefined, FlowTypeTruthValue.False))
            };
        }
        else {
            const sguard = guard as StructureMatchGuard;

            let allDeclared: [string, ResolvedType, StructuredAssignmentPathStep[], ResolvedType][] = [];
            let allAssigned: [string, StructuredAssignmentPathStep[], ResolvedType][] = [];
            let allChecks: [StructuredAssignmentPathStep[], Expression | ResolvedType][] = [];
            const oftype = this.checkStructuredMatch(sinfo, env, , sguard.match, );

                //{representation: vspecialinfo.declaredType, infered: vspecialinfo.flowType}, allDeclared, allAssigned, allChecks)[0];

            xxxx; //fix this up so we are checking/assigning everything per layer/expansion step 

            const tcreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, tcreg, this.m_emitter.registerResolvedTypeReference(oftype), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType));

            const filllabel = this.m_emitter.createNewBlock(`match${midx}_scfill`);
            if (allChecks.length === 0) {
                this.m_emitter.emitTempRegisterAssign(sinfo, tcreg, mreg);
                this.m_emitter.emitDirectJump(sinfo, filllabel);
            }
            else {
                const eqlabel = this.m_emitter.createNewBlock(`match${midx}_sceq`);
                this.m_emitter.emitBoolJump(sinfo, tcreg, eqlabel, nextlabel);

                this.m_emitter.setActiveBlock(eqlabel);
                this.m_emitter.emitLoadConstBool(sinfo, true, mreg);

                for (let i = 0; i < allChecks.length; ++i) {
                    const nexttestlabel = this.m_emitter.createNewBlock(`match${i}_test`);

                    if (allChecks[i][1] instanceof Expression) {
                        this.generateEqualityOps(env, sinfo, vspecialinfo.declaredType, vspecial, allChecks[i][0], allChecks[i][1] as Expression, mreg);
                    }
                    else {
                        this.generateTypeofOps(sinfo, vspecialinfo.declaredType, vspecial, allChecks[i][0], allChecks[i][1] as ResolvedType, mreg);
                    }

                    this.m_emitter.emitBoolJump(sinfo, mreg, nexttestlabel, nextlabel);
                    this.m_emitter.setActiveBlock(nexttestlabel);
                }

                this.m_emitter.emitDirectJump(sinfo, filllabel);
            }

            this.m_emitter.setActiveBlock(filllabel);
            for (let i = 0; i < allDeclared.length; ++i) {
                const declv = allDeclared[i];

                const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                this.m_emitter.localLifetimeStart(sinfo, declv[1], mirvtype);
                lifetimes.push(declv[1]);

                const treg = this.generateAssignOps(sinfo, vspecial, declv[3]);
                this.m_emitter.emitLocalVarStore(sinfo, treg, declv[1], mirvtype);
            }

            for (let i = 0; i < allAssigned.length; ++i) {
                const assignv = allAssigned[i];

                const treg = this.generateAssignOps(sinfo, vspecial, assignv[1]);
                const assigntype = (env.lookupVar(assignv[0]) as VarInfo).declaredType;
                const convarg = this.emitInlineConvertIfNeeded(sinfo, treg, assignv[2], assigntype);

                if(env.getLocalVarInfo(assignv[0]) === undefined) {
                    this.m_emitter.emitArgVarStore(sinfo, convarg as MIRTempRegister, assignv[0], this.m_emitter.registerResolvedTypeReference(assigntype));
                }
                else {
                    this.m_emitter.emitLocalVarStore(sinfo, convarg as MIRTempRegister, assignv[0], this.m_emitter.registerResolvedTypeReference(assigntype));
                }
            }

            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
            opts = {
                tenvs: fflows.tenvs.map((eev) => eev.multiVarUpdate(allDeclared, allAssigned).setResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)),
                fenvs: fflows.fenvs.map((eev) => eev.setResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))
            }
        }

        if (guard.optionalWhen === undefined) {
            if(lifetimes.length === 0) {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }
            else {
                const endlifeblock = this.m_emitter.createNewBlock(`match${midx}_endlife`);
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, endlifeblock);

                this.m_emitter.setActiveBlock(endlifeblock);
                for(let i = 0; i < lifetimes.length; ++i) {
                    this.m_emitter.localLifetimeEnd(sinfo, lifetimes[i]);
                }

                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }

            return opts;
        }
        else {
            const whenblck = this.m_emitter.createNewBlock(`match${midx}_when`);
            this.m_emitter.emitBoolJump(sinfo, mreg, whenblck, nextlabel);

            this.m_emitter.setActiveBlock(whenblck);

            let wreg = this.m_emitter.generateTmpRegister();
            const wopts = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...opts.tenvs), guard.optionalWhen, wreg, this.m_assembly.getSpecialBoolType());
            this.raiseErrorIf(sinfo, wopts.some((opt) => !opt.getExpressionResult().exptype.isSameType(this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

            if (lifetimes.length === 0) {
                this.m_emitter.emitBoolJump(sinfo, wreg, actionlabel, nextlabel);
            }
            else {
                const endlifeblock = this.m_emitter.createNewBlock(`match${midx}_whenendlife`);
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, endlifeblock);

                this.m_emitter.setActiveBlock(endlifeblock);
                for (let i = 0; i < lifetimes.length; ++i) {
                    this.m_emitter.localLifetimeEnd(sinfo, lifetimes[i]);
                }

                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }

            const wflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, wopts);

            return { tenvs: wflows.tenvs, fenvs: [...opts.fenvs, ...wflows.fenvs] };
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

        xxxx;

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
