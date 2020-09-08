//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { ResolvedType, ResolvedTupleAtomType, ResolvedEntityAtomType, ResolvedTupleAtomTypeEntry, ResolvedRecordAtomType, ResolvedRecordAtomTypeEntry, ResolvedAtomType, ResolvedConceptAtomType, ResolvedFunctionType, ResolvedFunctionTypeParam, ResolvedEphemeralListType, ResolvedConceptAtomTypeEntry } from "../ast/resolved_type";
import { Assembly, NamespaceConstDecl, OOPTypeDecl, StaticMemberDecl, EntityTypeDecl, StaticFunctionDecl, InvokeDecl, MemberFieldDecl, NamespaceFunctionDecl, TemplateTermDecl, OOMemberLookupInfo, MemberMethodDecl, BuildLevel, isBuildLevelEnabled, PreConditionDecl, PostConditionDecl, TypeConditionRestriction, ConceptTypeDecl, SpecialTypeCategory, TemplateTermSpecialRestriction, NamespaceOperatorDecl } from "../ast/assembly";
import { TypeEnvironment, ExpressionReturnResult, VarInfo, FlowTypeTruthValue, StructuredAssignmentPathStep } from "./type_environment";
import { TypeSignature, TemplateTypeSignature, NominalTypeSignature, AutoTypeSignature, FunctionParameter, FunctionTypeSignature, TupleTypeSignature } from "../ast/type_signature";
import { Expression, ExpressionTag, LiteralTypedStringExpression, LiteralTypedStringConstructorExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, NamedArgument, ConstructorPrimaryExpression, ConstructorPrimaryWithFactoryExpression, ConstructorTupleExpression, ConstructorRecordExpression, Arguments, PositionalArgument, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionOrOperatorExpression, PostfixOp, PostfixOpTag, PostfixAccessFromIndex, PostfixProjectFromIndecies, PostfixAccessFromName, PostfixProjectFromNames, PostfixInvoke, PostfixModifyWithIndecies, PostfixModifyWithNames, PrefixOp, BinOpExpression, BinEqExpression, BinCmpExpression, LiteralNoneExpression, BinLogicExpression, NonecheckExpression, CoalesceExpression, SelectExpression, VariableDeclarationStatement, VariableAssignmentStatement, IfElseStatement, Statement, StatementTag, BlockStatement, ReturnStatement, LiteralBoolExpression, LiteralIntegerExpression, LiteralStringExpression, BodyImplementation, AssertStatement, CheckStatement, DebugStatement, StructuredVariableAssignmentStatement, StructuredAssignment, RecordStructuredAssignment, IgnoreTermStructuredAssignment, ConstValueStructuredAssignment, VariableDeclarationStructuredAssignment, VariableAssignmentStructuredAssignment, TupleStructuredAssignment, MatchStatement, MatchGuard, WildcardMatchGuard, TypeMatchGuard, StructureMatchGuard, AbortStatement, YieldStatement, IfExpression, MatchExpression, BlockStatementExpression, ConstructorPCodeExpression, PCodeInvokeExpression, ExpOrExpression, LiteralRegexExpression, ConstructorEphemeralValueList, VariablePackDeclarationStatement, VariablePackAssignmentStatement, NominalStructuredAssignment, ValueListStructuredAssignment, NakedCallStatement, ValidateStatement, IfElse, CondBranchEntry, LiteralBigIntegerExpression, LiteralFloatExpression, MapEntryConstructorExpression, SpecialConstructorExpression, LiteralNaturalExpression, LiteralBigNaturalExpression, LiteralRationalExpression, LiteralDecimalExpression } from "../ast/body";
import { PCode, MIREmitter, MIRKeyGenerator, MIRBodyEmitter, ResultCheckCategory } from "../compiler/mir_emitter";
import { MIRTempRegister, MIRArgument, MIRConstantNone, MIRBody, MIRVirtualMethodKey, MIRNominalTypeKey, MIRConstantKey, MIRInvokeKey, MIRResolvedTypeKey, MIRFieldKey, MIRConstantEmpty, MIRConstantFalse, MIRConstantTrue, MIRConstantInt, MIRConstantBigInt, MIRConstantFloat, MIRConstantString, MIRConstantRegex, MIRLocalVariable, MIRParameterVariable, MIRVariableArgument } from "../compiler/mir_ops";
import { SourceInfo, unescapeLiteralString } from "../ast/parser";
import { MIREntityTypeDecl, MIRConceptTypeDecl, MIRFieldDecl, MIRInvokeDecl, MIRFunctionParameter, MIRType, MIROOTypeDecl, MIRConstantDecl, MIRPCode, MIRInvokePrimitiveDecl, MIRInvokeBodyDecl, MIREntityType, MIRRegex, MIREphemeralListType } from "../compiler/mir_assembly";
import * as assert from "assert";
import { BSQRegex } from "../ast/bsqregex";
import { RefRepr } from "../tooling/aot/type_repr";

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
    ref: string | undefined,
    pcode: PCode | undefined,
    treg: MIRTempRegister
};

type FilledLocation = {
    vtype: ResolvedType | ResolvedFunctionType,
    mustDef: boolean,
    ref: string | undefined,
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

    private checkedUnion(sinfo: SourceInfo, types: ResolvedType[]) {
        const tj = this.m_assembly.typeUpperBound(types);
        this.raiseErrorIf(sinfo, types.length !== 0 && tj.isEmptyType(), "Ephemeral list types must be unique");

        return tj;
    }

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "stringof" | "datastring" | "time" | "operator" {
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
            return "stringof";
        }

        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl))) {
            return "datastring";
        }

        return "operator";
    }
    
    private checkValueLess(lhs: ResolvedType, rhs: ResolvedType): "stringof" | "datastring" | "time" | "operator" {
        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.StringOfDecl))) {
            return "stringof";
        }

        if((lhs.isUniqueCallTargetType() && lhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl)) && (rhs.isUniqueCallTargetType() && rhs.getUniqueCallTargetType().object.specialDecls.has(SpecialTypeCategory.DataStringDecl))) {
            return "datastring";
        }
        
        return "operator";
    }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    private getInfoForLoadFromIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        const options = rtype.options.map((atom) => {
            this.raiseErrorIf(sinfo, !(atom instanceof ResolvedTupleAtomType), "Can only load indecies from Tuples");
            const tatom = atom as ResolvedTupleAtomType;
            if (idx < tatom.types.length) {
                if (!tatom.types[idx].isOptional) {
                    return tatom.types[idx].type;
                }
                else {
                    return this.m_assembly.typeUpperBound([tatom.types[idx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUpperBound(options.filter((opt) => !opt.isEmptyType()));
    }

    private getInfoForLoadFromPropertyName(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        const options = rtype.options.map((atom) => {
            this.raiseErrorIf(sinfo, !(atom instanceof ResolvedRecordAtomType), "Can only load properties from Records");
            const ratom = atom as ResolvedRecordAtomType;
            const tidx = ratom.entries.findIndex((re) => re.name === pname);
            if (tidx !== -1) {
                if (!ratom.entries[tidx].isOptional) {
                    return ratom.entries[tidx].type;
                }
                else {
                    return this.m_assembly.typeUpperBound([ratom.entries[tidx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });

        return this.m_assembly.typeUpperBound(options);
    }

    private updateTupleIndeciesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [number, ResolvedType][]): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedTupleAtomType), "Cannot only update indecies on Tuples");
        const tuple = t as ResolvedTupleAtomType;

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            this.raiseErrorIf(sinfo, update[0] < 0, "Update index is out of tuple bounds");

            if (update[0] > tentries.length) {
                const extendCount = (update[0] - tentries.length) + 1;
                for (let j = 0; j < extendCount; ++j) {
                    if (tentries.length + j < tuple.types.length) {
                        if (!tuple.types[i].isOptional) {
                            tentries.push(new ResolvedTupleAtomTypeEntry(tuple.types[j].type, false));
                        }
                        else {
                            tentries.push(new ResolvedTupleAtomTypeEntry(this.m_assembly.typeUpperBound([tuple.types[j].type, this.m_assembly.getSpecialNoneType()]), false));
                        }
                    }
                    else {
                        tentries.push(new ResolvedTupleAtomTypeEntry(this.m_assembly.getSpecialNoneType(), false));
                    }
                }
            }
            tentries[update[0]] = new ResolvedTupleAtomTypeEntry(update[1], false);
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tentries));
    }

    private updateNamedPropertiesAtom(sinfo: SourceInfo, t: ResolvedAtomType, updates: [string, ResolvedType][]): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedRecordAtomType), "Cannot update on 'Record' type");
        const record = t as ResolvedRecordAtomType;

        let rentries: ResolvedRecordAtomTypeEntry[] = [...record.entries];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            const idx = rentries.findIndex((e) => e.name === update[0]);
            rentries[idx !== -1 ? idx : rentries.length] = new ResolvedRecordAtomTypeEntry(update[0], update[1], false);
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(rentries));
    }

    private appendIntoTupleAtom(sinfo: SourceInfo, t: ResolvedTupleAtomType, merge: ResolvedAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedTupleAtomType), "Cannot append on 'Tuple' type");
        const tuple = merge as ResolvedTupleAtomType;

        let tentries: ResolvedTupleAtomTypeEntry[] = [];
        if (t.types.some((entry) => entry.isOptional)) {
            this.raiseError(sinfo, "Appending to tuple with optional entries creates ambigious result tuple");
        }
        else {
            //just copy everything along
            tentries = [...t.types, ...tuple.types];
        }

        return ResolvedType.createSingle(ResolvedTupleAtomType.create(tentries));
    }

    private mergeIntoRecordAtom(sinfo: SourceInfo, t: ResolvedRecordAtomType, merge: ResolvedAtomType): ResolvedType {
        this.raiseErrorIf(sinfo, !(t instanceof ResolvedRecordAtomType), "Cannot merge with 'Record' type");
        const record = merge as ResolvedRecordAtomType;

        let rentries: ResolvedRecordAtomTypeEntry[] = [...t.entries];
        for (let i = 0; i < record.entries.length; ++i) {
            const update = record.entries[i];
            const fidx = rentries.findIndex((e) => e.name === update.name);
            const idx = fidx !== -1 ? fidx : rentries.length;

            if (!update.isOptional) {
                rentries[idx] = new ResolvedRecordAtomTypeEntry(update.name, update.type, false);
            }
            else {
                if (idx === rentries.length) {
                    rentries[idx] = update;
                }
                else {
                    rentries[idx] = new ResolvedRecordAtomTypeEntry(update.name, this.m_assembly.typeUpperBound([update.type, rentries[idx].type]), true);
                }
            }
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(rentries));
    }

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
                eargs.push({ name: "this", argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: optSelfValue[2] });
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

                        eargs[i] = { name: narg.name, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg };
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

                        eargs[i] = { name: undefined, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg };
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
                const sigidx = ridx + i;

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

                        if (arg instanceof NamedArgument) {
                            eargs.push({ name: arg.name, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg });
                        }
                        else {
                            eargs.push({ name: undefined, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg });
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

                    if (arg instanceof NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg.declaredType, ref: rvname, expando: false, pcode: undefined, treg: treg });
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

        return rrecord;
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

        return rvl;
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

        return resulttype;
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

        let filledLocations: { vtype: ResolvedType, mustDef: boolean, trgt: MIRArgument }[] = [];

        //figure out named parameter mapping first
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");

            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);

                filledLocations[fidx] = { vtype: arg.argtype as ResolvedType, mustDef: true, trgt: arg.treg };
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
                    const lvtype =  this.getInfoForLoadFromPropertyName(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if (flatfinfo[fidx][1][1].value === undefined) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                    }
                    else {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
                    }

                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[0].has(pname), trgt: etreg };
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
                filledLocations[ii] = { vtype: arg.argtype as ResolvedType, mustDef: true, trgt: arg.treg };
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
                    const lvtype = this.getInfoForLoadFromIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if (flatfinfo[ii][1][1].value === undefined) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                    }
                    else {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
                    }

                    filledLocations[ii] = { vtype: lvtype, mustDef: ectr < expandInfo[0], trgt: etreg };

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

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        let cargs: MIRArgument[] = [];
        for (let i = 0; i < fields.length; ++i) {
            const field = (fieldInfo.get(fields[i]) as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]);
            const fieldtype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);

            if (filledLocations[i] === undefined) {
                this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[i]}" is required and must be assigned a value in constructor`);

                const etreg = this.m_emitter.generateTmpRegister();
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);
                this.m_emitter.emitBlankValue(sinfo, this.m_emitter.registerResolvedTypeReference(ftype), etreg);

                filledLocations[i] = { vtype: fieldtype, mustDef: true, trgt: etreg };
            }

            cargs.push(this.emitInlineConvertIfNeeded(sinfo, filledLocations[i].trgt, filledLocations[i].vtype, fieldtype));
        }

        const constype = ResolvedType.createSingle(oftype);
        const rtype = this.m_emitter.registerResolvedTypeReference(constype);
        const [restype, iipack] = this.genInferInfo(sinfo, constype, infertype, trgt);

        const ikey = MIRKeyGenerator.generateStaticKey(oftype.object, "@@constructor", oftype.binds, []);
        this.m_emitter.emitInvokeFixedFunction(sinfo, ikey, cargs, fflag, rtype, iipack[0]);

        this.emitConvertIfNeeded(sinfo, constype, infertype, iipack);
        return restype;
    }

    private checkArgumentsSignature(sinfo: SourceInfo, env: TypeEnvironment, name: string, sig: ResolvedFunctionType, args: ExpandedArgument[]): { args: MIRArgument[], types: ResolvedType[], fflag: string, refs: string[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
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

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
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
                    const lvtype =  this.getInfoForLoadFromPropertyName(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    if (!sig.params[fidx].isOptional) {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                    }
                    else {
                        this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg, fflag, fidx - optfirst);
                    }

                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[0].has(pname), ref: undefined, pcode: undefined, trgt: etreg };
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
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
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
                    const lvtype = this.getInfoForLoadFromIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    if (!sig.params[ii].isOptional) {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                    }
                    else {
                        this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg, fflag, ii - optfirst);
                    }

                    filledLocations[ii] = { vtype: lvtype, mustDef: ectr < expandInfo[0], ref: undefined, pcode: undefined, trgt: etreg };

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

        while (filledLocations[ii] !== undefined) {
            this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
            ii++;
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
        let refs: string[] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;

            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                const etreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBlankValue(sinfo, this.m_emitter.registerResolvedTypeReference(paramtype as ResolvedType), etreg);

                filledLocations[j] = { vtype: paramtype, mustDef: true, ref: undefined, pcode: undefined, trgt: etreg };
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

                    refs.push(filledLocations[j].ref as string);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype as ResolvedType, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                }

                const narg = this.emitInlineConvertIfNeeded(sinfo, filledLocations[j].trgt, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType);
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

    private checkArgumentsWOperator(sinfo: SourceInfo, env: TypeEnvironment, opnames: string[], args: ExpandedArgument[]): { args: MIRArgument[], types: ResolvedType[], fflag: string, refs: string[], pcodes: PCode[], cinfo: [string, ResolvedType][] } {
        let filledLocations: FilledLocation[] = [];

        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = opnames.findIndex((name) => name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);

                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
            }
            else if (arg.expando && (arg.argtype as ResolvedType).isRecordTargetType()) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, expandInfo[0].size !== expandInfo[1].size, "Cannot have optional arguments on operator");

                expandInfo[1].forEach((pname) => {
                    const fidx = opnames.findIndex((name) => name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Operator does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype =  this.getInfoForLoadFromPropertyName(sinfo, arg.argtype as ResolvedType, pname);
                    const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);

                    this.m_emitter.emitLoadProperty(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), pname, !(arg.argtype as ResolvedType).isUniqueRecordTargetType(), ptype, etreg);
                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[0].has(pname), ref: undefined, pcode: undefined, trgt: etreg };
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
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !(arg.argtype as ResolvedType).isTupleTargetType(), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype as ResolvedType);
                this.raiseErrorIf(sinfo, expandInfo[0] !== expandInfo[1], "Cannot have optional arguments on operator");

                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= opnames.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    
                    const etreg = this.m_emitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromIndex(sinfo, arg.argtype as ResolvedType, ectr);
                    const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                   
                    this.m_emitter.emitLoadTupleIndex(sinfo, arg.treg, this.m_emitter.registerResolvedTypeReference(arg.argtype as ResolvedType), ectr, !(arg.argtype as ResolvedType).isUniqueTupleTargetType(), itype, etreg);
                    filledLocations[ii] = { vtype: lvtype, mustDef: ectr < expandInfo[0], ref: undefined, pcode: undefined, trgt: etreg };

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

        if (ii < opnames.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${opnames[ii]}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }

        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs: MIRArgument[] = [];
        let mtypes: ResolvedType[] = [];
        let pcodes: PCode[] = [];
        let refs: string[] = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;

            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);

                const etreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBlankValue(sinfo, this.m_emitter.registerResolvedTypeReference(paramtype as ResolvedType), etreg);

                filledLocations[j] = { vtype: paramtype, mustDef: true, ref: undefined, pcode: undefined, trgt: etreg };
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

                    refs.push(filledLocations[j].ref as string);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype as ResolvedType, paramtype as ResolvedType), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                }

                const narg = this.emitInlineConvertIfNeeded(sinfo, filledLocations[j].trgt, filledLocations[j].vtype as ResolvedType, sig.params[j].type as ResolvedType);
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

    private generateRefInfoForCallEmit(fsig: ResolvedFunctionType, refs: string[]): [MIRType, MIRType, number, [string, MIRType][]] {
        const rtype = this.m_emitter.registerResolvedTypeReference(fsig.resultType); 
        const refinfo = refs.map((rn) => {
            const rp = fsig.params.find((p) => p.name === rn);
            const ptk = this.m_emitter.registerResolvedTypeReference((rp as ResolvedFunctionTypeParam).type as ResolvedType);
            return [rn, ptk] as [string, MIRType];
        });

        if (refinfo.length === 0) {
            return [rtype, rtype, -1, refinfo];
        }
        else {
            const rr = refs.map((rn) => (fsig.params.find((p) => p.name === rn) as ResolvedFunctionTypeParam).type as ResolvedType);

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
        const ctype = this.getResultBinds(aoftype.parsetype).T;

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
        this.m_emitter.emitAccessConstant(exp.sinfo, gkey, iipack[0]);
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
        this.m_emitter.emitAccessConstant(exp.sinfo, skey, iipack[0]);
        this.emitConvertIfNeeded(exp.sinfo, rtype, infertype, iipack);

        return [env.setResultExpression(restype)];
    }

    private checkAccessVariable(env: TypeEnvironment, exp: AccessVariableExpression, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");

        if (infertype === undefined || this.m_assembly.subtypeOf(vinfo.flowType, infertype)) {
            const totype = infertype || vinfo.flowType;
            const tmp = this.m_emitter.generateTmpRegister();

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

            return [env.setResultExpression(totype, vinfo.truthval)];
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

            return [env.setResultExpression(infertype, vinfo.truthval)];
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
            const okbinds = new Map<string, ResolvedType>().set("T", T || okenv.getExpressionResult().exptype).set("E", E || this.m_assembly.getSpecialNoneType());
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

    private checkCallNamespaceFunctionOrOperatorExpression(env: TypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression, trgt: MIRTempRegister, refok: boolean, infertype: ResolvedType | undefined): TypeEnvironment[] {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if (nsdecl.functions.has(exp.name)) {
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
        else {
            this.raiseErrorIf(exp.sinfo, !nsdecl.operators.has(exp.name), `Operator named '${exp.name}' is not defined`);
            const opdecl = nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[];

            //No terms to be bound on operator call


            //
            //TODO: if we want to do template inference this is a key point -- see the assertion in check args to figure out how to pre-check the body and get a result type
            //
            this.raiseErrorIf(exp.sinfo, fdecl.invoke.terms.length !== exp.terms.targs.length, "Missing template arguments that cannot be inferred");

            const binds = this.m_assembly.resolveBindsForCall(fdecl.invoke.terms, exp.terms.targs, new Map<string, ResolvedType>(), env.terms);
            this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

            this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, binds as Map<string, ResolvedType>, fdecl.invoke.termRestrictions);

            const fsig = this.m_assembly.normalizeTypeFunction(fdecl.invoke.generateSig(), binds as Map<string, ResolvedType>);
            this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");

            const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, exp.args, undefined, refok);
            const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig as ResolvedFunctionType, eargs);

            this.checkRecursion(exp.sinfo, fsig as ResolvedFunctionType, margs.pcodes, exp.pragmas.recursive);

            if (this.m_emitEnabled) {
                const ckey = this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(exp.sinfo, ckey, margs.args, refinfo, trgt);
            }

            return [env.setExpressionResult(this.resolveAndEnsureTypeOnly(exp.sinfo, fdecl.invoke.resultType, binds as Map<string, ResolvedType>))];
        }
    }

    private checkCallStaticFunctionExpression(env: TypeEnvironment, exp: CallStaticFunctionExpression, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);

        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "static", exp.name);
        this.raiseErrorIf(exp.sinfo, fdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);
        const fdecl = fdecltry as OOMemberLookupInfo;

        //
        //TODO: if we want to do template inference this is a key point -- see the assertion in check args to figure out how to pre-check the body and get a result type
        //
        this.raiseErrorIf(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.terms.length !== exp.terms.targs.length, "Missing template arguments that cannot be inferred");

        const binds = this.m_assembly.resolveBindsForCall((fdecl.decl as StaticFunctionDecl).invoke.terms, exp.terms.targs, fdecl.binds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");

        this.checkTemplateTypes(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.terms, binds as Map<string, ResolvedType>, (fdecl.decl as StaticFunctionDecl).invoke.termRestrictions);

        const fsig = this.m_assembly.normalizeTypeFunction((fdecl.decl as StaticFunctionDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");

        const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, exp.args, undefined, refok);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig as ResolvedFunctionType, eargs);

        this.checkRecursion(exp.sinfo, fsig as ResolvedFunctionType, margs.pcodes, exp.pragmas.recursive);

        const iskeyop = fdecl.contiainingType.ns === "NSCore" && fdecl.contiainingType.name === "KeyType";

        if (this.m_emitEnabled) {
            if (iskeyop && exp.name === "equal") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);

                const isstrictlhs = mirargtypeinferlhs.options.length === 1 && mirargtypeinferlhs.options[0] instanceof MIREntityType;
                const isstrictrhs = mirargtypeinferrhs.options.length === 1 && mirargtypeinferrhs.options[0] instanceof MIREntityType;
                const isstrict = isstrictlhs && isstrictrhs && mirargtypeinferlhs.trkey === mirargtypeinferrhs.trkey;

                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], "==", mirargtypeinferrhs.trkey, margs.args[1], trgt, !isstrict);
            }
            else if(iskeyop && exp.name === "less") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);

                const isstrictlhs = mirargtypeinferlhs.options.length === 1 && mirargtypeinferlhs.options[0] instanceof MIREntityType;
                const isstrictrhs = mirargtypeinferrhs.options.length === 1 && mirargtypeinferrhs.options[0] instanceof MIREntityType;
                const isstrict = isstrictlhs && isstrictrhs && mirargtypeinferlhs.trkey === mirargtypeinferrhs.trkey;

                this.m_emitter.bodyEmitter.emitBinLess(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], "==", mirargtypeinferrhs.trkey, margs.args[1], trgt, !isstrict);
            }
            else {
                this.m_emitter.registerResolvedTypeReference(baseType);
                this.m_emitter.registerTypeInstantiation(fdecl.contiainingType, fdecl.binds);
                const skey = this.m_emitter.registerStaticCall(fdecl.contiainingType, fdecl.binds, fdecl.decl as StaticFunctionDecl, (fdecl.decl as StaticFunctionDecl).name, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(exp.sinfo, skey, margs.args, refinfo, trgt);
            }
        }

        if (iskeyop && (exp.name === "equal" || exp.name === "less")) {
            return [env.setExpressionResult(this.m_assembly.getSpecialBoolType())];
        }
        else {
            return [env.setExpressionResult(this.resolveAndEnsureTypeOnly(exp.sinfo, (fdecl.decl as StaticFunctionDecl).invoke.resultType, binds as Map<string, ResolvedType>))];
        }
    }

    private checkPCodeInvokeExpression(env: TypeEnvironment, exp: PCodeInvokeExpression, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = (pco as { pcode: PCode, captured: string[] }).pcode;
        const captured = (pco as { pcode: PCode, captured: string[] }).captured;

        const cargs = [...exp.args.argList, ...captured.map((cv) => new PositionalArgument(false, false, new AccessVariableExpression(exp.sinfo, cv)))];
        const eargs = this.checkArgumentsEvaluationWSig(env, pcode.ftype, new Arguments(cargs), undefined, refok);

        //A little strange since we don't expand captured args on the signature yet and don't expand/rest/etc -- slice them off for the checking
        const margs = this.checkArgumentsSignature(exp.sinfo, env, pcode.ftype, eargs.slice(0, exp.args.argList.length));
        const cargsext = eargs.slice(exp.args.argList.length).map((ea) => ea.treg);

        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.pragmas.recursive);

        if (this.m_emitEnabled) {
            const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(exp.sinfo, MIRKeyGenerator.generatePCodeKey((pcode as PCode).code), [...margs.args, ...cargsext], refinfo, trgt);
        }

        return [env.setExpressionResult((pcode as PCode).ftype.resultType)];
    }

    private checkAccessFromIndex(env: TypeEnvironment, op: PostfixAccessFromIndex, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");

        const mirargtype = this.m_emitter.registerResolvedTypeReference(texp);

        if (op.kind === "basic") {
            const idxtype = this.getInfoForLoadFromIndex(op.sinfo, texp, "none", op.index);
            const mirloadtype = this.m_emitter.registerResolvedTypeReference(idxtype);
            if (infertype === undefined || infertype.isSameType(idxtype)) {
                this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, mirargtype.trkey, op.index, !texp.isUniqueTupleTargetType(), mirloadtype.trkey, trgt);

                return [env.setResultExpression(idxtype)];
            }
            else {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, mirargtype.trkey, op.index, !texp.isUniqueTupleTargetType(), mirloadtype.trkey, creg);
                this.emitAssignToTempAndConvertIfNeeded(op.sinfo, idxtype, infertype, creg, trgt);

                return [env.setResultExpression(infertype)];
            }
        }
        else if(op.kind === "option") {
            xxxx;
        }
        else {
            xxxx;
        }
    }

    private checkProjectFromIndecies(env: TypeEnvironment, op: PostfixProjectFromIndecies, arg: MIRTempRegister, trgt: MIRTempRegister, infertype: ResolvedType | undefined): TypeEnvironment[] {
        const texp = env.getExpressionResult().exptype;

        this.raiseErrorIf(op.sinfo, !texp.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx.index < 0), "Index cannot be negative");

        if(op.isEphemeralListResult) {
            let itype: ResolvedEphemeralListType | undefined = undefined;
            if (infertype !== undefined) {
                itype = infertype.tryGetInferrableValueListConstructorType();
                this.raiseErrorIf(op.sinfo, itype !== undefined && itype.types.length !== op.indecies.length, "Mismatch between number of indecies loaded and number expected by inferred type");
            }

            let ctypes: ResolvedType[] = [];
            for (let i = 0; i < op.indecies.length; ++i) {
                const reqtype = op.indecies[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.indecies[i].reqtype as TypeSignature, env.terms) : undefined;
                let inferidx: ResolvedType | undefined = undefined
                if (reqtype !== undefined || itype !== undefined) {
                    inferidx = reqtype !== undefined ? reqtype : (itype as ResolvedEphemeralListType).types[op.indecies[i].index];
                }

                const ttype = this.getInfoForLoadFromIndex(op.sinfo, texp, op.indecies[i].index);
                this.raiseErrorIf(op.sinfo, inferidx === undefined || !this.m_assembly.subtypeOf(ttype, inferidx), `Type incompatibility in projecting index ${i}`);
                ctypes.push(inferidx || ttype);
            }

            const rephemeralatom = ResolvedEphemeralListType.create(ctypes);
            const rephemeral = ResolvedType.createSingle(rephemeralatom);
            this.raiseErrorIf(op.sinfo, infertype !== undefined && !infertype.isSameType(rephemeral), "Cannot create EphemeralList of needed type");

            const rindecies = op.indecies.map((idv) => idv.index);

            if (texp.isUniqueTupleTargetType()) {
                const invk = this.m_emitter.registerTupleProjectToEphemeral(texp.getUniqueTupleTargetType(), rindecies, rephemeralatom);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg], [rephemeral, rephemeral, -1, []], trgt);
            }
            else {
                const invk = this.m_emitter.registerTupleProjectToEphemeralVirtual(texp, rindecies, rephemeralatom);
                this.m_emitter.emitInvokeVirtualTarget(op.sinfo, invk, this.m_emitter.registerResolvedTypeReference(texp).trkey, [arg], [rephemeral, rephemeral, -1, []], trgt);
            }

            return [env.setResultExpression(rephemeral)];
        }
        else {
            let itype: ResolvedTupleAtomType | undefined = undefined;
            if (infertype !== undefined) {
                itype = infertype.tryGetInferrableTupleConstructorType(op.isValue);
            }

            const resultOptions = texp.options.map((opt) => {
                let ctypes: ResolvedTupleAtomTypeEntry[] = [];
                for (let i = 0; i < op.indecies.length; ++i) {
                    const reqtype = op.indecies[i].reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.indecies[i].reqtype as TypeSignature, env.terms) : undefined;
                    let inferidx: ResolvedType | undefined = undefined
                    if (reqtype !== undefined || itype !== undefined) {
                        inferidx = reqtype !== undefined ? reqtype : this.getInfoForLoadFromIndex(op.sinfo, ResolvedType.createSingle(itype as ResolvedTupleAtomType), op.indecies[i].index);
                    }

                    const ttype = this.getInfoForLoadFromIndex(op.sinfo, ResolvedType.createSingle(opt), op.indecies[i].index);
                    this.raiseErrorIf(op.sinfo, inferidx === undefined || !this.m_assembly.subtypeOf(ttype, inferidx), `Type incompatibility in projecting index ${i}`);
                    ctypes.push(new ResolvedTupleAtomTypeEntry(inferidx || ttype, false));
                }

                return ResolvedType.createSingle(ResolvedTupleAtomType.create(op.isValue, ctypes));
            });

            const ubtype = this.m_assembly.typeUpperBound(resultOptions);
            this.raiseErrorIf(op.sinfo, infertype !== undefined && !this.m_assembly.subtypeOf(ubtype, infertype), "Cannot create Tuple of needed type");

            const rtupletype = ResolvedType.create((infertype || ubtype).options.filter((tt) => tt instanceof ResolvedTupleAtomType));

            const rindecies = op.indecies.map((idv) => {
                return {
                    index: idv.index,
                    reqtype: idv.reqtype !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, idv.reqtype as TypeSignature, env.terms) : this.getInfoForLoadFromIndex(op.sinfo, ResolvedType.createSingle(itype as ResolvedTupleAtomType), idv.index)
                };
            });

            let ttreg = rtupletype.isSameType(infertype || ubtype) ? trgt : this.m_emitter.generateTmpRegister();

            if (texp.isUniqueTupleTargetType()) {
                const invk = this.m_emitter.registerTupleProjectToTuple(texp.getUniqueTupleTargetType(), rindecies, rtupletype);
                this.m_emitter.emitInvokeFixedFunction(op.sinfo, invk, [arg], [rtupletype, rtupletype, -1, []], ttreg);
            }
            else {
                const invk = this.m_emitter.registerTupleProjectToTupleVirtual(texp, rindecies, rtupletype);  
                this.m_emitter.emitInvokeVirtualTarget(op.sinfo, invk, this.m_emitter.registerResolvedTypeReference(texp).trkey, [arg], [rtupletype, rtupletype, -1, []], ttreg);
            }

            if(!rtupletype.isSameType(infertype || ubtype)) {
                this.emitAssignToTempAndConvertIfNeeded(op.sinfo, rtupletype, infertype || ubtype, ttreg, trgt);
            }

            return [env.setResultExpression(rtupletype)];
        }
    }

    private checkAccessFromName(env: TypeEnvironment, op: PostfixAccessFromName, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const rtype = this.getInfoForLoadFromPropertyName(op.sinfo, texp, op.name);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadProperty(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, op.name, trgt);
            }

            return [env.setExpressionResult(rtype)];
        }
        else {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", op.name);
            this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

            const topts = (finfo.decls as OOMemberLookupInfo[]).map((info) => this.resolveAndEnsureTypeOnly(op.sinfo, (info.decl as MemberFieldDecl).declaredType, info.binds));
            const rtype = this.m_assembly.typeUpperBound(topts);

            if (this.m_emitEnabled) {
                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const fkey = MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, op.name);
                this.m_emitter.bodyEmitter.emitLoadField(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, fkey, trgt);
            }

            return [env.setExpressionResult(rtype)];
        }
    }

    private checkProjectFromNames(env: TypeEnvironment, op: PostfixProjectFromNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => {
                let ttypes = op.names.map((name) => new ResolvedRecordAtomTypeEntry(name, this.getInfoForLoadFromPropertyName(op.sinfo, ResolvedType.createSingle(opt), name), false));

                return ResolvedType.createSingle(ResolvedRecordAtomType.create(ttypes));
            });
            const restype = this.m_assembly.typeUpperBound(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, op.names, trgt);
            }

            return [env.setExpressionResult(restype)];
        }
        else {
            const fieldkeys = op.names.map((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", f);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                return MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, f);
            });

            if(op.isEphemeralListResult) {
                const resultOptions = texp.options.map((atom) => {
                    const oentries = op.names.map((f) => {
                        const finfo = this.m_assembly.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), "field", f) as OOMemberLookupInfo;
                        const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                        return ftype;
                    });

                    return ResolvedType.createSingle(ResolvedEphemeralListType.create(oentries));
                });
                const restype = this.checkedUnion(op.sinfo, resultOptions);

                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitProjectFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, fieldkeys, trgt);
                }

                return [env.setExpressionResult(restype)];
            }
            else {
                const resultOptions = texp.options.map((atom) => {
                    const oentries = op.names.map((f) => {
                        const finfo = this.m_assembly.tryGetOOMemberDeclUnique(ResolvedType.createSingle(atom), "field", f) as OOMemberLookupInfo;
                        const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, (finfo.decl as MemberFieldDecl).declaredType, finfo.binds);
                        return new ResolvedRecordAtomTypeEntry(f, ftype, false);
                    });

                    return ResolvedType.createSingle(ResolvedRecordAtomType.create(oentries));
                });
                const restype = this.m_assembly.typeUpperBound(resultOptions);

                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitProjectFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, fieldkeys, trgt);
                }

                return [env.setExpressionResult(restype)];
            }
        }
    }

    private checkProjectFromType(env: TypeEnvironment, op: PostfixProjectFromType, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        let resultOptions: ResolvedType[] = [];
        let mayfail = false;
        const opType = this.resolveAndEnsureTypeOnly(op.sinfo, op.ptype, env.terms);
        this.raiseErrorIf(op.sinfo, opType.options.length !== 1, "Invalid type");

        const ptype = opType.options[0];
        if (ptype instanceof ResolvedTupleAtomType) {
            if(!this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType())) {
                if(op.istry) {
                    return [env.setExpressionResult(this.m_assembly.getSpecialNoneType())];
                }
                else {
                    this.raiseError(op.sinfo, "This projection will always fail");
                }
            }

            resultOptions = texp.options.map((opt) => this.projectTupleAtom(op.sinfo, opt, ptype, op.istry));
            mayfail = resultOptions.some((ropt) => ropt.isEmptyType());

            resultOptions = resultOptions.filter((ropt) => !ropt.isEmptyType());
            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUpperBound(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeTuple(op.sinfo, resultType.trkey, arg, op.istry, this.m_emitter.registerResolvedTypeReference(texp).trkey, ttype.trkey, trgt);
            }
        }
        else if (ptype instanceof ResolvedRecordAtomType) {
            if(!this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
                if(op.istry) {
                    return [env.setExpressionResult(this.m_assembly.getSpecialNoneType())];
                }
                else {
                    this.raiseError(op.sinfo, "This projection will always fail");
                }
            }

            resultOptions = texp.options.map((opt) => this.projectRecordAtom(op.sinfo, opt, ptype, op.istry));
            mayfail = resultOptions.some((ropt) => ropt.isEmptyType());

            resultOptions = resultOptions.filter((ropt) => !ropt.isEmptyType());
            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUpperBound(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeRecord(op.sinfo, resultType.trkey, arg, op.istry, this.m_emitter.registerResolvedTypeReference(texp).trkey, ttype.trkey, trgt);
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, !(ptype instanceof ResolvedConceptAtomType) && !(ptype instanceof ResolvedEntityAtomType), "Can only project on Tuple, Record, Object, or Concept types");

            if(!this.m_assembly.subtypeOf(texp, opType)) {
                if(op.istry) {
                    return [env.setExpressionResult(this.m_assembly.getSpecialNoneType())];
                }
                else {
                    this.raiseError(op.sinfo, "This projection will always fail");
                }
            }

            const res = this.projectOOTypeAtom(op.sinfo, texp, ptype as (ResolvedEntityAtomType | ResolvedConceptAtomType), op.istry);
            resultOptions = [res[0]];
            mayfail = resultOptions.some((ropt) => ropt.isEmptyType());

            resultOptions = resultOptions.filter((ropt) => !ropt.isEmptyType());
            if (this.m_emitEnabled) {
                this.m_emitter.registerResolvedTypeReference(opType);
                if(ptype instanceof ResolvedEntityAtomType) {
                    this.m_emitter.registerTypeInstantiation((ptype as ResolvedEntityAtomType).object, (ptype as ResolvedEntityAtomType).binds);
                }
                else {
                    (ptype as ResolvedConceptAtomType).conceptTypes.map((ctype) => this.m_emitter.registerTypeInstantiation(ctype.concept, ctype.binds));
                }

                const cfields = res[1].map((ff) => MIRKeyGenerator.generateFieldKey(ff.contiainingType, ff.binds, (ff.decl as MemberFieldDecl).name));
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUpperBound(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeNominal(op.sinfo, resultType.trkey, arg, op.istry, this.m_emitter.registerResolvedTypeReference(texp).trkey, this.m_emitter.registerResolvedTypeReference(opType).trkey, cfields, trgt);
            }
        }

        this.raiseErrorIf(op.sinfo, !op.istry && mayfail, "Project may fail but not using 'tryProject'");
        return [env.setExpressionResult(this.m_assembly.typeUpperBound(mayfail ? [...resultOptions, this.m_assembly.getSpecialNoneType()] : resultOptions))];
    }

    private checkModifyWithIndecies(env: TypeEnvironment, op: PostfixModifyWithIndecies, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));

        const updates = op.updates.map<[number, ResolvedType, MIRTempRegister]>((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });

        const resultOptions = texp.options.map((opt) => this.updateTupleIndeciesAtom(op.sinfo, opt, updates.map<[number, ResolvedType]>((update) => [update[0], update[1]])));
        const rtuple = this.m_assembly.typeUpperBound(resultOptions);

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitModifyWithIndecies(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtuple).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, updates.map<[number, MIRArgument]>((update) => [update[0], update[2]]), trgt);
        }

        return [env.setExpressionResult(rtuple)];
    }

    private checkModifyWithNames(env: TypeEnvironment, op: PostfixModifyWithNames, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const updates = op.updates.map<[string, ResolvedType, MIRTempRegister]>((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });

        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => this.updateNamedPropertiesAtom(op.sinfo, opt, updates.map<[string, ResolvedType]>((update) => [update[0], update[1]])));
            const rrecord = this.m_assembly.typeUpperBound(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(rrecord).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, updates.map<[string, MIRArgument]>((update) => [update[0], update[2]]), trgt);
            }

            return [env.setExpressionResult(rrecord)];
        }
        else {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialObjectConceptType()), "Should be subtype of Object");

            const fieldupdates = updates.map<[MIRFieldKey, MIRTempRegister]>((update) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", update[0]);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const decltype = this.m_assembly.normalizeTypeGeneral((fdeclinfo.decl as MemberFieldDecl).declaredType, fdeclinfo.binds) as ResolvedType;
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(update[1], decltype));

                return [MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, update[0]), update[2]];
            });
            
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, fieldupdates, trgt);

                const noinvcheck = texp.options.length === 1 && texp.options[0] instanceof ResolvedEntityAtomType && !this.m_assembly.hasInvariants((texp.options[0] as ResolvedEntityAtomType).object, (texp.options[0] as ResolvedEntityAtomType).binds);
                if (!noinvcheck) {
                    const ttreg = this.m_emitter.bodyEmitter.generateTmpRegister();

                    if (texp.options.length === 1 && texp.options[0] instanceof ResolvedEntityAtomType && this.m_assembly.hasInvariants((texp.options[0] as ResolvedEntityAtomType).object, (texp.options[0] as ResolvedEntityAtomType).binds)) {
                        const oftype = texp.options[0] as ResolvedEntityAtomType;
                        const tkey = MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);
                        const ikey = MIRKeyGenerator.generateStaticKey(oftype.object, "@@invariant", oftype.binds, []);
                        this.m_emitter.bodyEmitter.emitInvokeInvariantCheckDirect(op.sinfo, ikey, tkey, trgt, ttreg);
                    }
                    else {
                        const mirotype = this.m_emitter.registerResolvedTypeReference(texp);
                        this.m_emitter.bodyEmitter.emitInvokeInvariantCheckVirtualTarget(op.sinfo, mirotype.trkey, trgt, ttreg);
                    }

                    const okblock = this.m_emitter.bodyEmitter.createNewBlock("invariantok");
                    const failblock = this.m_emitter.bodyEmitter.createNewBlock("invariantfail");
                    this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, ttreg, true, okblock, failblock);

                    this.m_emitter.bodyEmitter.setActiveBlock(failblock);
                    this.m_emitter.bodyEmitter.emitAbort(op.sinfo, "Invariant Failure");

                    this.m_emitter.bodyEmitter.setActiveBlock(okblock);
                }
            }

            return [env.setExpressionResult(texp)];
        }
    }

    private checkStructuredExtend(env: TypeEnvironment, op: PostfixStructuredExtend, arg: MIRTempRegister, trgt: MIRTempRegister): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        let mergeValue = this.checkExpression(env, op.extension, etreg).getExpressionResult().etype;

        let resultOptions: ResolvedType[] = [];
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialTupleConceptType()), "Must be two Tuples to merge");

            const minarglen = Math.min(...texp.options.map((topt) => (topt as ResolvedTupleAtomType).types.length));
            const maxarglen = Math.min(...texp.options.map((topt) => (topt as ResolvedTupleAtomType).types.length));
            this.raiseErrorIf(op.sinfo, minarglen !== maxarglen, "Appending into tuples with different lengths creates an ambigious result tuple");

            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.appendIntoTupleAtom(op.sinfo, topt as ResolvedTupleAtomType, tmerge));
            }));
            const resulttype = this.m_assembly.typeUpperBound(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendTuple(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, etreg, this.m_emitter.registerResolvedTypeReference(mergeValue).trkey, trgt);
            }

            return [env.setExpressionResult(resulttype)];
        }
        else if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be two Records to merge");

            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.mergeIntoRecordAtom(op.sinfo, topt as ResolvedRecordAtomType, tmerge));
            }));
            const resulttype = this.m_assembly.typeUpperBound(resultOptions);

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendRecord(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, etreg, this.m_emitter.registerResolvedTypeReference(mergeValue).trkey, trgt);
            }

            return [env.setExpressionResult(this.m_assembly.typeUpperBound(resultOptions))];
        }
        else {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialObjectConceptType()), "Can only merge onto Tuples/Records/Objects");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be Record to merge into Object");

            let allnames = new Map<string, ResolvedType>();
            mergeValue.options.forEach((opt) => {
                const record = opt as ResolvedRecordAtomType;
                record.entries.forEach((entry) => {
                    allnames.set(entry.name, allnames.has(entry.name) ? entry.type : this.m_assembly.typeUpperBound([entry.type, allnames.get(entry.name) as ResolvedType]));
                });
            });

            const namel = [...allnames].map((np) => np[0]).sort();
            const fieldResolves = namel.map<[string, MIRFieldKey]>((pname) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", pname);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");

                const fdeclinfo = finfo.root as OOMemberLookupInfo;
                const decltype = this.m_assembly.normalizeTypeGeneral((fdeclinfo.decl as MemberFieldDecl).declaredType, fdeclinfo.binds) as ResolvedType;
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(allnames.get(pname) as ResolvedType, decltype));

                return [pname, MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, pname)];
            });

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendObject(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, this.m_emitter.registerResolvedTypeReference(texp).trkey, etreg, this.m_emitter.registerResolvedTypeReference(mergeValue).trkey, fieldResolves, trgt);

                const noinvcheck = texp.options.length === 1 && texp.options[0] instanceof ResolvedEntityAtomType && !this.m_assembly.hasInvariants((texp.options[0] as ResolvedEntityAtomType).object, (texp.options[0] as ResolvedEntityAtomType).binds);
                if (!noinvcheck) {
                    const ttreg = this.m_emitter.bodyEmitter.generateTmpRegister();

                    if (texp.options.length === 1 && texp.options[0] instanceof ResolvedEntityAtomType && this.m_assembly.hasInvariants((texp.options[0] as ResolvedEntityAtomType).object, (texp.options[0] as ResolvedEntityAtomType).binds)) {
                        const oftype = texp.options[0] as ResolvedEntityAtomType;
                        const tkey = MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);
                        const ikey = MIRKeyGenerator.generateStaticKey(oftype.object, "@@invariant", oftype.binds, []);
                        this.m_emitter.bodyEmitter.emitInvokeInvariantCheckDirect(op.sinfo, ikey, tkey, trgt, ttreg);
                    }
                    else {
                        const mirotype = this.m_emitter.registerResolvedTypeReference(texp);
                        this.m_emitter.bodyEmitter.emitInvokeInvariantCheckVirtualTarget(op.sinfo, mirotype.trkey, trgt, ttreg);
                    }

                    const okblock = this.m_emitter.bodyEmitter.createNewBlock("invariantok");
                    const failblock = this.m_emitter.bodyEmitter.createNewBlock("invariantfail");
                    this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, ttreg, true, okblock, failblock);

                    this.m_emitter.bodyEmitter.setActiveBlock(failblock);
                    this.m_emitter.bodyEmitter.emitAbort(op.sinfo, "Invariant Failure");

                    this.m_emitter.bodyEmitter.setActiveBlock(okblock);
                }
            }

            return [env.setExpressionResult(texp)];
        }
    }

    private checkInvoke(env: TypeEnvironment, op: PostfixInvoke, arg: MIRTempRegister, trgt: MIRTempRegister, optArgVar: string | undefined, refok: boolean): TypeEnvironment[] {
        const texp = env.getExpressionResult().etype;

        const specialcall = (op.name === "isNone" || op.name === "isSome" || op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs");

        //three ways an invoke can be to a single known target
        const isspecific = op.specificResolve !== undefined;
        const isuniquetype = texp.isUniqueCallTargetType();
        const muniqlookup = this.m_assembly.tryGetOOMemberDeclUnique(texp, "method", op.name);
        const isnonvirtdecl = muniqlookup !== undefined && !(muniqlookup.decl as MemberMethodDecl).attributes.includes("abstract") && !(muniqlookup.decl as MemberMethodDecl).attributes.includes("virtual") && !(muniqlookup.decl as MemberMethodDecl).attributes.includes("override");

        const isknown = isspecific || isuniquetype || isnonvirtdecl;

        if (!specialcall && isknown) {
            const resolveType = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp;

            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, resolveType), "This is not a subtype of specified resolve type");

            const mdecltry = this.m_assembly.tryGetOOMemberDeclUnique(resolveType, "method", op.name);
            this.raiseErrorIf(op.sinfo, mdecltry === undefined, `Method not defined for type '${resolveType.idStr}'`);

            const mdecl = mdecltry as OOMemberLookupInfo;

            const binds = this.m_assembly.resolveBindsForCall((mdecl.decl as MemberMethodDecl).invoke.terms, op.terms.targs, mdecl.binds, env.terms);
            this.raiseErrorIf(op.sinfo, binds === undefined, "Call bindings could not be resolved");

            const fsig = this.m_assembly.normalizeTypeFunction((mdecl.decl as MemberMethodDecl).invoke.generateSig(), binds as Map<string, ResolvedType>);
            this.raiseErrorIf(op.sinfo, fsig === undefined, "Invalid function signature");

            //
            //TODO: if we want to do template inference this is a key point -- see the assertion in check args to figure out how to pre-check the body and get a result type
            //

            const eargs = this.checkArgumentsEvaluationWSig(env, fsig as ResolvedFunctionType, op.args, [resolveType, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, fsig as ResolvedFunctionType, eargs);

            this.checkRecursion(op.sinfo, fsig as ResolvedFunctionType, margs.pcodes, op.pragmas.recursive);

            if (this.m_emitEnabled) {
                this.m_emitter.registerResolvedTypeReference(resolveType);
                this.m_emitter.registerTypeInstantiation(mdecl.contiainingType, mdecl.binds);
                const mkey = this.m_emitter.registerMethodCall(mdecl.contiainingType, mdecl.decl as MemberMethodDecl, mdecl.binds, (mdecl.decl as MemberMethodDecl).name, binds as Map<string, ResolvedType>, margs.pcodes, margs.cinfo);

                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(op.sinfo, mkey, margs.args, refinfo, trgt);
            }

            return [env.setExpressionResult((fsig as ResolvedFunctionType).resultType)];
        }
        else {
            const vinfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "method", op.name);
            this.raiseErrorIf(op.sinfo, vinfo.root === undefined, `Missing (or multiple possible) declarations of "${op.name}" method`);

            const vopts = (vinfo.decls as OOMemberLookupInfo[]).map((opt) => {
                const mdecl = (opt.decl as MemberMethodDecl);
                const binds = this.m_assembly.resolveBindsForCall(mdecl.invoke.terms, op.terms.targs, opt.binds, env.terms) as Map<string, ResolvedType>;
                return this.m_assembly.normalizeTypeFunction(mdecl.invoke.generateSig(), binds) as ResolvedFunctionType;
            });

            const rootdecl = (vinfo.root as OOMemberLookupInfo).contiainingType.memberMethods.get(op.name) as MemberMethodDecl;
            const rootbinds = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, (vinfo.root as OOMemberLookupInfo).binds, env.terms) as Map<string, ResolvedType>;
            const rootsig = this.m_assembly.normalizeTypeFunction(rootdecl.invoke.generateSig(), rootbinds) as ResolvedFunctionType;

            const lsigtry = this.m_assembly.computeUnifiedFunctionType(vopts, rootsig);
            this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for invoke");

            //
            //TODO: if we want to do template inference this is a key point -- see the assertion in check args to figure out how to pre-check the body and get a result type
            //

            const lsig = lsigtry as ResolvedFunctionType;
            const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, [texp, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);

            this.checkRecursion(op.sinfo, lsig as ResolvedFunctionType, margs.pcodes, op.pragmas.recursive);

            if (this.m_emitEnabled) {
                let cbindsonly = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, new Map<string, ResolvedType>(), env.terms) as Map<string, ResolvedType>;

                const specialm0type = this.m_emitter.registerResolvedTypeReference(margs.types.length === 1 ? margs.types[0] : this.m_assembly.getSpecialNoneType()).trkey;
                if (op.name === "isNone") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "isSome") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeConceptType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs") {
                    const ttype = rootbinds.get("T") as ResolvedType;
                    const mt = this.m_emitter.registerResolvedTypeReference(ttype);

                    if (op.name === "is") {
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, mt.trkey, specialm0type, margs.args[0]);
                    }
                    else if (op.name === "as") {
                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Las_done");
                        const failblck = this.m_emitter.bodyEmitter.createNewBlock("Las_fail");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, true, doneblck, failblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(failblck);
                        this.m_emitter.bodyEmitter.emitAbort(op.sinfo, "as<T> fail");
                        
                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);
                    }
                    else if (op.name === "tryAs") {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);

                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, true, doneblck, noneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, doneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                    else {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);

                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, true, doneblck, noneblck);

                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[1], trgt);

                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                }
                else {
                    const vkey = this.m_emitter.registerVirtualMethodCall((vinfo.root as OOMemberLookupInfo).contiainingType, (vinfo.root as OOMemberLookupInfo).binds, op.name, cbindsonly, margs.pcodes, margs.cinfo);

                    const refinfo = this.generateRefInfoForCallEmit(lsig, margs.refs);
                    this.m_emitter.bodyEmitter.emitInvokeVirtualTarget(op.sinfo, vkey, margs.args, this.m_emitter.registerResolvedTypeReference(texp).trkey, refinfo, trgt);
                }
            }

            if (!this.AnySplitMethods.some((m) => m === op.name)) {
                const returnOpts = vopts.map((ropt) => ropt.resultType);
                return [env.setExpressionResult(this.m_assembly.typeUpperBound(returnOpts))];
            }
            else {
                //
                //TODO: we may want to do some as/tryAs action here as well
                //
                let opname = op.name;
                if (op.name === "is") {
                    const ttype = rootbinds.get("T") as ResolvedType;
                    if (ttype.isNoneType()) {
                        opname = "isNone";
                    }
                    else if (ttype.isSomeType()) {
                        opname = "isSome";
                    }
                    else {
                        //don't specialize
                    }
                }

                if (opname === "isNone" || opname === "isSome") {
                    const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, [env]);

                    //
                    //TODO: we are not going to warn here since template instantiation can be annoying 
                    //      should have one mode for TypeCheck -- only on un-templated code and one for compile
                    //
                    //this.raiseErrorIf(op.sinfo, enone.length === 0, "Value is never equal to none");
                    //this.raiseErrorIf(op.sinfo, esome.length === 0, "Value is always equal to none");

                    if (optArgVar === undefined) {
                        const eqnone = enone.map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));
                        const neqnone = esome.map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                        return [...eqnone, ...neqnone];
                    }
                    else {
                        const eqnone = enone.map((opt) => opt
                            .assumeVar(optArgVar, (opt.expressionResult as ExpressionReturnResult).etype)
                            .setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));

                        const neqnone = esome.map((opt) => opt
                            .assumeVar(optArgVar, (opt.expressionResult as ExpressionReturnResult).etype)
                            .setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                        return [...eqnone, ...neqnone];
                    }
                }
                else {
                    const ttype = rootbinds.get("T") as ResolvedType;

                    //
                    //TODO: we are not going to warn here since template instantiation can be annoying 
                    //      should have one mode for TypeCheck -- only on un-templated code and one for compile
                    //
                    //this.raiseErrorIf(op.sinfo, tvals.length === 0, "Value is never of type");
                    //this.raiseErrorIf(op.sinfo, ntvals.length === 0, "Value is always of type");

                    if (optArgVar === undefined) {
                        const tvals = [env]
                            .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

                        const ntvals = [env]
                            .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

                        return [...tvals, ...ntvals];
                    }
                    else {
                        const tvals = [env]
                            .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt
                                .assumeVar(optArgVar, this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

                        const ntvals = [env]
                            .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                            .map((opt) => opt
                                .assumeVar(optArgVar, this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

                        return [...tvals, ...ntvals];
                    }
                }
            }
        }
    }

    private checkElvisAction(sinfo: SourceInfo, env: TypeEnvironment[], elvisEnabled: boolean, etrgt: MIRTempRegister, noneblck: string): [TypeEnvironment[], TypeEnvironment[]] {
        const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, env);
        //this.raiseErrorIf(sinfo, enone.length === 0 && elvisEnabled, "None value is not possible -- will never return none and elvis access is redundant");
        //this.raiseErrorIf(sinfo, esome.length === 0 && elvisEnabled, "Some value is not possible -- will always return none and following expression is redundant");

        if (this.m_emitEnabled && elvisEnabled) {
            const nextblk = this.m_emitter.bodyEmitter.createNewBlock("Lelvis");
            this.m_emitter.bodyEmitter.emitNoneJump(sinfo, etrgt, noneblck, nextblk);
            this.m_emitter.bodyEmitter.setActiveBlock(nextblk);
        }

        return elvisEnabled ? [esome, enone] : [[...esome, ...enone], []];
    }

    private checkPostfixExpression(env: TypeEnvironment, exp: PostfixOp, trgt: MIRTempRegister, refok: boolean): TypeEnvironment[] {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_none") : "[DISABLED]";
        const doneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_done") : "[DISABLED]";

        let etgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt);

        if (exp.rootExp instanceof AccessVariableExpression && exp.ops.length === 1 && exp.ops[0] instanceof PostfixInvoke) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, eenv, exp.ops[0].isElvis, etgrt, noneblck);

            const res = this.checkInvoke(TypeEnvironment.join(this.m_assembly, ...fflow), exp.ops[0] as PostfixInvoke, etgrt, trgt, exp.rootExp.name, refok);

            if (hasNoneCheck && this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            return [...res, ...scflow];
        }
        else {
            let scflows: TypeEnvironment[] = [];
            let cenv = eenv;
            for (let i = 0; i < exp.ops.length; ++i) {
                const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, etgrt, noneblck);
                scflows = [...scflows, ...scflow];

                const nflow = TypeEnvironment.join(this.m_assembly, ...fflow);
                const ntgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
                switch (exp.ops[i].op) {
                    case PostfixOpTag.PostfixAccessFromIndex:
                        cenv = this.checkAccessFromIndex(nflow, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromIndecies:
                        cenv = this.checkProjectFromIndecies(nflow, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixAccessFromName:
                        cenv = this.checkAccessFromName(nflow, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromNames:
                        cenv = this.checkProjectFromNames(nflow, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixProjectFromType:
                        cenv = this.checkProjectFromType(nflow, exp.ops[i] as PostfixProjectFromType, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixModifyWithIndecies:
                        cenv = this.checkModifyWithIndecies(nflow, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixModifyWithNames:
                        cenv = this.checkModifyWithNames(nflow, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt);
                        break;
                    case PostfixOpTag.PostfixStructuredExtend:
                        cenv = this.checkStructuredExtend(nflow, exp.ops[i] as PostfixStructuredExtend, etgrt, ntgrt);
                        break;
                    default:
                        this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                        cenv = this.checkInvoke(nflow, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, undefined, refok);
                        break;
                }

                etgrt = ntgrt;
            }

            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, etgrt, trgt);

                if (hasNoneCheck) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                    this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                    this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                    this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                }
            }

            return [...cenv, ...scflows];
        }
    }

    private checkPrefixOp(env: TypeEnvironment, exp: PrefixOp, trgt: MIRTempRegister): TypeEnvironment[] {
        if (exp.op === "+" || exp.op === "-") {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const eres = this.checkExpression(env, exp.exp, etreg);

            const isinttype = this.m_assembly.subtypeOf(eres.getExpressionResult().etype, this.m_assembly.getSpecialIntType());
            const isfloattype = this.m_assembly.subtypeOf(eres.getExpressionResult().etype, this.m_assembly.getSpecialFloat64Type());
            this.raiseErrorIf(exp.sinfo, !(isinttype || isfloattype), "Prefix + and - only applicable to numeric values");

            if (this.m_emitEnabled) {
                const mirargtype = this.m_emitter.registerResolvedTypeReference(eres.getExpressionResult().etype).trkey;
                this.m_emitter.bodyEmitter.emitPrefixOp(exp.sinfo, exp.op, etreg, mirargtype, trgt);
            }

            return [env.setExpressionResult(eres.getExpressionResult().etype)];
        }
        else {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg);
            const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

            this.raiseErrorIf(exp.sinfo, estates.some((state) => !this.m_assembly.subtypeOf(state.getExpressionResult().etype, okType)), "Operator ! only applicable to None/Bool values");

            const [tstates, fstates] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, estates);
            const ntstates = tstates.map((state) => state.setExpressionResult(state.getExpressionResult().etype, FlowTypeTruthValue.False));
            const nfstates = fstates.map((state) => state.setExpressionResult(state.getExpressionResult().etype, FlowTypeTruthValue.True));

            if (this.m_emitEnabled) {
                const isstrict = estates.every((state) => this.m_assembly.subtypeOf(state.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                const boolkey = this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()).trkey;
                this.m_emitter.bodyEmitter.emitPrefixNot(exp.sinfo, "!", isstrict, etreg, boolkey, trgt);
            } 

            return [...ntstates, ...nfstates];
        }
    }

    private checkTailTypeExpression(ev: TypeEnvironment, exp: TailTypeExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const cenv = this.checkExpression(ev, exp.exp, etreg);
        const op = exp.op;
        const ttype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, ev.terms);

        const optvname = (exp.exp instanceof AccessVariableExpression) ? (exp.exp as AccessVariableExpression).name : undefined;

        if (this.m_emitEnabled) {
            const infertt = this.m_emitter.registerResolvedTypeReference(cenv.getExpressionResult().etype);
            const mt = this.m_emitter.registerResolvedTypeReference(ttype);

            if (op === "typeis") {
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, mt.trkey, infertt.trkey, etreg);
            }
            else if (op === "typeas") {
                const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Las_done");
                const failblck = this.m_emitter.bodyEmitter.createNewBlock("Las_fail");
                const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, creg, mt.trkey, infertt.trkey, etreg);
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, creg, true, doneblck, failblck);

                this.m_emitter.bodyEmitter.setActiveBlock(failblck);
                this.m_emitter.bodyEmitter.emitAbort(exp.sinfo, "typeas fail");

                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, etreg, trgt);
            }
            else {
                this.raiseErrorIf(exp.sinfo, op !== "typetry");

                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, etreg, trgt);

                const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_done");
                const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_none");
                const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, creg, mt.trkey, infertt.trkey, etreg);
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, creg, true, doneblck, noneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);

                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }
        }

        //
        //TODO: we may want to do some as/tryAs action here as well
        //
        if (op === "typeas") {
            return [cenv.setExpressionResult(ttype)];
        }
        else if(op === "tryas") {
            return [cenv.setExpressionResult(this.m_assembly.typeUpperBound([ttype, this.m_assembly.getSpecialNoneType()]))];
        }
        else {
            let opname = op;

            if (ttype.isNoneType()) {
                opname = "isNone";
            }
            else if (ttype.isSomeType()) {
                opname = "isSome";
            }
            else {
                //don't specialize
            }

            if (opname === "isNone" || opname === "isSome") {
                const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, [cenv]);

                //
                //TODO: we are not going to warn here since template instantiation can be annoying 
                //      should have one mode for TypeCheck -- only on un-templated code and one for compile
                //
                //this.raiseErrorIf(op.sinfo, enone.length === 0, "Value is never equal to none");
                //this.raiseErrorIf(op.sinfo, esome.length === 0, "Value is always equal to none");

                if (optvname === undefined) {
                    const eqnone = enone.map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));
                    const neqnone = esome.map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                    return [...eqnone, ...neqnone];
                }
                else {
                    const eqnone = enone.map((opt) => opt
                        .assumeVar(optvname, (opt.expressionResult as ExpressionReturnResult).etype)
                        .setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));

                    const neqnone = esome.map((opt) => opt
                        .assumeVar(optvname, (opt.expressionResult as ExpressionReturnResult).etype)
                        .setExpressionResult(this.m_assembly.getSpecialBoolType(), opname === "isNone" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

                    return [...eqnone, ...neqnone];
                }
            }
            else {
                //
                //TODO: we are not going to warn here since template instantiation can be annoying 
                //      should have one mode for TypeCheck -- only on un-templated code and one for compile
                //
                //this.raiseErrorIf(op.sinfo, tvals.length === 0, "Value is never of type");
                //this.raiseErrorIf(op.sinfo, ntvals.length === 0, "Value is always of type");

                if (optvname === undefined) {
                    const tvals = [cenv]
                        .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

                    const ntvals = [cenv]
                        .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

                    return [...tvals, ...ntvals];
                }
                else {
                    const tvals = [cenv]
                        .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) =>
                            opt.assumeVar(optvname, this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

                    const ntvals = [cenv]
                        .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) =>
                            opt.assumeVar(optvname, this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype))
                                .setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

                    return [...tvals, ...ntvals];
                }
            }
        }
    }

    private checkBinOp(env: TypeEnvironment, exp: BinOpExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);
        const lhstype = lhs.getExpressionResult().etype;

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);
        const rhstype = rhs.getExpressionResult().etype;
        
        this.raiseErrorIf(exp.sinfo, !(this.m_assembly.subtypeOf(lhstype, this.m_assembly.getSpecialIntType()) || this.m_assembly.subtypeOf(lhstype, this.m_assembly.getSpecialBigIntType()) || this.m_assembly.subtypeOf(lhstype, this.m_assembly.getSpecialFloat64Type())), "Operand can only be applied to Int, BigInt, or Float64 types");
        this.raiseErrorIf(exp.sinfo, !(this.m_assembly.subtypeOf(rhstype, this.m_assembly.getSpecialIntType()) || this.m_assembly.subtypeOf(rhstype, this.m_assembly.getSpecialBigIntType()) || this.m_assembly.subtypeOf(rhstype, this.m_assembly.getSpecialFloat64Type())), "Operand can only be applied to Int, BigInt, or Float64 types");    
        this.raiseErrorIf(exp.sinfo, lhstype.idStr !== rhstype.idStr, "Operand types must be the same");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinOp(exp.sinfo, lhstype.idStr, lhsreg, exp.op, rhstype.idStr, rhsreg, trgt);
        }

        return [env.setExpressionResult(lhstype)];
    }

    private checkBinEq(env: TypeEnvironment, exp: BinEqExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);

        xxxx;
        if(/*lhs is None || rhs is None*/) {
            //do optimized none checks
        }
        else if(/*lhs is Empty || rhs is Empty*/) {
            //do optimized empty checks
        }
        else {
            //do regular equality
        }

        const [pairwiseok, isstrict] = this.checkValueEq(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype);
        this.raiseErrorIf(exp.sinfo, !pairwiseok, "Types are incompatible for equality compare");

        if (this.m_emitEnabled) {
            if (exp.lhs instanceof LiteralNoneExpression && exp.rhs instanceof LiteralNoneExpression) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, exp.op === "==" ? true : false, trgt);
            }
            else if (exp.lhs instanceof LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeConceptType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg);
            }
            else if (exp.rhs instanceof LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeConceptType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt, !isstrict);
            }
        }

        if ((exp.lhs instanceof LiteralNoneExpression && exp.rhs instanceof AccessVariableExpression) ||
            (exp.lhs instanceof AccessVariableExpression && exp.rhs instanceof LiteralNoneExpression)) {

            const [enone, esome] = TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, exp.rhs instanceof AccessVariableExpression ? [rhs] : [lhs]);
            this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
            this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");

            const vname = exp.rhs instanceof AccessVariableExpression ? exp.rhs.name : (exp.lhs as AccessVariableExpression).name;

            const eqnone = enone.map((opt) => opt
                .assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype)
                .setExpressionResult(this.m_assembly.getSpecialBoolType(), exp.op === "==" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False));

            const neqnone = esome.map((opt) => opt
                .assumeVar(vname, (opt.expressionResult as ExpressionReturnResult).etype)
                .setExpressionResult(this.m_assembly.getSpecialBoolType(), exp.op === "==" ? FlowTypeTruthValue.False : FlowTypeTruthValue.True));

            return [...eqnone, ...neqnone];
        }
        else {
            return [env.setExpressionResult(this.m_assembly.getSpecialBoolType())];
        }
    }

    private checkBinCmp(env: TypeEnvironment, exp: BinCmpExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);

        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);

        this.raiseErrorIf(exp.sinfo, !this.checkValueLess(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype), "Types are incompatible for order compare");

        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt);
        }

        return [env.setExpressionResult(this.m_assembly.getSpecialBoolType())];
    }

    private checkBinLogic(env: TypeEnvironment, exp: BinLogicExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const okType = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);

        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);

        this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_rest");
        if (this.m_emitEnabled) {
            const isstrict = lhs.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
            if (exp.op === "||") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, isstrict, scblck, restblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else if (exp.op === "&&") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, isstrict, restblck, scblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, false, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, isstrict, restblck, scblck);

                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }

            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }

        const [trueflow, falseflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, lhs);

        //THIS IS WRONG -- in "true && x" the true is redundant but the rest of the expressions needs to be evaluated 
        //this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false rest of expression is infeasible");

        if (exp.op === "||") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...falseflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                const rhsstrict = rhs.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                if (rhsstrict) {
                    this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rhsreg, trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                }
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);

            //THIS IS WRONG -- in "x || false" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...trueflow, ...rtflow, ...rfflow];
        }
        else if (exp.op === "&&") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                const rhsstrict = rhs.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                if (rhsstrict) {
                    this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rhsreg, trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                }
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);

            //THIS IS WRONG -- in "x && true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow, ...rtflow, ...rfflow];
        }
        else {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");

            if (this.m_emitEnabled) {
                const rhsstrict = rhs.every((opt) => this.m_assembly.subtypeOf(opt.getExpressionResult().etype, this.m_assembly.getSpecialBoolType()));
                if (rhsstrict) {
                    this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rhsreg, trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                }
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }

            const [rtflow, rfflow] = TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);

            //THIS IS WRONG -- in "x => true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow.map((opt) => opt.setExpressionResult(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)), ...rtflow, ...rfflow];
        }
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, trgt: MIRTempRegister): TypeEnvironment[] {
        const kreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const ktype = this.checkExpression(env, exp.kexp, kreg).getExpressionResult().etype;

        this.raiseErrorIf(exp.kexp.sinfo, !this.m_assembly.subtypeOf(ktype, this.m_assembly.getSpecialKeyTypeConceptType()), "Key must be a KeyType value");

        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const vtype = this.checkExpression(env, exp.vexp, vreg).getExpressionResult().etype;

        const mentity = this.m_assembly.tryGetObjectTypeForFullyResolvedName("NSCore::MapEntry") as EntityTypeDecl;
        const mbinds = new Map<string, ResolvedType>().set("K", ktype).set("V", vtype);
        const mtype = ResolvedType.createSingle(ResolvedEntityAtomType.create(mentity, mbinds));

        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(mtype);
            this.m_emitter.registerTypeInstantiation(mentity, mbinds);
            const tkey = MIRKeyGenerator.generateTypeKey(mentity, mbinds);

            this.m_emitter.bodyEmitter.emitConstructorPrimary(exp.sinfo, tkey, [kreg, vreg], trgt);
        }

        return [env.setExpressionResult(mtype)];
    }

    private checkNonecheck(env: TypeEnvironment, exp: NonecheckExpression, trgt: MIRTempRegister): TypeEnvironment[] {
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

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRTempRegister, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
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
