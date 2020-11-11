//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRAbort, MIRAllTrue, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRBody, MIRCheckNoError, MIRConstantBigInt, MIRConstantBigNat, MIRConstantComplex, MIRConstantDecmial, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeadFlow, MIRDebug, MIRDeclareGuardFlagLocation, MIREntityProjectToEphemeral, MIREntityUpdate, MIREphemeralListExtend, MIRExtractResultOkValue, MIRFieldKey, MIRGlobalKey, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadConstDataString, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRLocalVarStore, MIRMultiLoadFromEpehmeralList, MIRNop, MIROp, MIRParameterVariable, MIRParameterVarStore, MIRPrefixNotOp, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTempRegister, MIRTempRegisterAssign, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRVarLifetimeEnd, MIRVarLifetimeStart, MIRVirtualMethodKey } from "./mir_ops";
import { Assembly, BuildLevel, EntityTypeDecl, InvokeDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, OOPTypeDecl, StaticFunctionDecl, StaticMemberDecl, StaticOperatorDecl } from "../ast/assembly";
import { ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedEphemeralListType, ResolvedFunctionType, ResolvedLiteralAtomType, ResolvedRecordAtomType, ResolvedTupleAtomType, ResolvedType } from "../ast/resolved_type";
import { MIRAssembly, MIRConceptType, MIREntityType, MIREphemeralListType, MIRLiteralType, MIRRecordType, MIRRecordTypeEntry, MIRTupleType, MIRTupleTypeEntry, MIRType, MIRTypeOption, PackageConfig } from "./mir_assembly";

import { TypeChecker } from "../type_checker/type_checker";
import { propagateTmpAssignForBody, removeDeadTempAssignsFromBody } from "./mir_cleanup";
import { convertBodyToSSA } from "./mir_ssa";
import { computeVarTypesForInvoke } from "./mir_vartype";
import { functionalizeInvokes } from "./functionalize";
import { BSQRegex } from "../ast/bsqregex";
import { ConstantExpressionValue } from "../ast/body";
import { ValueType } from "../type_checker/type_environment";

import * as Crypto from "crypto";

type PCode = {
    code: InvokeDecl,
    scope: MIRInvokeKey,
    captured: Map<string, ResolvedType>,
    ftype: ResolvedFunctionType
};

class MIRKeyGenerator {
    static computeBindsKeyInfo(binds: Map<string, ResolvedType>): string {
        if (binds.size === 0) {
            return "";
        }

        let terms: string[] = [];
        binds.forEach((v, k) => terms.push(`${k}=${v.idStr}`));

        return `<${terms.sort().join(", ")}>`;
    }

    static computePCodeKeyInfo(pcodes: PCode[]): string {
        if (pcodes.length === 0) {
            return "";
        }

        return "[" + pcodes.map((pc) => `${pc.code.srcFile}%${pc.code.sourceLocation.line}%${pc.code.sourceLocation.column}`).join(",") + "]";
    }

    static generateTypeKey(t: ResolvedType): MIRResolvedTypeKey {
        return t.idStr;
    }

    static generateFieldKey(t: ResolvedType, name: string): MIRFieldKey {
        return `${MIRKeyGenerator.generateTypeKey(t)}.${name}`;
    }

    static generateFunctionKey(prefix: string, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${prefix}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateMethodKey(name: string, t: MIRResolvedTypeKey, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${t}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRVirtualMethodKey {
        return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generatePCodeKey(inv: InvokeDecl): MIRInvokeKey {
        return `fn--${inv.srcFile}+${inv.sourceLocation.line}##${inv.sourceLocation.pos}`;
    }

    static generateOperatorSignatureKey(ikey: MIRInvokeKey, isprefix: boolean, isinfix: boolean, sigkeys: string[]): string {
        if(isprefix) {
            ikey = ikey + "=prefix";
        }
        if(isinfix) {
            ikey = ikey + "=infix";
        }

        return ikey + `=(${sigkeys.join(", ")})`
    }
}

class MIREmitter {
    readonly assembly: Assembly;
    readonly masm: MIRAssembly;
    
    private readonly pendingOOProcessing: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingConstExprProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, ConstantExpressionValue, string[], Map<string, ResolvedType>, ResolvedType][] = [];
    private readonly pendingFunctionProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOperatorProcessing: [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOOMethodProcessing: [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingPCodeProcessing: [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]][] = [];
    private readonly entityInstantiationInfo: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];
    private readonly allVInvokes: [MIRVirtualMethodKey, MIRResolvedTypeKey, ResolvedType, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly allVOPInvokes: [MIRVirtualMethodKey, string | undefined, ResolvedType | undefined, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];

    private emitEnabled: boolean;
    
    private m_blockMap: Map<string, MIRBasicBlock> = new Map<string, MIRBasicBlock>();
    private m_currentBlockName = "UNDEFINED";
    private m_currentBlock: MIROp[] = [];

    private m_tmpIDCtr = 0;

    private yieldPatchInfo: [string, MIRTempRegister, ValueType][][] = [];
    private returnPatchInfo: [string, MIRTempRegister, ValueType][] = [];

    private constructor(assembly: Assembly, masm: MIRAssembly, emitEnabled: boolean) {
        this.assembly = assembly;
        this.masm = masm;

        this.emitEnabled = emitEnabled;
    }

    getEmitEnabled(): boolean {
        return this.emitEnabled;
    }

    setEmitEnabled(enabled: boolean) {
        this.emitEnabled = enabled;
    }

    initializeBodyEmitter() {
        this.m_tmpIDCtr = 0;

        this.m_blockMap = new Map<string, MIRBasicBlock>();
        this.m_blockMap.set("entry", new MIRBasicBlock("entry", []));
        this.m_blockMap.set("returnassign", new MIRBasicBlock("returnassign", []));
        this.m_blockMap.set("exit", new MIRBasicBlock("exit", []));

        this.m_currentBlockName = "entry";
        this.m_currentBlock = (this.m_blockMap.get("entry") as MIRBasicBlock).ops;

        this.yieldPatchInfo = [];
        this.returnPatchInfo = [];
    }

    generateTmpRegister(): MIRTempRegister {
        if(!this.emitEnabled) {
            return new MIRTempRegister(-1);
        }

        return new MIRTempRegister(this.m_tmpIDCtr++);
    }

    generateCapturedVarName(name: string): string {
        return "__c_" + name;
    }

    createNewBlock(pfx: string): string {
        if(!this.emitEnabled) {
            return "DISABLED";
        }

        const name = `${pfx}_${this.m_blockMap.size}`;
        this.m_blockMap.set(name, new MIRBasicBlock(name, []));

        return name;
    }

    getActiveBlockName(): string {
        return this.m_currentBlockName;
    }

    setActiveBlock(name: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlockName = name;
        this.m_currentBlock = (this.m_blockMap.get(name) as MIRBasicBlock).ops;
    }

    emitNOP(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRNop(sinfo));
    }

    emitDeadBlock(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDeadFlow(sinfo));
    }

    emitAbort(sinfo: SourceInfo, info: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAbort(sinfo, info));
    }

    emitAssertCheck(sinfo: SourceInfo, msg: string, src: MIRArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAssertCheck(sinfo, msg, src));
    }

    emitDebugBreak(sinfo: SourceInfo) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDebug(sinfo, undefined));
    }

    emitDebugPrint(sinfo: SourceInfo, value: MIRArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRDebug(sinfo, value));
    }

    emitRegisterStore(sinfo: SourceInfo, src: MIRArgument, trgt: MIRRegisterArgument, vtype: MIRType, guard: MIRGuard | undefined) {
        if (!this.emitEnabled) {
            return;
        }

        if (trgt instanceof MIRTempRegister) {
            this.m_currentBlock.push(new MIRTempRegisterAssign(sinfo, src, trgt, vtype.trkey, guard));
        }
        else if (trgt instanceof MIRParameterVariable) {
            this.m_currentBlock.push(new MIRParameterVarStore(sinfo, src, trgt, vtype.trkey, guard));
        }
        else {
            this.m_currentBlock.push(new MIRLocalVarStore(sinfo, src, trgt as MIRParameterVariable, vtype.trkey, guard));
        }
    }

    emitLoadUninitVariableValue(sinfo: SourceInfo, oftype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        //This value will not be accessed from but can be passed/assigned atomically
        //we need to have space for it etc. so just plop a "fresh" or zero-filled value there
        this.m_currentBlock.push(new MIRLoadUnintVariableValue(sinfo, trgt, oftype.trkey));
    }

    emitGuardFlagLocation(sinfo: SourceInfo, name: string, count: number): string {
        if(!this.emitEnabled || count === 0) {
            return "[IGNORE]";
        }

        this.m_currentBlock.push(new MIRDeclareGuardFlagLocation(sinfo, name, count));
        return name;
    }

    emitSetGuardFlagConstant(sinfo: SourceInfo, name: string, position: number, flag: boolean) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRSetConstantGuardFlag(sinfo, name, position, flag));
    }

    emitConvert(sinfo: SourceInfo, srctypelayout: MIRType, srctypeflow: MIRType, intotype: MIRType, src: MIRArgument, trgt: MIRRegisterArgument, guard: MIRGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConvertValue(sinfo, srctypelayout.trkey, srctypeflow.trkey, intotype.trkey, src, trgt, guard));
    }

    emitCheckNoError(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRCheckNoError(sinfo, src, srctype.trkey, trgt));
    }

    emitExtractResultOkValue(sinfo: SourceInfo, src: MIRArgument, srctype: MIRType, valuetype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRExtractResultOkValue(sinfo, src, srctype.trkey, valuetype.trkey, trgt));
    }

    emitLoadConstNone(sinfo: SourceInfo, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNone(), trgt));
    }

    emitLoadConstBool(sinfo: SourceInfo, bv: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, bv ? new MIRConstantTrue() : new MIRConstantFalse(), trgt));
    }

    emitLoadConstIntegralValue(sinfo: SourceInfo, itype: MIRType, vv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(itype.trkey === "NSCore::Int") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantInt(vv), trgt));
        }
        else if(itype.trkey === "NSCore::Nat") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantNat(vv), trgt));
        }
        else if(itype.trkey === "NSCore::BigInt") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigInt(vv), trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantBigNat(vv), trgt));
        }
    }

    emitLoadConstRational(sinfo: SourceInfo, iv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRational(iv), trgt));
    }

    emitLoadConstFloatPoint(sinfo: SourceInfo, ftype: MIRType, fv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        if(ftype.trkey === "NSCore::Float") {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantFloat(fv), trgt));
        }
        else {
            this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantDecmial(fv), trgt));
        }
    }

    emitLoadConstComplex(sinfo: SourceInfo, rv: string, iv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantComplex(rv, iv), trgt));
    }

    emitLoadConstString(sinfo: SourceInfo, sv: string, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantString(sv), trgt));
    }

    emitLoadLiteralRegex(sinfo: SourceInfo, restr: BSQRegex, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantRegex(restr), trgt));
    }

    emitLoadLiteralStringOf(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConst(sinfo, new MIRConstantStringOf(sv, tskey), trgt));
    }

    emitLoadConstDataString(sinfo: SourceInfo, sv: string, tskey: MIRResolvedTypeKey, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadConstDataString(sinfo, sv, tskey, trgt));
    }

    emitTupleHasIndex(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRTupleHasIndex(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, isvirtual, trgt));
    }

    emitRecordHasProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRRecordHasProperty(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, isvirtual, trgt));
    }
    
    emitLoadTupleIndex(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndex(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, isvirtual, resulttype.trkey, trgt));
    }

    emitLoadTupleIndexSetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, idx: number, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadTupleIndexSetGuard(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, idx, isvirtual, resulttype.trkey, trgt, guard));
    }

    emitLoadProperty(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordProperty(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, isvirtual, resulttype.trkey, trgt));
    }

    emitLoadRecordPropertySetGuard(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, pname: string, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadRecordPropertySetGuard(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, pname, isvirtual, resulttype.trkey, trgt, guard));
    }

    emitLoadField(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fname: MIRFieldKey, isvirtual: boolean, resulttype: MIRType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRLoadField(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, fname, isvirtual, resulttype.trkey, trgt));
    }

    emitTupleProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, indecies: number[], epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRTupleProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, indecies, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitRecordProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, properties: string[], epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRRecordProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, properties, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitEntityProjectToEphemeral(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREntityProjectToEphemeral(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, fields, this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey, trgt));
    }

    emitTupleUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [number, ResolvedType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [number, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRTupleUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, trgt));
    }

    emitRecordUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [string, ResolvedType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [string, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIRRecordUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, trgt));
    }

    emitEntityUpdate(sinfo: SourceInfo, arg: MIRArgument, arglayouttype: MIRType, argflowtype: MIRType, updates: [MIRFieldKey, ResolvedType, MIRArgument][], trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const upds = updates.map((upd) => [upd[0], upd[2], this.registerResolvedTypeReference(upd[1]).trkey] as [MIRFieldKey, MIRArgument, MIRResolvedTypeKey]);
        this.m_currentBlock.push(new MIREntityUpdate(sinfo, arg, arglayouttype.trkey, argflowtype.trkey, upds, trgt));
    }

    emitLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, idx: number, resulttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, arg, argtype.trkey, idx, resulttype.trkey, trgt));
    }

    emitMultiLoadFromEpehmeralList(sinfo: SourceInfo, arg: MIRArgument, argtype: MIRType, trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[]) {
        if (!this.emitEnabled) {
            return;
        }

        const etrgts = trgts.map((trgt) => {
            return { pos: trgt.pos, into: trgt.into, oftype: trgt.oftype.trkey };
        });
        this.m_currentBlock.push(new MIRMultiLoadFromEpehmeralList(sinfo, arg, argtype.trkey, etrgts));
    }

    emitInvokeFixedFunction(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.declresult.trkey, ikey, args, optstatusmask, trgt, undefined));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.runtimeresult.trkey, ikey, args, optstatusmask, rr, undefined));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return { pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeFixedFunctionWithGuard(sinfo: SourceInfo, ikey: MIRInvokeKey, args: MIRArgument[], optstatusmask: string | undefined, retinfo: MIRType, trgt: MIRRegisterArgument, guard: MIRGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRInvokeFixedFunction(sinfo, retinfo.trkey, ikey, args, optstatusmask, trgt, guard));
    }

    emitInvokeVirtualFunction(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, rcvrlayouttype: MIRType, rcvrflowtype: MIRType, args: MIRArgument[], optstatusmask: string | undefined, rretinfo: MIRType | { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRRegisterArgument) {
        if(!this.emitEnabled) {
            return;
        }

        const retinfo = rretinfo instanceof MIRType ? { declresult: rretinfo, runtimeresult: rretinfo, elrcount: -1, refargs: [] as [MIRRegisterArgument, MIRType][] } : rretinfo;
        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.declresult.trkey, vresolve, rcvrlayouttype.trkey, rcvrflowtype.trkey, args, optstatusmask, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualFunction(sinfo, retinfo.runtimeresult.trkey, vresolve, rcvrlayouttype.trkey, rcvrflowtype.trkey, args, optstatusmask, rr));
           
            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return {pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx]};
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitInvokeVirtualOperator(sinfo: SourceInfo, vresolve: MIRVirtualMethodKey, args: { arglayouttype: MIRType, argflowtype: MIRType, arg: MIRArgument }[], retinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [MIRRegisterArgument, MIRType][] }, trgt: MIRTempRegister) {
        const eargs = args.map((arg) => {
            return { arglayouttype: arg.arglayouttype.trkey, argflowtype: arg.argflowtype.trkey, arg: arg.arg };
        });

        if (retinfo.refargs.length === 0) {
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.declresult.trkey, vresolve, eargs, trgt));
        }
        else {
            const rr = this.generateTmpRegister();
            this.m_currentBlock.push(new MIRInvokeVirtualOperator(sinfo, retinfo.runtimeresult.trkey, vresolve, eargs, rr));

            if (retinfo.elrcount === -1) {
                this.m_currentBlock.push(new MIRLoadFromEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, 0, retinfo.declresult.trkey, trgt));
            }
            else {
                this.m_currentBlock.push(new MIRSliceEpehmeralList(sinfo, rr, retinfo.runtimeresult.trkey, retinfo.declresult.trkey, trgt));
            }

            const refbase = retinfo.elrcount != -1 ? retinfo.elrcount : 1;
            const argvs = retinfo.refargs.map((rinfo, idx) => {
                return { pos: refbase + idx, into: rinfo[0], oftype: (retinfo.declresult.options[0] as MIREphemeralListType).entries[refbase + idx] };
            });

            this.emitMultiLoadFromEpehmeralList(sinfo, rr, retinfo.declresult, argvs);
        }
    }

    emitConstructorTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTuple(sinfo, resultTupleType.trkey, args, trgt));
    }

    emitConstructorTupleFromEphemeralList(sinfo: SourceInfo, resultTupleType: MIRType, arg: MIRArgument, elisttype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorTupleFromEphemeralList(sinfo, resultTupleType.trkey, arg, elisttype.trkey, trgt));
    }

    emitConstructorRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: [string, MIRArgument][], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecord(sinfo, resultRecordType.trkey, args, trgt));
    }

    emitConstructorRecordFromEphemeralList(sinfo: SourceInfo, resultRecordType: MIRType, arg: MIRArgument, elisttype: MIRType, namelayout: string[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorRecordFromEphemeralList(sinfo, resultRecordType.trkey, arg, elisttype.trkey, namelayout, trgt));
    }

    emitStructuredAppendTuple(sinfo: SourceInfo, resultTupleType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.trkey, flow: tt.flow.trkey };
        });
        this.m_currentBlock.push(new MIRStructuredAppendTuple(sinfo, resultTupleType.trkey, args, etypes, trgt));
    } 

    emitStructuredJoinRecord(sinfo: SourceInfo, resultRecordType: MIRType, args: MIRArgument[], ttypes: {layout: MIRType, flow: MIRType}[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        const etypes = ttypes.map((tt) => {
            return { layout: tt.layout.trkey, flow: tt.flow.trkey };
        });
        this.m_currentBlock.push(new MIRStructuredJoinRecord(sinfo, resultRecordType.trkey, args, etypes, trgt));
    }

    emitConstructorValueList(sinfo: SourceInfo, resultEphemeralType: MIRType, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorEphemeralList(sinfo, resultEphemeralType.trkey, args, trgt));
    }

    emitMIRPackExtend(sinfo: SourceInfo, basepack: MIRArgument, basetype: MIRType, ext: MIRArgument[], sltype: MIRType, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIREphemeralListExtend(sinfo, basepack, basetype.trkey, ext, sltype.trkey, trgt));
    }

    emitConstructorPrimaryCollectionEmpty(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt));
    }

    emitConstructorPrimaryCollectionSingletons(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionSingletons(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionCopies(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionCopies(sinfo, tkey, args, trgt));
    }

    emitConstructorPrimaryCollectionMixed(sinfo: SourceInfo, tkey: MIRResolvedTypeKey, args: [boolean, MIRArgument][], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }
        
        this.m_currentBlock.push(new MIRConstructorPrimaryCollectionMixed(sinfo, tkey, args, trgt));
    }

    emitBinKeyEq(sinfo: SourceInfo, lhslayouttype: MIRType, lhsflowtype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhsflowtype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyEq(sinfo, lhslayouttype.trkey, lhsflowtype.trkey, lhs, rhslayouttype.trkey, rhsflowtype.trkey, rhs, trgt));
    }

    emitBinKeyLess(sinfo: SourceInfo, lhslayouttype: MIRType, lhsflowtype: MIRType, lhs: MIRArgument, rhslayouttype: MIRType, rhsflowtype: MIRType, rhs: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRBinKeyLess(sinfo, lhslayouttype.trkey, lhsflowtype.trkey, lhs, rhslayouttype.trkey, rhsflowtype.trkey, rhs, trgt));
    }

    emitPrefixNotOp(sinfo: SourceInfo, arg: MIRArgument, trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRPrefixNotOp(sinfo, arg, trgt));
    }

    emitAllTrue(sinfo: SourceInfo, args: MIRArgument[], trgt: MIRTempRegister) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRAllTrue(sinfo, args, trgt));
    }
    
    emitTypeOf(sinfo: SourceInfo, trgt: MIRTempRegister, chktype: MIRType, src: MIRArgument, srclayouttype: MIRType, srcflowtype: MIRType, guard: MIRGuard | undefined) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRIsTypeOf(sinfo, trgt, chktype.trkey, src, srclayouttype.trkey, srcflowtype.trkey, guard));
    }

    emitDirectJump(sinfo: SourceInfo, blck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJump(sinfo, blck));
    }

    emitBoolJump(sinfo: SourceInfo, arg: MIRTempRegister, trueblck: string, falseblck: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpCond(sinfo, arg, trueblck, falseblck));
    }

    emitNoneJump(sinfo: SourceInfo, arg: MIRTempRegister, noneblck: string, someblk: string, ) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRJumpNone(sinfo, arg, noneblck, someblk));
    }

    emitReturnAssign(sinfo: SourceInfo, src: MIRArgument, rtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssign(sinfo, src));
    }

    emitReturnAssignOfCons(sinfo: SourceInfo, oftype: MIRType, args: MIRArgument[]) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRReturnAssignOfCons(sinfo, oftype.trkey, args));
    }

    processEnterYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.push([]);
    }

    getActiveYieldSet(): [string, MIRTempRegister, ValueType][] {
        return this.emitEnabled ? this.yieldPatchInfo[this.yieldPatchInfo.length - 1] : [];
    }

    processExitYield() {
        if(!this.emitEnabled) {
            return;
        }

        this.yieldPatchInfo.pop();
    }

    getActiveReturnSet(): [string, MIRTempRegister, ValueType][] {
        return this.emitEnabled ? this.returnPatchInfo : [];
    }


    localLifetimeStart(sinfo: SourceInfo, name: string, vtype: MIRType) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRVarLifetimeStart(sinfo, name, vtype.trkey));
    }

    localLifetimeEnd(sinfo: SourceInfo, name: string) {
        if(!this.emitEnabled) {
            return;
        }

        this.m_currentBlock.push(new MIRVarLifetimeEnd(sinfo, name));
    }

    getBody(file: string, sinfo: SourceInfo, args: Map<string, MIRType>): MIRBody | undefined {
        if(!this.emitEnabled) {
            return undefined;
        }

        let ibody = new MIRBody(file, sinfo, this.m_blockMap);

        propagateTmpAssignForBody(ibody);
        removeDeadTempAssignsFromBody(ibody);

        convertBodyToSSA(ibody, args);

        return ibody;
    }

    getVCallInstantiations(assembly: Assembly): [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] | undefined {
        if (this.allVInvokes.length === 0) {
            return undefined;
        }

        let resvi = new Map<string, [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]]>();
        for (let i = 0; i < this.allVInvokes.length; ++i) {
            const vinv = this.allVInvokes[i];

            const vcpt = ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(vinv[2] as ConceptTypeDecl, vinv[3])]));
            const impls = this.entityInstantiationInfo.filter((iinfo) => {
                if (iinfo[1] instanceof EntityTypeDecl) {
                    const etype = ResolvedType.createSingle(ResolvedEntityAtomType.create(iinfo[1] as EntityTypeDecl, iinfo[2]));
                    return assembly.subtypeOf(etype, vcpt);
                }
                else {
                    const cpt = ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(iinfo[1] as ConceptTypeDecl, iinfo[2])]);
                    const ctype = ResolvedType.createSingle(cpt);
                    return assembly.subtypeOf(ctype, vcpt);
                }
            });

            for (let j = 0; j < impls.length; ++j) {
                const impl = impls[j];
                const itype = ResolvedType.createSingle(ResolvedEntityAtomType.create(impl[1] as EntityTypeDecl, impl[2]));

                const mcreate = assembly.tryGetOOMemberDeclUnique(itype, "method", vinv[4]);
                if (mcreate !== undefined) {
                    const binds = new Map<string, ResolvedType>(mcreate.binds);
                    vinv[5].forEach((v, k) => binds.set(k, v));

                    const mkey = MIRKeyGenerator.generateMethodKey(mcreate.contiainingType, (mcreate.decl as MemberMethodDecl).name, mcreate.binds, vinv[6]);
                    if (!resvi.has(mkey)) {
                        resvi.set(mkey, [vinv[0], mkey, mcreate.contiainingType, mcreate.binds, mcreate.decl as MemberMethodDecl, binds as Map<string, ResolvedType>, vinv[6], vinv[7]]);
                    }
                }
            }
        }

        let fres: [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
        resvi.forEach((v, k) => fres.push(v));

        return fres;
    }

    private registerTypeInstantiation(rtype: ResolvedType, decl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if(!this.emitEnabled) {
            return;
        }

        const key = MIRKeyGenerator.generateTypeKey(rtype);
        if (this.masm.conceptDecls.has(key) || this.masm.entityDecls.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }

        if (decl.ns === "NSCore" && decl.name === "Result") {    
            const okdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Ok") as EntityTypeDecl;
            const okkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(okdecl, binds)));
            if (!this.masm.entityDecls.has(okkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === okkey) === -1) {
                this.pendingOOProcessing.push([okkey, okdecl, binds]);
                this.entityInstantiationInfo.push([okkey, okdecl, binds]);
            }

            const errdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Result::Err") as EntityTypeDecl;
            const errkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(ResolvedEntityAtomType.create(errdecl, binds)));
            if (!this.masm.entityDecls.has(errkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === errkey) === -1) {
                this.pendingOOProcessing.push([errkey, errdecl, binds]);
                this.entityInstantiationInfo.push([errkey, errdecl, binds]);
            }
        }

        this.pendingOOProcessing.push([key, decl, binds]);
        this.entityInstantiationInfo.push([key, decl, binds]);
    }

    registerResolvedTypeReference(t: ResolvedType): MIRType {
        if (t.options.length > 1) {
            const oopts = t.options.map((opt) => this.registerResolvedTypeReference(ResolvedType.createSingle(opt)).options);
            const ft = MIRType.create(([] as MIRTypeOption[]).concat(...oopts));

            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.trkey, ft);
            }

            return ft;
        }
        else {
            const sopt = t.options[0];
            const rtt = ResolvedType.createSingle(sopt);
            let rt: MIRTypeOption | undefined = undefined;

            if (sopt instanceof ResolvedEntityAtomType) {
                this.registerTypeInstantiation(rtt, sopt.object, sopt.binds);
                rt = MIREntityType.create(MIRKeyGenerator.generateTypeKey(rtt));
            }
            else if (sopt instanceof ResolvedConceptAtomType) {
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(rtt, cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(rtt);
                });
                rt = MIRConceptType.create(natoms);
            }
            else if (sopt instanceof ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => new MIRTupleTypeEntry(this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRTupleType.create(sopt.isvalue, sopt.grounded, tatoms);
                if(!this.masm.tupleDecls.has(rt.trkey)) {
                    this.masm.tupleDecls.set(rt.trkey, rt as MIRTupleType);
                }
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRRecordType.create(sopt.isvalue, sopt.grounded, tatoms);
                if(!this.masm.recordDecls.has(rt.trkey)) {
                    this.masm.recordDecls.set(rt.trkey, rt as MIRRecordType);
                }
            }
            else if(sopt instanceof ResolvedLiteralAtomType) {
                const 
                rt = MIRLiteralType.create(sopt.idStr, sopt.ofvalue);
                if(!this.masm.literalTypes.has(rt.trkey)) {
                    this.masm.literalTypes.set(rt.trkey, rt as MIRLiteralType);
                }
            }
            else {
                const vpatoms = (sopt as ResolvedEphemeralListType).types.map((tt) => this.registerResolvedTypeReference(tt));
                rt = MIREphemeralListType.create(vpatoms);
                if(!this.masm.ephemeralListDecls.has(rt.trkey)) {
                    this.masm.ephemeralListDecls.set(rt.trkey, rt as MIREphemeralListType);
                }
            }

            const ft = MIRType.create([(rt as MIRTypeOption)]);
            if(this.emitEnabled) {
                this.masm.typeMap.set(ft.trkey, ft);
            }

            return ft;
        }
    }

    registerPendingGlobalProcessing(decl: NamespaceConstDecl, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`global@${decl.ns}`, decl.name, new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, decl.srcFile, decl.name, undefined, decl.value, ["static_initializer", ...decl.attributes], new Map<string, ResolvedType>(), etype]);
        return gkey;
    }

    registerPendingConstProcessing(containingtype: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], decl: StaticMemberDecl, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`static@${containingtype[0].trkey}`, decl.name, new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, decl.srcFile, decl.name, containingtype, decl.value as ConstantExpressionValue, ["static_initializer", ...decl.attributes], binds, etype]);
        return gkey;
    }

    registerConstExpr(srcFile: string, exp: ConstantExpressionValue, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`cexpr@${srcFile}#${exp.exp.sinfo.pos}`, "expr", new Map<string, ResolvedType>(), []);
        const gkey = "$global_" + key;
        if (!this.emitEnabled || this.masm.constantDecls.has(gkey) || this.pendingConstExprProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, srcFile, "[CONST]", undefined, exp, ["constexp_initializer"], binds, etype]);
        return gkey;
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f.name, name, undefined, f.invoke, binds, pcodes, cinfo]);
        return key;
    }

    registerNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, sigkeys: string[], pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, new Map<string, ResolvedType>(), pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOperatorProcessing.findIndex((fp) => fp[0] === okey) !== -1) {
            return key;
        }

        this.pendingOperatorProcessing.push([okey, opdecl.name, name, undefined, opdecl.invoke, new Map<string, ResolvedType>(), pcodes, cinfo]);
        return okey;
    }

    registerStaticCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(containingType[0].trkey, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f.name, name, containingType, f.invoke, binds, pcodes, cinfo]);
        return key;
    }

    registerStaticOperatorCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], name: string, opdecl: StaticOperatorDecl, sigkeys: string[], binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(containingType[0].trkey, name, binds, pcodes);
        const okey = MIRKeyGenerator.generateOperatorSignatureKey(key, opdecl.isPrefix, opdecl.isInfix, sigkeys);

        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOperatorProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }

        this.pendingOperatorProcessing.push([okey, opdecl.name, name, containingType, opdecl.invoke, binds, pcodes, cinfo]);
        return key;
    }

    registerMethodCall(containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], m: MemberMethodDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        const key = MIRKeyGenerator.generateMethodKey(name, containingType[0].trkey, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[1] === key) !== -1) {
            return key;
        }

        this.pendingOOMethodProcessing.push([vkey, key, m.name, name, containingType, m, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualMethodCall(containingType: ResolvedType, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds, pcodes);
        const tkey = containingType.idStr;
        if (!this.emitEnabled || this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return key;
        }

        this.allVInvokes.push([key, tkey, containingType, name, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${ns}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.allVOPInvokes.findIndex((vi) => vi[0] === key) !== -1) {
            return key;
        }

        this.allVOPInvokes.push([key, ns, undefined, name, new Map<string, ResolvedType>(), pcodes, cinfo]);
        return key;
    }

    registerVirtualStaticOperatorCall(containingType: ResolvedType, name: string, opdecl: StaticOperatorDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(`${containingType.idStr}::${name}`, new Map<string, ResolvedType>(), pcodes);
        if (!this.emitEnabled || this.allVOPInvokes.findIndex((vi) => vi[0] === key) !== -1) {
            return key;
        }

        this.allVOPInvokes.push([key, undefined, containingType, name, new Map<string, ResolvedType>(), pcodes, cinfo]);
        return key;
    }

    registerPCode(idecl: InvokeDecl, fsig: ResolvedFunctionType, binds: Map<string, ResolvedType>, cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generatePCodeKey(idecl);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingPCodeProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingPCodeProcessing.push([key, idecl, fsig, binds, cinfo]);
        return key;
    }

    registerTupleProjectToEphemeralVirtual(tt: ValueType, indecies: number[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        const idxname = indecies.map((idx) => `${idx}`).join(", ");
        const vname = `$TupleProject_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${idxname})%%${this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey}`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allTupleVirtualProject.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allTupleVirtualProject.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, indecies: indecies, reph: this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey });
        return key;
    }

    registerRecordProjectToEphemeralVirtual(tt: ValueType, properties: string[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        const pnames = properties.join(", ");
        const vname = `$RecordProject_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${pnames})%%${this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey}`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allRecordVirtualProject.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allRecordVirtualProject.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, properties: properties, reph: this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey });
        return key;
    }

    registerOOTypeProjectToEphemeralVirtual(tt: ValueType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        const fnames = fields.join(", ");
        const vname = `$EntityProject_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${fnames})%%${this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey}`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allEntityVirtualProject.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allEntityVirtualProject.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, fields: fields, reph: this.registerResolvedTypeReference(ResolvedType.createSingle(epht)).trkey });
        return key;
    }

    registerTupleUpdateVirtual(tt: ValueType, updates: [number, ResolvedType][]): MIRVirtualMethodKey {
        const idxname = updates.map((udp) => `${udp[0]} ${this.registerResolvedTypeReference(udp[1]).trkey}`).join(", ");
        const vname = `$TupleUpdate_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${idxname})`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allTupleVirtualUpdate.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allTupleVirtualUpdate.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, updates: updates.map((upd) => [upd[0], this.registerResolvedTypeReference(upd[1]).trkey]) });
        return key;
    }

    registerRecordUpdateVirtual(tt: ValueType, updates: [string, ResolvedType][]): MIRVirtualMethodKey {
        const pname = updates.map((udp) => `${udp[0]} ${this.registerResolvedTypeReference(udp[1]).trkey}`).join(", ");
        const vname = `$RecordUpdate_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${pname})`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allRecordVirtualUpdate.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allRecordVirtualUpdate.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, updates: updates.map((upd) => [upd[0], this.registerResolvedTypeReference(upd[1]).trkey]) });
        return key;
    }

    registerOOTypeUpdateVirtual(tt: ValueType, updates: [MIRFieldKey, ResolvedType][]): MIRVirtualMethodKey {
        const fname = updates.map((udp) => `${udp[0]} ${this.registerResolvedTypeReference(udp[1]).trkey}`).join(", ");
        const vname = `$EntityUpdate_${this.registerResolvedTypeReference(tt.layout).trkey}##${this.registerResolvedTypeReference(tt.flowtype).trkey}(${fname})`;

        const key = MIRKeyGenerator.generateVirtualMethodKey(vname, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.allEntityVirtualUpdate.findIndex((vi) => vi.vkey === key) !== -1) {
            return key;
        }

        this.masm.allEntityVirtualUpdate.push({vkey: key, layouttype: this.registerResolvedTypeReference(tt.layout).trkey, flowtype: this.registerResolvedTypeReference(tt.flowtype).trkey, updates: updates.map((upd) => [upd[0], this.registerResolvedTypeReference(upd[1]).trkey]) });
        return key;
    }

    static generateMASM(pckge: PackageConfig, buildLevel: BuildLevel, entrypoints: { namespace: string, names: string[] }, functionalize: boolean, srcFiles: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
        ////////////////
        //Parse the contents and generate the assembly
        const assembly = new Assembly();
        let p = new Parser(assembly);
        try {
            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass1(srcFiles[i].relativePath, srcFiles[i].contents);
            }

            for (let i = 0; i < srcFiles.length; ++i) {
                p.parseCompilationUnitPass2(srcFiles[i].relativePath, srcFiles[i].contents);
            }
        }
        catch (ex) {
            return { masm: undefined, errors: [`Hard failure in parse with exception -- ${ex}`] };
        }

        const parseErrors = p.getParseErrors();
        if (parseErrors !== undefined) {
            return { masm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)) };
        }

        ////////////////
        //Compute the assembly hash and initialize representations
        const hash = Crypto.createHash("sha512");
        const data = [...srcFiles].sort((a, b) => a.relativePath.localeCompare(b.relativePath));
        data.forEach((sf) => {
            hash.update(sf.relativePath);
            hash.update(sf.contents);
        });

        const masm = new MIRAssembly(pckge, srcFiles, hash.digest("hex"));
        const emitter = new MIREmitter(assembly, masm, true);
        const checker = new TypeChecker(assembly, emitter, buildLevel);

        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialPODTypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPIValueConceptType());
        emitter.registerResolvedTypeReference(assembly.getSpecialObjectConceptType());

        emitter.registerResolvedTypeReference(assembly.getSpecialNoneType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBoolType());
        emitter.registerResolvedTypeReference(assembly.getSpecialIntType());
        emitter.registerResolvedTypeReference(assembly.getSpecialNatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigIntType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigNatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRationalType());
        emitter.registerResolvedTypeReference(assembly.getSpecialComplexType());
        emitter.registerResolvedTypeReference(assembly.getSpecialFloatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialDecimalType());
        emitter.registerResolvedTypeReference(assembly.getSpecialStringType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferFormatType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferEncodingType());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerResolvedTypeReference(assembly.getSpecialCryptoHashType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexMatchType());

        //get any entrypoint functions and initialize the checker there
        const epns = assembly.getNamespace(entrypoints.namespace);
        if (epns === undefined) {
            return { masm: undefined, errors: [`Could not find namespace ${entrypoints.namespace}`] };
        }
        else {
            if(entrypoints.names.length === 0) {
                return { masm: undefined, errors: ["No entrypoints specified"] };
            }

            for(let i = 0; i < entrypoints.names.length; ++i) {
                const f = epns.functions.get(entrypoints.names[i]);
                if(f === undefined) {
                    return { masm: undefined, errors: [`Could not find function ${entrypoints.names[i]}`] };
                }

                emitter.registerFunctionCall(f.ns, f.name, f, new Map<string, ResolvedType>(), [], []);
            }
        }

        ////////////////
        //While there is more to process get an item and run the checker on it
        try {
            let lastVCount = 0;
            let lastVOPCount = 0;
            while (true) {
                while (emitter.pendingOOProcessing.length !== 0 || emitter.pendingConstExprProcessing.length !== 0
                    || emitter.pendingFunctionProcessing.length !== 0 || emitter.pendingOperatorProcessing.length !== 0 
                    || emitter.pendingOOMethodProcessing.length !== 0 || emitter.pendingPCodeProcessing.length !== 0) {

                    while (emitter.pendingOOProcessing.length !== 0) {
                        const tt = emitter.pendingOOProcessing.pop() as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
                        checker.processOOType(...tt);
                    }

                    if(emitter.pendingConstExprProcessing.length !== 0) {
                        const pc = emitter.pendingConstExprProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, ConstantExpressionValue, string[], Map<string, ResolvedType>, ResolvedType];
                        checker.processConstExpr(...pc);
                    }
                    else if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processFunctionDecl(...pf);
                    }
                    else if (emitter.pendingOperatorProcessing.length !== 0) {
                        const pf = emitter.pendingOperatorProcessing.pop() as [MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, InvokeDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processFunctionDecl(...pf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop() as [MIRVirtualMethodKey, MIRInvokeKey, string, string, [MIRType, OOPTypeDecl, Map<string, ResolvedType>], MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processMethodFunction(...mf);
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing.pop() as [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]];
                        checker.processLambdaFunction(...lf);
                    }
                    else {
                        ;
                    }
                }

                //make sure all vcall candidates are processed
                const vcgens = emitter.getVCallInstantiations(assembly);
                const vopgens = emitter.getVOPCallInstantiations(assembly);
                if ((vcgens === undefined || vcgens.length === lastVCount) && (vopgens === undefined || vopgens.length === lastVOPCount)) {
                    break;
                }
                lastVCount = vcgens.length;
                lastVOPCount = 

                for (let i = 0; i < vcgens.length; ++i) {
                    checker.processMethodFunction(...vcgens[i]);
                }
            }

            if (checker.getErrorList().length === 0) {
                checker.processRegexInfo();

                masm.invokeDecls.forEach((idecl) => {
                    const args = new Map<string, MIRType>();
                    idecl.params.forEach((param) => args.set(param.name, masm.typeMap.get(param.type) as MIRType));
                    computeVarTypesForInvoke(idecl.body, args, masm.typeMap.get(idecl.resultType) as MIRType, masm);
                });

                if (functionalize) {
                    functionalizeInvokes(masm);
                }
            }
        }
        catch (ex) {
            //ignore
        }

        const tcerrors = checker.getErrorList();
        if (tcerrors.length !== 0) {
            return { masm: undefined, errors: tcerrors.map((err: [string, number, string]) => JSON.stringify(err)) };
        }
        else {
            return { masm: masm, errors: [] };
        }
    }
}

export { PCode, MIRKeyGenerator, MIREmitter };
