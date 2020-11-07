//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { SourceInfo, Parser } from "../ast/parser";
import { MIRAbort, MIRAllTrue, MIRArgument, MIRAssertCheck, MIRBasicBlock, MIRBinKeyEq, MIRBinKeyLess, MIRBody, MIRCheckNoError, MIRConstantBigInt, MIRConstantBigNat, MIRConstantComplex, MIRConstantDecmial, MIRConstantFalse, MIRConstantFloat, MIRConstantInt, MIRConstantNat, MIRConstantNone, MIRConstantRational, MIRConstantRegex, MIRConstantString, MIRConstantStringOf, MIRConstantTrue, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionEmpty, MIRConstructorPrimaryCollectionMixed, MIRConstructorPrimaryCollectionSingletons, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConvertValue, MIRDeadFlow, MIRDebug, MIRDeclareGuardFlagLocation, MIREphemeralListExtend, MIRExtractResultOkValue, MIRFieldKey, MIRGuard, MIRInvokeFixedFunction, MIRInvokeKey, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRIsTypeOf, MIRJump, MIRJumpCond, MIRJumpNone, MIRLoadConst, MIRLoadConstDataString, MIRLoadField, MIRLoadFromEpehmeralList, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRLocalVarStore, MIRMultiLoadFromEpehmeralList, MIRNop, MIROp, MIRParameterVariable, MIRParameterVarStore, MIRPrefixNotOp, MIRRecordHasProperty, MIRRegisterArgument, MIRResolvedTypeKey, MIRReturnAssign, MIRReturnAssignOfCons, MIRSetConstantGuardFlag, MIRSliceEpehmeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRTempRegister, MIRTempRegisterAssign, MIRTupleHasIndex, MIRVarLifetimeEnd, MIRVarLifetimeStart, MIRVirtualMethodKey } from "./mir_ops";
import { Assembly, InvokeDecl } from "../ast/assembly";
import { ResolvedFunctionType, ResolvedType } from "../ast/resolved_type";
import { MIRAssembly, MIREphemeralListType, MIRType } from "./mir_assembly";

import { TypeChecker } from "../type_checker/type_checker";
import { propagateTmpAssignForBody, removeDeadTempAssignsFromBody } from "./mir_cleanup";
import { convertBodyToSSA } from "./mir_ssa";
import { computeVarTypesForInvoke } from "./mir_vartype";
import { functionalizeInvokes } from "./functionalize";
import { BSQRegex } from "../ast/bsqregex";
import { ConstantExpressionValue } from "../ast/body";
import { ValueType } from "../type_checker/type_environment";

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

    static generateMethodKey(name: string, t: ResolvedType, binds: Map<string, ResolvedType>, pcodes: PCode[]): MIRInvokeKey {
        return `${this.generateTypeKey(t)}::${name}${MIRKeyGenerator.computeBindsKeyInfo(binds)}${MIRKeyGenerator.computePCodeKeyInfo(pcodes)}`;
    }

    static generateVirtualMethodKey(vname: string, binds: Map<string, ResolvedType>): MIRVirtualMethodKey {
        return `${vname}${MIRKeyGenerator.computeBindsKeyInfo(binds)}`;
    }

    static generatePCodeKey(inv: InvokeDecl): MIRInvokeKey {
        return `fn--${inv.srcFile}+${inv.sourceLocation.line}##${inv.sourceLocation.pos}`;
    }
}

class MIREmitter {
    readonly assembly: Assembly;
    readonly masm: MIRAssembly;
    
    private readonly pendingOOProcessing: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingGlobalProcessing: [MIRConstantKey, NamespaceConstDecl][] = [];
    private readonly pendingConstProcessing: [MIRConstantKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>][] = [];

    private readonly pendingOOStaticProcessing: [MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, StaticFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingOOMethodProcessing: [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingFunctionProcessing: [MIRInvokeKey, NamespaceFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];
    private readonly pendingPCodeProcessing: [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]][] = [];

    private readonly entityInstantiationInfo: [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>][] = [];
    private readonly allVInvokes: [MIRVirtualMethodKey, MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>, string, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]][] = [];

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

    private registerTypeInstantiation(decl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if(!this.emitEnabled) {
            return;
        }

        const key = MIRKeyGenerator.generateTypeKey(decl, binds);
        if (this.masm.conceptDecls.has(key) || this.masm.entityDecls.has(key) || this.pendingOOProcessing.findIndex((oop) => oop[0] === key) !== -1) {
            return;
        }

        if (decl.ns === "NSCore" && decl.name === "Result") {    
            const okdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Ok") as EntityTypeDecl;
            const okkey = MIRKeyGenerator.generateTypeKey(okdecl, binds);
            if (!this.masm.entityDecls.has(okkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === okkey) === -1) {
                this.pendingOOProcessing.push([okkey, okdecl, binds]);
                this.entityInstantiationInfo.push([okkey, okdecl, binds]);
            }

            const errdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Err") as EntityTypeDecl;
            const errkey = MIRKeyGenerator.generateTypeKey(errdecl, binds);
            if (!this.masm.entityDecls.has(errkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === errkey) === -1) {
                this.pendingOOProcessing.push([errkey, errdecl, binds]);
                this.entityInstantiationInfo.push([errkey, errdecl, binds]);
            }
        }

        if (decl.ns === "NSCore" && decl.name === "Option") {
            const optdecl = this.assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Opt") as EntityTypeDecl;
            const optkey = MIRKeyGenerator.generateTypeKey(optdecl, binds);
            if (!this.masm.entityDecls.has(optkey) && this.pendingOOProcessing.findIndex((oop) => oop[0] === optkey) === -1) {
                this.pendingOOProcessing.push([optkey, optdecl, binds]);
                this.entityInstantiationInfo.push([optkey, optdecl, binds]);
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
            let rt: MIRTypeOption | undefined = undefined;

            if (sopt instanceof ResolvedEntityAtomType) {
                this.registerTypeInstantiation(sopt.object, sopt.binds);
                rt = MIREntityType.create(MIRKeyGenerator.generateTypeKey(sopt.object, sopt.binds));
            }
            else if (sopt instanceof ResolvedConceptAtomType) {
                const natoms = sopt.conceptTypes.map((cpt) => {
                    this.registerTypeInstantiation(cpt.concept, cpt.binds);
                    return MIRKeyGenerator.generateTypeKey(cpt.concept, cpt.binds);
                });
                rt = MIRConceptType.create(natoms);
            }
            else if (sopt instanceof ResolvedTupleAtomType) {
                const tatoms = sopt.types.map((entry) => new MIRTupleTypeEntry(this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRTupleType.create(tatoms);
                if(!this.masm.tupleDecls.has(rt.trkey)) {
                    this.masm.tupleDecls.set(rt.trkey, rt as MIRTupleType);
                }
            }
            else if (sopt instanceof ResolvedRecordAtomType) {
                const tatoms = sopt.entries.map((entry) => new MIRRecordTypeEntry(entry.name, this.registerResolvedTypeReference(entry.type), entry.isOptional));
                rt = MIRRecordType.create(tatoms);
                if(!this.masm.recordDecls.has(rt.trkey)) {
                    this.masm.recordDecls.set(rt.trkey, rt as MIRRecordType);
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

    registerPendingGlobalProcessing(decl: NamespaceConstDecl): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`global@${decl.ns}`, decl.name, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingGlobalProcessing.findIndex((gp) => gp[0] === key) !== -1) {
            return key;
        }

        this.pendingGlobalProcessing.push([key, decl]);
        return key;
    }

    registerPendingConstProcessing(mircontaining: MIRType, containingType: OOPTypeDecl, decl: StaticMemberDecl, binds: Map<string, ResolvedType>): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`static@${mircontaining.trkey}`, decl.name, new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstProcessing.push([key, containingType, decl, binds]);
        return key;
    }

    registerConstExpr(srcFile: string, exp: ConstantExpressionValue, binds: Map<string, ResolvedType>, etype: ResolvedType): MIRGlobalKey {
        const key = MIRKeyGenerator.generateFunctionKey(`cexpr@${srcFile}#${exp.exp.sinfo.pos}`, "expr", new Map<string, ResolvedType>(), []);
        if (!this.emitEnabled || this.masm.constantDecls.has(key) || this.pendingConstProcessing.findIndex((cp) => cp[0] === key) !== -1) {
            return key;
        }

        this.pendingConstExprProcessing.push([key, exp, binds, etype]);
        return key;
    }

    registerFunctionCall(ns: string, name: string, f: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateFunctionKey(ns, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingFunctionProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingFunctionProcessing.push([key, f, binds, pcodes, cinfo]);
        return key;
    }

    registerNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        xxxx;
    }

    registerStaticOperatorCall(containingType: OOPTypeDecl, name: string, opdecl: StaticOperatorDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        xxxx;
    }

    registerStaticCall(containingType: OOPTypeDecl, cbinds: Map<string, ResolvedType>, f: StaticFunctionDecl, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generateStaticKey(containingType, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOStaticProcessing.findIndex((sp) => sp[0] === key) !== -1) {
            return key;
        }

        this.pendingOOStaticProcessing.push([key, containingType, cbinds, f, binds, pcodes, cinfo]);
        return key;
    }

    registerMethodCall(containingType: OOPTypeDecl, m: MemberMethodDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const vkey = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const key = MIRKeyGenerator.generateMethodKey(containingType, name, binds, pcodes);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingOOMethodProcessing.findIndex((mp) => mp[1] === key) !== -1) {
            return key;
        }

        this.pendingOOMethodProcessing.push([vkey, key, containingType, cbinds, m, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualMethodCall(containingType: OOPTypeDecl, cbinds: Map<string, ResolvedType>, name: string, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        const key = MIRKeyGenerator.generateVirtualMethodKey(name, binds);
        const tkey = MIRKeyGenerator.generateTypeKey(containingType, binds);
        if (!this.emitEnabled || this.allVInvokes.findIndex((vi) => vi[0] === key && vi[1] === tkey) !== -1) {
            return key;
        }

        this.allVInvokes.push([key, tkey, containingType, cbinds, name, binds, pcodes, cinfo]);
        return key;
    }

    registerVirtualNamespaceOperatorCall(ns: string, name: string, opdecl: NamespaceOperatorDecl, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerVirtualStaticOperatorCall(containingType: OOPTypeDecl, name: string, opdecl: StaticOperatorDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cinfo: [string, ResolvedType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerPCode(idecl: InvokeDecl, fsig: ResolvedFunctionType, binds: Map<string, ResolvedType>, cinfo: [string, ResolvedType][]): MIRInvokeKey {
        const key = MIRKeyGenerator.generatePCodeKey(idecl);
        if (!this.emitEnabled || this.masm.invokeDecls.has(key) || this.masm.primitiveInvokeDecls.has(key) || this.pendingPCodeProcessing.findIndex((fp) => fp[0] === key) !== -1) {
            return key;
        }

        this.pendingPCodeProcessing.push([key, idecl, fsig, binds, cinfo]);
        return key;
    }

    registerTupleProjectToEphemeral(tt: ResolvedTupleAtomType, indecies: number[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerTupleProjectToEphemeralVirtual(tt: ValueType, indecies: number[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerRecordProjectToEphemeral(tt: ResolvedRecordAtomType, properties: string[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerRecordProjectToEphemeralVirtual(tt: ValueType, properties: string[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerEntityProjectToEphemeral(tt: ResolvedEntityAtomType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType): MIRInvokeKey {
        xxxx;
    }

    registerOOTypeProjectToEphemeralVirtual(tt: ValueType, fields: MIRFieldKey[], epht: ResolvedEphemeralListType): MIRVirtualMethodKey {
        xxxx;
    }

    registerTupleUpdate(tt: ResolvedTupleAtomType, updates: [number, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerTupleUpdateVirtual(tt: ValueType, updates: [number, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerRecordUpdate(tt: ResolvedRecordAtomType, updates: [string, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerRecordUpdateVirtual(tt: ValueType, updates: [string, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    registerEntityUpdate(tt: ResolvedEntityAtomType, updates: [MIRFieldKey, MIRType][]): MIRInvokeKey {
        xxxx;
    }

    registerOOTypeUpdateVirtual(tt: ValueType, updates: [MIRFieldKey, MIRType][]): MIRVirtualMethodKey {
        xxxx;
    }

    private closeConceptDecl( cpt: MIRConceptTypeDecl) {
        cpt.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!cpt.vcallMap.has(vcname)) {
                    cpt.vcallMap.set(vcname, vcall);
                }
            });
        });
    }

    private closeEntityDecl(entity: MIREntityTypeDecl) {
        entity.provides.forEach((tkey) => {
            const ccdecl = this.masm.conceptDecls.get(tkey) as MIRConceptTypeDecl;
            this.closeConceptDecl(ccdecl);

            ccdecl.vcallMap.forEach((vcall, vcname) => {
                if (!entity.vcallMap.has(vcname)) {
                    entity.vcallMap.set(vcname, vcall);
                }
            });
        });
    }

    static generateMASM(pckge: PackageConfig, buildLevel: BuildLevel, validateLiteralStrings: boolean, functionalize: boolean, srcFiles: { relativePath: string, contents: string }[]): { masm: MIRAssembly | undefined, errors: string[] } {
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
        const emitter = new MIREmitter(assembly, masm);
        const checker = new TypeChecker(assembly, true, emitter, buildLevel, validateLiteralStrings);

        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Any") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAnyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Some") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialSomeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Parsable") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialParsableConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Validator") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialValidatorConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::KeyType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialKeyTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::PODType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialPODTypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIType") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPITypeConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::APIValue") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialAPIValueConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Truthy") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialTruthyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Enum") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialEnumConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::IdKey") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialIdKeyConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Tuple") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialTupleConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Record") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialRecordConceptType());
        emitter.registerTypeInstantiation(assembly.tryGetConceptTypeForFullyResolvedName("NSCore::Object") as ConceptTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialObjectConceptType());

        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::None") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialNoneType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Bool") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBoolType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Int") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BigInt") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBigIntType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Float64") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialFloat64Type());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::String") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialStringType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferFormat") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferFormatType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferEncoding") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferEncodingType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::BufferCompression") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialBufferCompressionType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ByteBuffer") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialByteBufferType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::ISOTime") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialISOTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::UUID") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialUUIDType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::LogicalTime") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialLogicalTimeType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::CryptoHash") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialCryptoHashType());
        emitter.registerTypeInstantiation(assembly.tryGetObjectTypeForFullyResolvedName("NSCore::Regex") as EntityTypeDecl, new Map<string, ResolvedType>());
        emitter.registerResolvedTypeReference(assembly.getSpecialRegexType());

        //get any entrypoint functions and initialize the checker there
        const nslist = assembly.getNamespaces();
        nslist.forEach((nsentry) => {
            nsentry.functions.forEach((f) => {
                if (f.attributes.indexOf("entrypoint") !== -1) {
                    emitter.registerFunctionCall(f.ns, f.name, f, new Map<string, ResolvedType>(), [], []);
                }
            });
        });

        ////////////////
        //While there is more to process get an item and run the checker on it
        try {
            let lastVCount = 0;
            while (true) {
                while (emitter.pendingOOProcessing.length !== 0 ||
                    emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0 ||
                    emitter.pendingFunctionProcessing.length !== 0 || emitter.pendingPCodeProcessing.length !== 0 ||
                    emitter.pendingOOStaticProcessing.length !== 0 || emitter.pendingOOMethodProcessing.length !== 0) {

                    while (emitter.pendingOOProcessing.length !== 0) {
                        const tt = emitter.pendingOOProcessing.pop() as [MIRResolvedTypeKey, OOPTypeDecl, Map<string, ResolvedType>];
                        checker.processOOType(...tt);
                    }

                    while (emitter.pendingGlobalProcessing.length !== 0 || emitter.pendingConstProcessing.length !== 0) {
                        if (emitter.pendingGlobalProcessing.length !== 0) {
                            const pg = emitter.pendingGlobalProcessing.pop() as [MIRConstantKey, NamespaceConstDecl];
                            checker.processGlobal(...pg);
                        }
                        if (emitter.pendingConstProcessing.length !== 0) {
                            const pc = emitter.pendingConstProcessing.pop() as [MIRConstantKey, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>];
                            checker.processConst(...pc);
                        }
                    }

                    if (emitter.pendingFunctionProcessing.length !== 0) {
                        const pf = emitter.pendingFunctionProcessing.pop() as [MIRInvokeKey, NamespaceFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processNamespaceFunction(...pf);
                    }
                    else if (emitter.pendingPCodeProcessing.length !== 0) {
                        const lf = emitter.pendingPCodeProcessing.pop() as [MIRInvokeKey, InvokeDecl, ResolvedFunctionType, Map<string, ResolvedType>, [string, ResolvedType][]];
                        checker.processLambdaFunction(...lf);
                    }
                    else if (emitter.pendingOOStaticProcessing.length !== 0) {
                        const sf = emitter.pendingOOStaticProcessing.pop() as [MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, StaticFunctionDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processStaticFunction(...sf);
                    }
                    else if (emitter.pendingOOMethodProcessing.length !== 0) {
                        const mf = emitter.pendingOOMethodProcessing.pop() as [MIRVirtualMethodKey, MIRInvokeKey, OOPTypeDecl, Map<string, ResolvedType>, MemberMethodDecl, Map<string, ResolvedType>, PCode[], [string, ResolvedType][]];
                        checker.processMethodFunction(...mf);
                    }
                    else {
                        //nop
                    }
                }

                //make sure all vcall candidates are processed
                const vcgens = emitter.getVCallInstantiations(assembly);
                if (vcgens === undefined || vcgens.length === lastVCount) {
                    break;
                }
                lastVCount = vcgens.length;

                for (let i = 0; i < vcgens.length; ++i) {
                    checker.processMethodFunction(...vcgens[i]);
                }
            }

            if (checker.getErrorList().length === 0) {
                checker.processRegexInfo();
                checker.runFinalExhaustiveChecks();

                //compute closed field and vtable info
                masm.conceptDecls.forEach((cpt) => emitter.closeConceptDecl(cpt));
                masm.entityDecls.forEach((entity) => emitter.closeEntityDecl(entity));

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
