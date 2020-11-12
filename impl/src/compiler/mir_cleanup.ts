//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { MIRArgument, MIRAssertCheck, MIRConvertValue, MIRDebug, MIRGuard, MIRMaskGuard, MIROp, MIROpTag, MIRRegisterArgument, MIRArgGuard, MIRCheckNoError, MIRExtractResultOkValue, MIRLoadConst, MIRTupleHasIndex, MIRRecordHasProperty, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadField, MIRTupleProjectToEphemeral, MIRRecordProjectToEphemeral, MIREntityProjectToEphemeral, MIRTupleUpdate, MIRRecordUpdate, MIREntityUpdate, MIRResolvedTypeKey, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList } from "./mir_ops";

function propagateAssign_Bind(treg: MIRRegisterArgument, arg: MIRArgument, propMap: Map<string, MIRArgument>) {
    assert(!propMap.has(treg.nameID));
    propMap.set(treg.nameID, arg);
}

function propagateAssign_Kill(arg: MIRRegisterArgument, propMap: Map<string, MIRArgument>) {
    let killset = new Set<string>();
    propMap.forEach((v, k) => {
        if (v instanceof MIRRegisterArgument && v.nameID === arg.nameID) {
            killset.add(k);
        }
    });

    killset.forEach((k) => propMap.delete(k));
}

function propagateAssign_Remap(arg: MIRArgument, propMap: Map<string, MIRArgument>): MIRArgument {
    return (arg instanceof MIRRegisterArgument && propMap.has(arg.nameID)) ? propMap.get(arg.nameID) as MIRArgument : arg;
}

function propagateAssign_RemapGuard(arg: MIRGuard | undefined, propMap: Map<string, MIRArgument>): MIRGuard | undefined {
    if(arg === undefined) {
        return arg;
    }
    else if (arg instanceof MIRMaskGuard) {
        return arg;
    }
    else {
        return new MIRArgGuard(propagateAssign_Remap((arg as MIRArgGuard).greg, propMap));
    }
}

function propagateAssign_RemapArgs(args: MIRArgument[], propMap: Map<string, MIRArgument>): MIRArgument[] {
    return args.map((v) => propagateAssign_Remap(v, propMap));
}

function propagateAssign_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function propagateAssignForOp(op: MIROp, propMap: Map<string, MIRArgument>) {
    switch (op.tag) {
        case MIROpTag.MIRNop: 
        case MIROpTag.MIRDeadFlow:
        case MIROpTag.MIRAbort: 
        case MIROpTag.MIRLoadUnintVariableValue: 
        case MIROpTag.MIRDeclareGuardFlagLocation: 
        case MIROpTag.MIRSetConstantGuardFlag:
        case MIROpTag.MIRLoadConstDataString: {
            break;
        }
        case MIROpTag.MIRAssertCheck: {
            const asrt = op as MIRAssertCheck;
            asrt.arg = propagateAssign_Remap(asrt.arg, propMap);
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = propagateAssign_Remap(dbg.value, propMap);
            }
            break;
        }
        case MIROpTag.MIRConvertValue: {
            const conv = op as MIRConvertValue;
            conv.src = propagateAssign_Remap(conv.src, propMap);
            conv.guard = propagateAssign_RemapGuard(conv.guard, propMap);
            break;
        }
        case MIROpTag.MIRCheckNoError: {
            const chk = op as MIRCheckNoError;
            chk.src = propagateAssign_Remap(chk.src, propMap);
            break;
        }
        case MIROpTag.MIRExtractResultOkValue: {
            const erok = op as MIRExtractResultOkValue;
            erok.src = propagateAssign_Remap(erok.src, propMap);
            break;
        }
        case MIROpTag.MIRLoadConst: {
            const lc = op as MIRLoadConst;
            propagateAssign_Bind(lc.trgt, lc.src, propMap);
            break;
        }
        case MIROpTag.MIRTupleHasIndex: {
            const thi = op as MIRTupleHasIndex;
            thi.arg = propagateAssign_Remap(thi.arg, propMap);
            break;
        }
        case MIROpTag.MIRRecordHasProperty: {
            const rhi = op as MIRRecordHasProperty;
            rhi.arg = propagateAssign_Remap(rhi.arg, propMap);
            break;
        }
        case MIROpTag.MIRLoadTupleIndex: {
            const lti = op as MIRLoadTupleIndex;
            lti.arg = propagateAssign_Remap(lti.arg, propMap);
            break;
        }
        case MIROpTag.MIRLoadTupleIndexSetGuard: {
            const ltig = op as MIRLoadTupleIndexSetGuard;
            ltig.arg = propagateAssign_Remap(ltig.arg, propMap);
            ltig.guard = propagateAssign_RemapGuard(ltig.guard, propMap) as MIRGuard;
            break;
        }
        case MIROpTag.MIRLoadRecordProperty: {
            const lrp = op as MIRLoadRecordProperty;
            lrp.arg = propagateAssign_Remap(lrp.arg, propMap);
            break;
        }
        case MIROpTag.MIRLoadRecordPropertySetGuard: {
            const lrpg = op as MIRLoadRecordPropertySetGuard;
            lrpg.arg = propagateAssign_Remap(lrpg.arg, propMap);
            lrpg.guard = propagateAssign_RemapGuard(lrpg.guard, propMap) as MIRGuard;
            break;
        }
        case MIROpTag.MIRLoadField: {
            const lmf = op as MIRLoadField;
            lmf.arg = propagateAssign_Remap(lmf.arg, propMap);
            break;
        }
        case MIROpTag.MIRTupleProjectToEphemeral: {
            const pte = op as MIRTupleProjectToEphemeral;
            pte.arg = propagateAssign_Remap(pte.arg, propMap);
            break;
        }
        case MIROpTag.MIRRecordProjectToEphemeral: {
            const pre = op as MIRRecordProjectToEphemeral;
            pre.arg = propagateAssign_Remap(pre.arg, propMap);
            break;
        }
        case MIROpTag.MIREntityProjectToEphemeral: {
            const pee = op as MIREntityProjectToEphemeral;
            pee.arg = propagateAssign_Remap(pee.arg, propMap);
            break;
        }
        case MIROpTag.MIRTupleUpdate: {
            const mi = op as MIRTupleUpdate;
            mi.arg = propagateAssign_Remap(mi.arg, propMap);
            mi.updates = propagateAssign_RemapStructuredArgs<[number, MIRArgument, MIRResolvedTypeKey]>(mi.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
            break;
        }
        case MIROpTag.MIRRecordUpdate: {
            const mp = op as MIRRecordUpdate;
            mp.arg = propagateAssign_Remap(mp.arg, propMap);
            mp.updates = propagateAssign_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mp.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
            break;
        }
        case MIROpTag.MIREntityUpdate: {
            const mf = op as MIREntityUpdate;
            mf.arg = propagateAssign_Remap(mf.arg, propMap);
            mf.updates = propagateAssign_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mf.updates, (u) => [u[0], propagateAssign_Remap(u[1], propMap), u[2]]);
            break;
        }
        case MIROpTag.MIRLoadFromEpehmeralList: {
            const mle = op as MIRLoadFromEpehmeralList;
            mle.arg = propagateAssign_Remap(mle.arg, propMap);
            break;
        }
        case MIROpTag.MIRMultiLoadFromEpehmeralList: {
            const mle = op as MIRMultiLoadFromEpehmeralList;
            mle.arg = propagateAssign_Remap(mle.arg, propMap);
            break;
        }
        case MIROpTag.MIRSliceEpehmeralList: {
            const mle = op as MIRSliceEpehmeralList;
            mle.arg = propagateAssign_Remap(mle.arg, propMap);
            break;
        }

        case MIROpTag.MIRInvokeFixedFunction: {
            const invk = op as MIRInvokeFixedFunction;
            invk.args = propagateAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case MIROpTag.MIRInvokeVirtualFunction: {
            const invk = op as MIRInvokeVirtualFunction;
            invk.args = propagateAssign_RemapArgs(invk.args, propMap);
            break;
        }
        case MIROpTag.MIRInvokeVirtualOperator: {
            const invk = op as MIRInvokeVirtualOperator;
            invk.args = propagateAssign_RemapStructuredArgs<{ arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }>(invk.args, (u) => {
                return { arglayouttype: u.arglayouttype, argflowtype: u.argflowtype, arg: propagateAssign_Remap(u.arg, propMap) };
            });
            break;
        }
        case MIROpTag.MIRConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            tc.args = propagateAssign_RemapArgs(tc.args, propMap);
            break;
        }
        case MIROpTag.MIRConstructorTupleFromEphemeralList: {
            const tc = op as MIRConstructorTupleFromEphemeralList;
            tc.arg = propagateAssign_Remap(tc.arg, propMap);
            break;
        }
        case MIROpTag.MIRConstructorRecord: {
            const tc = op as MIRConstructorRecord;
            tc.args = propagateAssign_RemapStructuredArgs<[string, MIRArgument]>(tc.args, (v) => [v[0], propagateAssign_Remap(v[1], propMap)]);
            break;
        }
        case MIROpTag.MIRConstructorRecordFromEphemeralList: {
            const tc = op as MIRConstructorRecordFromEphemeralList;
            tc.arg = propagateAssign_Remap(tc.arg, propMap);
            break;
        }

   
    MIRStructuredAppendTuple = "MIRStructuredAppendTuple",
    MIRStructuredJoinRecord = "MIRStructuredJoinRecord",
    MIRConstructorEphemeralList = "MIRConstructorEphemeralList",
    MIREphemeralListExtend = "MIREphemeralListExtend",

    MIRConstructorPrimaryCollectionEmpty = "MIRConstructorPrimaryCollectionEmpty",
    MIRConstructorPrimaryCollectionSingletons = "MIRConstructorPrimaryCollectionSingletons",
    MIRConstructorPrimaryCollectionCopies = "MIRConstructorPrimaryCollectionCopies",
    MIRConstructorPrimaryCollectionMixed = "MIRConstructorPrimaryCollectionMixed",

    MIRBinKeyEq = "MIRBinKeyEq",
    MIRBinKeyLess = "MIRBinKeyLess",
    MIRPrefixNotOp = "MIRPrefixNotOp",
    MIRAllTrue = "MIRAllTrue",

    MIRIsTypeOf = "MIRIsTypeOf",

    MIRJump = "MIRJump",
    MIRJumpCond = "MIRJumpCond",
    MIRJumpNone = "MIRJumpNone",

    MIRTempRegisterAssign = "MIRTempRegisterAssign",
    MIRParameterVarStore = "MIRParameterVarStore",
    MIRLocalVarStore = "MIRLocalVarStore",

    MIRReturnAssign = "MIRReturnAssign",
    MIRReturnAssignOfCons = "MIRReturnAssignOfCons",
    MIRVarLifetimeStart = "MIRVarLifetimeStart",
    MIRVarLifetimeEnd = "MIRVarLifetimeEnd",

    MIRPhi = "MIRPhi"


        
        case MIROpTag.MIRAccessArgVariable: {
            const lav = op as MIRAccessArgVariable;
            propagateTmpAssign_Bind(lav.trgt, lav.name, propMap);
            break;
        }
        case MIROpTag.MIRAccessLocalVariable: {
            const llv = op as MIRAccessLocalVariable;
            propagateTmpAssign_Bind(llv.trgt, llv.name, propMap);
            break;
        }
        case MIROpTag.MIRInvokeInvariantCheckDirect: {
            const cp = op as MIRInvokeInvariantCheckDirect;
            cp.rcvr = propagateTmpAssign_Remap(cp.rcvr, propMap);
            break;
        }
        case MIROpTag.MIRInvokeInvariantCheckVirtualTarget: {
            const cp = op as MIRInvokeInvariantCheckVirtualTarget;
            cp.rcvr = propagateTmpAssign_Remap(cp.rcvr, propMap);
            break;
        }
        case MIROpTag.MIRConstructorPrimary: {
            const cp = op as MIRConstructorPrimary;
            cp.args = propagateTmpAssign_RemapArgs(cp.args, propMap);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cc = op as MIRConstructorPrimaryCollectionSingletons;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cc = op as MIRConstructorPrimaryCollectionCopies;
            cc.args = propagateTmpAssign_RemapArgs(cc.args, propMap);
            break;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cc = op as MIRConstructorPrimaryCollectionMixed;
            cc.args = propagateTmpAssign_RemapStructuredArgs(cc.args, (v) => [v[0], propagateTmpAssign_Remap(v[1], propMap)] as [boolean, MIRArgument]);
            break;
        }
        
        
        case MIROpTag.MIRConstructorEphemeralValueList: {
            const tc = op as MIRConstructorEphemeralValueList;
            tc.args = propagateTmpAssign_RemapArgs(tc.args, propMap);
            break;
        }
        
        
        case MIROpTag.MIRPrefixOp: {
            const pfx = op as MIRPrefixOp;
            pfx.arg = propagateTmpAssign_Remap(pfx.arg, propMap);
            break;
        }
        case MIROpTag.MIRBinOp: {
            const bop = op as MIRBinOp;
            bop.lhs = propagateTmpAssign_Remap(bop.lhs, propMap);
            bop.rhs = propagateTmpAssign_Remap(bop.rhs, propMap);
            break;
        }
        case MIROpTag.MIRBinEq: {
            const beq = op as MIRBinEq;
            beq.lhs = propagateTmpAssign_Remap(beq.lhs, propMap);
            beq.rhs = propagateTmpAssign_Remap(beq.rhs, propMap);
            break;
        }
        case MIROpTag.MIRBinLess: {
            const bl = op as MIRBinLess;
            bl.lhs = propagateTmpAssign_Remap(bl.lhs, propMap);
            bl.rhs = propagateTmpAssign_Remap(bl.rhs, propMap);
            break;
        }
        case MIROpTag.MIRBinCmp: {
            const bcp = op as MIRBinCmp;
            bcp.lhs = propagateTmpAssign_Remap(bcp.lhs, propMap);
            bcp.rhs = propagateTmpAssign_Remap(bcp.rhs, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOfNone: {
            const ton = op as MIRIsTypeOfNone;
            ton.arg = propagateTmpAssign_Remap(ton.arg, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            const tos = op as MIRIsTypeOfSome;
            tos.arg = propagateTmpAssign_Remap(tos.arg, propMap);
            break;
        }
        case MIROpTag.MIRIsTypeOf: {
            const tog = op as MIRIsTypeOf;
            tog.arg = propagateTmpAssign_Remap(tog.arg, propMap);
            break;
        }
        case MIROpTag.MIRRegAssign: {
            const regop = op as MIRRegAssign;
            regop.src = propagateTmpAssign_Remap(regop.src, propMap);
            propagateTmpAssign_Bind(regop.trgt, regop.src, propMap);
            break;
        }
        case MIROpTag.MIRTruthyConvert: {
            const tcop = op as MIRTruthyConvert;
            tcop.src = propagateTmpAssign_Remap(tcop.src, propMap);
            break;
        }
        case MIROpTag.MIRVarStore: {
            const vs = op as MIRVarStore;
            vs.src = propagateTmpAssign_Remap(vs.src, propMap);
            break;
        }
        case MIROpTag.MIRPackSlice: {
            const pso = op as MIRPackSlice;
            pso.src = propagateTmpAssign_Remap(pso.src, propMap);
            break;
        }
        case MIROpTag.MIRPackExtend: {
            const pse = op as MIRPackExtend;
            pse.basepack = propagateTmpAssign_Remap(pse.basepack, propMap);
            pse.ext = propagateTmpAssign_RemapArgs(pse.ext, propMap);
            break;
        }
        case MIROpTag.MIRReturnAssign: {
            const ra = op as MIRReturnAssign;
            ra.src = propagateTmpAssign_Remap(ra.src, propMap);
            break;
        }
        case MIROpTag.MIRAbort: {
            break;
        }
        
        case MIROpTag.MIRJump: {
            break;
        }
        case MIROpTag.MIRJumpCond: {
            const cjop = op as MIRJumpCond;
            cjop.arg = propagateTmpAssign_Remap(cjop.arg, propMap);
            break;
        }
        case MIROpTag.MIRJumpNone: {
            const njop = op as MIRJumpNone;
            njop.arg = propagateTmpAssign_Remap(njop.arg, propMap);
            break;
        }
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            break;
        }
        default:
            assert(false);
            break;
    }

    const ks = op.getModVars();
    ks.forEach((kv) => propagateAssign_Kill(kv, propMap));
}

function propagateTmpAssignForBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        let propMap = new Map<number, MIRArgument>();
        for (let i = 0; i < blk.ops.length; ++i) {
            propagateTmpAssignForOp(blk.ops[i], propMap);
        }
    });
}

function computeTmpUseForBody(body: MIRBody): Set<number> {
    if (typeof (body) === "string") {
        return new Set<number>();
    }

    let usedTemps = new Set<number>();
    (body.body as Map<string, MIRBasicBlock>).forEach((blk) => {
        for (let i = 0; i < blk.ops.length; ++i) {
            const optmps = blk.ops[i].getUsedVars().filter((arg) => arg instanceof MIRTempRegister);
            for (let j = 0; j < optmps.length; ++j) {
                usedTemps.add((optmps[j] as MIRTempRegister).regID);
            }
        }
    });

    return usedTemps;
}

function isDeadTempAssign(op: MIROp, liveTemps: Set<number>): boolean {
    switch (op.tag) {
        case MIROpTag.MIRLoadConst:
        case MIROpTag.MIRAccessArgVariable:
        case MIROpTag.MIRAccessLocalVariable:
        case MIROpTag.MIRRegAssign: {
            return op.getModVars().every((mv) => mv instanceof MIRTempRegister && !liveTemps.has(mv.regID));
        }
        default:
            return false;
    }
}

function removeDeadTempAssignsFromBody(body: MIRBody) {
    if (typeof (body) === "string") {
        return;
    }

    let oldLiveSize = Number.MAX_SAFE_INTEGER;
    let liveTemps = computeTmpUseForBody(body);
    while (liveTemps.size < oldLiveSize) {
        let nbody = new Map<string, MIRBasicBlock>();
        (body.body as Map<string, MIRBasicBlock>).forEach((blk, id) => {
            const ops = blk.ops.filter((op) => !isDeadTempAssign(op, liveTemps));
            nbody.set(id, new MIRBasicBlock(id, ops));
        });
        body.body = nbody;

        oldLiveSize = liveTemps.size;
        liveTemps = computeTmpUseForBody(body);
    }
}

export { propagateTmpAssignForBody, removeDeadTempAssignsFromBody };
