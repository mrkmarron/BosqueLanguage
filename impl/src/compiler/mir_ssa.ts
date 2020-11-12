//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";
import { MIRArgGuard, MIRArgument, MIRAssertCheck, MIRCheckNoError, MIRConvertValue, MIRDebug, MIREntityProjectToEphemeral, MIREntityUpdate, MIRExtractResultOkValue, MIRGuard, MIRLoadConst, MIRLoadConstDataString, MIRLoadField, MIRLoadRecordProperty, MIRLoadRecordPropertySetGuard, MIRLoadTupleIndex, MIRLoadTupleIndexSetGuard, MIRLoadUnintVariableValue, MIRMaskGuard, MIROp, MIROpTag, MIRRecordHasProperty, MIRRecordProjectToEphemeral, MIRRecordUpdate, MIRRegisterArgument, MIRTempRegister, MIRTupleHasIndex, MIRTupleProjectToEphemeral, MIRTupleUpdate, MIRResolvedTypeKey, MIRLoadFromEpehmeralList, MIRMultiLoadFromEpehmeralList, MIRSliceEpehmeralList, MIRInvokeFixedFunction, MIRInvokeVirtualFunction, MIRInvokeVirtualOperator, MIRConstructorTuple, MIRConstructorTupleFromEphemeralList, MIRConstructorRecord, MIRConstructorRecordFromEphemeralList, MIRStructuredAppendTuple, MIRStructuredJoinRecord, MIRConstructorEphemeralList, MIRConstructorPrimaryCollectionEmpty, MIREphemeralListExtend, MIRConstructorPrimaryCollectionSingletons, MIRConstructorPrimaryCollectionCopies, MIRConstructorPrimaryCollectionMixed, MIRBinKeyEq, MIRBinKeyLess, MIRPrefixNotOp, MIRAllTrue, MIRIsTypeOf, MIRJumpCond, MIRJumpNone, MIRTempRegisterAssign, MIRLocalVarStore, MIRParameterVarStore, MIRReturnAssign, MIRReturnAssignOfCons, MIRPhi, MIRBody, MIRBasicBlock, MIRParameterVariable, MIRLocalVariable } from "./mir_ops";
import { SourceInfo } from "../ast/parser";
import { FlowLink, BlockLiveSet, computeBlockLinks, computeBlockLiveVars, topologicalOrder } from "./mir_info";
import { MIRType } from "./mir_assembly";

type SSAState = {
    remap: Map<string, MIRRegisterArgument>,
    ctrs: Map<string, number>,
    tmpregids: Map<string, number>
};

function convertToSSA(reg: MIRRegisterArgument, ssastate: SSAState): MIRTempRegister {
    if (reg instanceof MIRTempRegister && !ssastate.ctrs.has(reg.nameID)) {
        ssastate.ctrs.set(reg.nameID, 0);
        ssastate.remap.set(reg.nameID, reg);

        return reg;
    }
    else {
        const ssaCtr = ssastate.ctrs.has(reg.nameID) ? ssastate.ctrs.get(reg.nameID) as number + 1 : 0;
        ssastate.ctrs.set(reg.nameID, ssaCtr);

        const vname = reg.nameID + `$${ssaCtr}`;

        if (reg instanceof MIRTempRegister) {
            ssastate.remap.set(reg.nameID, new MIRTempRegister(reg.regID, vname));
        }
        else {
            ssastate.remap.set(reg.nameID, new MIRTempRegister(ssastate.tmpregids.get(reg.nameID) as number, vname));
        }

        return ssastate.remap.get(reg.nameID) as MIRTempRegister;
    }
}

function convertToSSA_Guard(guard: MIRGuard, ssastate: SSAState): MIRGuard {
    if(guard instanceof MIRMaskGuard) {
        return guard;
    }
    else {
        const vg = guard as MIRArgGuard;
        if(vg.greg instanceof MIRRegisterArgument) {
            return new MIRArgGuard(convertToSSA(vg.greg as MIRRegisterArgument, ssastate));
        }
        else {
            return vg;
        }
    }
}

function processSSA_Use(arg: MIRArgument, ssastate: SSAState): MIRRegisterArgument {
    if (arg instanceof MIRRegisterArgument) {
        return ssastate.remap.get(arg.nameID) || arg;
    }
    else {
        return arg;
    }
}

function processSSAUse_RemapGuard(guard: MIRGuard | undefined, ssastate: SSAState): MIRGuard | undefined {
    if(guard === undefined) {
        return undefined;
    }
    else if(guard instanceof MIRMaskGuard) {
        return guard;
    }
    else {
        return new MIRArgGuard(processSSA_Use((guard as MIRArgGuard).greg, ssastate));
    }
}

function processSSAUse_RemapArgs(args: MIRArgument[], ssastate: SSAState): MIRArgument[] {
    return args.map((v) => processSSA_Use(v, ssastate));
}

function processSSAUse_RemapStructuredArgs<T>(args: T[], remap: (arg: T) => T): T[] {
    return args.map((v) => remap(v));
}

function assignSSA(op: MIROp, ssastate: SSAState): MIROp {
    switch (op.tag) {
        case MIROpTag.MIRNop: 
        case MIROpTag.MIRDeadFlow:
        case MIROpTag.MIRAbort:
        case MIROpTag.MIRDeclareGuardFlagLocation: 
        case MIROpTag.MIRSetConstantGuardFlag:
        case MIROpTag.MIRVarLifetimeStart:
        case MIROpTag.MIRVarLifetimeEnd: {
            return op;
        }
        case MIROpTag.MIRAssertCheck: {
            const asrt = op as MIRAssertCheck;
            asrt.arg = processSSA_Use(asrt.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRDebug: {
            const dbg = op as MIRDebug;
            if (dbg.value !== undefined) {
                dbg.value = processSSA_Use(dbg.value, ssastate);
            }
            return op;
        }
        case MIROpTag.MIRLoadUnintVariableValue: {
            const luv = op as MIRLoadUnintVariableValue;
            luv.trgt = convertToSSA(luv.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConvertValue: {
            const conv = op as MIRConvertValue;
            conv.src = processSSA_Use(conv.src, ssastate);
            conv.guard = processSSAUse_RemapGuard(conv.guard, ssastate);
            conv.trgt = convertToSSA(conv.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRCheckNoError: {
            const chk = op as MIRCheckNoError;
            chk.src = processSSA_Use(chk.src, ssastate);
            chk.trgt = convertToSSA(chk.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRExtractResultOkValue: {
            const erok = op as MIRExtractResultOkValue;
            erok.src = processSSA_Use(erok.src, ssastate);
            erok.trgt = convertToSSA(erok.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadConst: {
            const lc = op as MIRLoadConst;
            lc.trgt = convertToSSA(lc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadConstDataString: {
            const lcd = op as MIRLoadConstDataString;
            lcd.trgt = convertToSSA(lcd.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleHasIndex: {
            const thi = op as MIRTupleHasIndex;
            thi.arg = processSSA_Use(thi.arg, ssastate);
            thi.trgt = convertToSSA(thi.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordHasProperty: {
            const rhi = op as MIRRecordHasProperty;
            rhi.arg = processSSA_Use(rhi.arg, ssastate);
            rhi.trgt = convertToSSA(rhi.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadTupleIndex: {
            const lti = op as MIRLoadTupleIndex;
            lti.arg = processSSA_Use(lti.arg, ssastate);
            lti.trgt = convertToSSA(lti.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadTupleIndexSetGuard: {
            const ltig = op as MIRLoadTupleIndexSetGuard;
            ltig.arg = processSSA_Use(ltig.arg, ssastate);
            ltig.guard = convertToSSA_Guard(ltig.guard, ssastate);
            ltig.trgt = convertToSSA(ltig.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadRecordProperty: {
            const lrp = op as MIRLoadRecordProperty;
            lrp.arg = processSSA_Use(lrp.arg, ssastate);
            lrp.trgt = convertToSSA(lrp.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadRecordPropertySetGuard: {
            const lrpg = op as MIRLoadRecordPropertySetGuard;
            lrpg.arg = processSSA_Use(lrpg.arg, ssastate);
            lrpg.guard = convertToSSA_Guard(lrpg.guard, ssastate);
            lrpg.trgt = convertToSSA(lrpg.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadField: {
            const lmf = op as MIRLoadField;
            lmf.arg = processSSA_Use(lmf.arg, ssastate);
            lmf.trgt = convertToSSA(lmf.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleProjectToEphemeral: {
            const pte = op as MIRTupleProjectToEphemeral;
            pte.arg = processSSA_Use(pte.arg, ssastate);
            pte.trgt = convertToSSA(pte.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordProjectToEphemeral: {
            const pre = op as MIRRecordProjectToEphemeral;
            pre.arg = processSSA_Use(pre.arg, ssastate);
            pre.trgt = convertToSSA(pre.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIREntityProjectToEphemeral: {
            const pee = op as MIREntityProjectToEphemeral;
            pee.arg = processSSA_Use(pee.arg, ssastate);
            pee.trgt = convertToSSA(pee.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRTupleUpdate: {
            const mi = op as MIRTupleUpdate;
            mi.arg = processSSA_Use(mi.arg, ssastate);
            mi.updates = processSSAUse_RemapStructuredArgs<[number, MIRArgument, MIRResolvedTypeKey]>(mi.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mi.trgt = convertToSSA(mi.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRRecordUpdate: {
            const mp = op as MIRRecordUpdate;
            mp.arg = processSSA_Use(mp.arg, ssastate);
            mp.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mp.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mp.trgt = convertToSSA(mp.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIREntityUpdate: {
            const mf = op as MIREntityUpdate;
            mf.arg = processSSA_Use(mf.arg, ssastate);
            mf.updates = processSSAUse_RemapStructuredArgs<[string, MIRArgument, MIRResolvedTypeKey]>(mf.updates, (u) => [u[0], processSSA_Use(u[1], ssastate), u[2]]);
            mf.trgt = convertToSSA(mf.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLoadFromEpehmeralList: {
            const mle = op as MIRLoadFromEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgt = convertToSSA(mle.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRMultiLoadFromEpehmeralList: {
            const mle = op as MIRMultiLoadFromEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgts.forEach((trgt) => {
                trgt.into = convertToSSA(trgt.into, ssastate);
            });
            return op;
        }
        case MIROpTag.MIRSliceEpehmeralList: {
            const mle = op as MIRSliceEpehmeralList;
            mle.arg = processSSA_Use(mle.arg, ssastate);
            mle.trgt = convertToSSA(mle.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeFixedFunction: {
            const invk = op as MIRInvokeFixedFunction;
            invk.args = processSSAUse_RemapArgs(invk.args, ssastate);
            invk.trgt = convertToSSA(invk.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeVirtualFunction: {
            const invk = op as MIRInvokeVirtualFunction;
            invk.args = processSSAUse_RemapArgs(invk.args, ssastate);
            invk.trgt = convertToSSA(invk.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRInvokeVirtualOperator: {
            const invk = op as MIRInvokeVirtualOperator;
            invk.args = processSSAUse_RemapStructuredArgs<{ arglayouttype: MIRResolvedTypeKey, argflowtype: MIRResolvedTypeKey, arg: MIRArgument }>(invk.args, (u) => {
                return { arglayouttype: u.arglayouttype, argflowtype: u.argflowtype, arg: processSSA_Use(u.arg, ssastate) };
            });
            invk.trgt = convertToSSA(invk.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorTuple: {
            const tc = op as MIRConstructorTuple;
            tc.args = processSSAUse_RemapArgs(tc.args, ssastate);
            tc.trgt = convertToSSA(tc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorTupleFromEphemeralList: {
            const tc = op as MIRConstructorTupleFromEphemeralList;
            tc.arg = processSSA_Use(tc.arg, ssastate);
            tc.trgt = convertToSSA(tc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorRecord: {
            const tc = op as MIRConstructorRecord;
            tc.args = processSSAUse_RemapStructuredArgs<[string, MIRArgument]>(tc.args, (v) => [v[0], processSSA_Use(v[1], ssastate)]);
            tc.trgt = convertToSSA(tc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorRecordFromEphemeralList: {
            const tc = op as MIRConstructorRecordFromEphemeralList;
            tc.arg = processSSA_Use(tc.arg, ssastate);
            tc.trgt = convertToSSA(tc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRStructuredAppendTuple: {
            const at = op as MIRStructuredAppendTuple;
            at.args = processSSAUse_RemapArgs(at.args, ssastate);
            at.trgt = convertToSSA(at.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRStructuredJoinRecord: {
            const sj = op as MIRStructuredJoinRecord;
            sj.args = processSSAUse_RemapArgs(sj.args, ssastate);
            sj.trgt = convertToSSA(sj.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorEphemeralList: {
            const tc = op as MIRConstructorEphemeralList;
            tc.args = processSSAUse_RemapArgs(tc.args, ssastate);
            tc.trgt = convertToSSA(tc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIREphemeralListExtend: {
            const pse = op as MIREphemeralListExtend;
            pse.arg = processSSA_Use(pse.arg, ssastate);
            pse.ext = processSSAUse_RemapArgs(pse.ext, ssastate);
            pse.trgt = convertToSSA(pse.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
            const cc = op as MIRConstructorPrimaryCollectionEmpty;
            cc.trgt = convertToSSA(cc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
            const cc = op as MIRConstructorPrimaryCollectionSingletons;
            cc.args = processSSAUse_RemapArgs(cc.args, ssastate);
            cc.trgt = convertToSSA(cc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionCopies: {
            const cc = op as MIRConstructorPrimaryCollectionCopies;
            cc.args = processSSAUse_RemapArgs(cc.args, ssastate);
            cc.trgt = convertToSSA(cc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRConstructorPrimaryCollectionMixed: {
            const cc = op as MIRConstructorPrimaryCollectionMixed;
            cc.args = processSSAUse_RemapStructuredArgs<[boolean, MIRArgument]>(cc.args, (v) => [v[0], processSSA_Use(v[1], ssastate)]);
            cc.trgt = convertToSSA(cc.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRBinKeyEq: {
            const beq = op as MIRBinKeyEq;
            beq.lhs = processSSA_Use(beq.lhs, ssastate);
            beq.rhs = processSSA_Use(beq.rhs, ssastate);
            beq.trgt = convertToSSA(beq.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRBinKeyLess: {
            const bl = op as MIRBinKeyLess;
            bl.lhs = processSSA_Use(bl.lhs, ssastate);
            bl.rhs = processSSA_Use(bl.rhs, ssastate);
            bl.trgt = convertToSSA(bl.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRPrefixNotOp: {
            const pfx = op as MIRPrefixNotOp;
            pfx.arg = processSSA_Use(pfx.arg, ssastate);
            pfx.trgt = convertToSSA(pfx.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRAllTrue: {
            const at = op as MIRAllTrue;
            at.args = processSSAUse_RemapArgs(at.args, ssastate);
            at.trgt = convertToSSA(at.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRIsTypeOf: {
            const it = op as MIRIsTypeOf;
            it.arg = processSSA_Use(it.arg, ssastate);
            it.guard = processSSAUse_RemapGuard(it.guard, ssastate);
            it.trgt = convertToSSA(it.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRJump: {
            return op;
        }
        case MIROpTag.MIRJumpCond: {
            const cjop = op as MIRJumpCond;
            cjop.arg = processSSA_Use(cjop.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRJumpNone: {
            const njop = op as MIRJumpNone;
            njop.arg = processSSA_Use(njop.arg, ssastate);
            return op;
        }
        case MIROpTag.MIRTempRegisterAssign: {
            const regop = op as MIRTempRegisterAssign;
            regop.src = processSSA_Use(regop.src, ssastate);
            regop.guard = processSSAUse_RemapGuard(regop.guard, ssastate);
            regop.trgt = convertToSSA(regop.trgt, ssastate);
            return op;
        }
        case MIROpTag.MIRLocalVarStore: {
            const vs = op as MIRLocalVarStore;
            const src = processSSA_Use(vs.src, ssastate);
            const guard = processSSAUse_RemapGuard(vs.guard, ssastate);
            const trgt = convertToSSA(vs.trgt, ssastate);
            return new MIRTempRegisterAssign(vs.sinfo, src, trgt, vs.layouttype, guard);
        }
        case MIROpTag.MIRParameterVarStore: {
            const vs = op as MIRParameterVarStore;
            const src = processSSA_Use(vs.src, ssastate);
            const guard = processSSAUse_RemapGuard(vs.guard, ssastate);
            const trgt = convertToSSA(vs.trgt, ssastate);
            return new MIRTempRegisterAssign(vs.sinfo, src, trgt, vs.layouttype, guard);
        }
        case MIROpTag.MIRReturnAssign: {
            const ra = op as MIRReturnAssign;
            ra.src = processSSA_Use(ra.src, ssastate);
            ra.name = convertToSSA(ra.name, ssastate);
            return op;
        }
        case MIROpTag.MIRReturnAssignOfCons: {
            const ra = op as MIRReturnAssignOfCons;
            ra.args = processSSAUse_RemapArgs(ra.args, ssastate);
            ra.name = convertToSSA(ra.name, ssastate);
            return op;
        }
        case MIROpTag.MIRPhi: {
           assert(false);
           return op;
        }
        default:
            assert(false);
            return op;
    }
}

function generatePhi(sinfo: SourceInfo, lv: string, opts: [string, MIRRegisterArgument][], ctrs: Map<string, number>): MIRPhi {
    let vassign = new Map<string, MIRRegisterArgument>();
    opts.forEach((e) => vassign.set(e[0], e[1]));

    const ssaCtr = ctrs.get(lv) as number + 1;
    ctrs.set(lv, ssaCtr);

    const vname = lv + `$${ssaCtr}`;
    if (lv.startsWith("#tmp_")) {
        return new MIRPhi(sinfo, vassign, new MIRTempRegister(Number.parseInt(lv.substr(5)), vname));
    }
    else {
        return new MIRPhi(sinfo, vassign, new MIRVariable(lv, vname));
    }
}

function computePhis(sinfo: SourceInfo, block: string, ctrs: Map<string, number>, remapped: Map<string, Map<string, MIRRegisterArgument>>, links: Map<string, FlowLink>, live: Map<string, BlockLiveSet>): [MIRPhi[], Map<string, MIRRegisterArgument>] {
    let remap = new Map<string, MIRRegisterArgument>();
    let phis: MIRPhi[] = [];

    (live.get(block) as BlockLiveSet).liveEntry.forEach((v, n) => {
        const preds = (links.get(block) as FlowLink).preds;

        let phiOpts: [string, MIRRegisterArgument][] = [];
        let uniqueOpts = new Map<string, MIRRegisterArgument>();
        preds.forEach((pred) => {
            const pm = remapped.get(pred) as Map<string, MIRRegisterArgument>;
            const mreg = pm.get(n) as MIRRegisterArgument;
            uniqueOpts.set(mreg.nameID, mreg);
            phiOpts.push([pred, mreg]);
        });

        if (uniqueOpts.size === 1) {
            const rmp = [...uniqueOpts][0][1];
            remap.set(n, rmp);
        }
        else {
            const phi = generatePhi(sinfo, n, phiOpts, ctrs);

            phis.push(phi);
            remap.set(n, phi.trgt);
        }
    });

    return [phis, remap];
}

function convertBodyToSSA(body: MIRBody, args: Map<string, MIRType>) {
    const blocks = body.body as Map<string, MIRBasicBlock>;
    const links = computeBlockLinks(blocks);
    const live = computeBlockLiveVars(blocks);
    const torder = topologicalOrder(blocks);

    let remapped = new Map<string, Map<string, MIRRegisterArgument>>();
    let ctrs = new Map<string, number>();

    for (let j = 0; j < torder.length; ++j) {
        const block = torder[j];

        if (block.label === "entry") {
            let remap = new Map<string, MIRRegisterArgument>();
            args.forEach((arg, name) => remap.set(name, new MIRParameterVariable(name)));
            remap.set("$__ir_ret__", new MIRLocalVariable("$__ir_ret__"));
            remap.set("$$return", new MIRLocalVariable("$$return"));

            for (let i = 0; i < block.ops.length; ++i) {
                block.ops[i] = assignSSA(block.ops[i], remap, ctrs);
            }

            remapped.set(block.label, remap);
        }
        else {
            const [phis, remap] = computePhis(body.sinfo, block.label, ctrs, remapped, links, live);

            for (let i = 0; i < block.ops.length; ++i) {
                assignSSA(block.ops[i], remap, ctrs);
            }

            block.ops.unshift(...phis);
            remapped.set(block.label, remap);
        }
    }
}

export { convertBodyToSSA };
