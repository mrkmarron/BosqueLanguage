//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBody, MIRResolvedTypeKey, MIRPhi, MIRBasicBlock, MIRInvokeKey, MIRTempRegister, MIRVariable, MIRRegAssign, MIRRegisterArgument, MIROpTag, MIRJump, MIRInvokeFixedFunction, MIRReturnAssign, MIRJumpOp, MIRJumpCond, MIRJumpNone } from "./mir_ops";
import { computeBlockLinks, topologicalOrder, FlowLink, computeBlockLiveVars, BlockLiveSet } from "./mir_info";
import { MIRFunctionParameter } from "./mir_assembly";
import { SourceInfo } from "../ast/parser";

type NBodyInfo = {
    nname: MIRInvokeKey;
    nparams: MIRFunctionParameter[];
    nblocks: MIRBasicBlock[];
};

const sinfo_undef = new SourceInfo(-1, -1, -1, -1);

class FunctionalizeEnv
{
    tmpctr: number = 100000;
    readonly rtype: MIRResolvedTypeKey;
    readonly invid: MIRInvokeKey;
    readonly largs: MIRRegisterArgument[];
    readonly trgtphis: MIRPhi[];
    readonly jlabel: string;

    nbbl: MIRBasicBlock[] = [];
    rphimap: Map<string, MIRRegisterArgument> = new Map<string, MIRRegisterArgument>();

    constructor(rtype: MIRResolvedTypeKey, invid: MIRInvokeKey, largs: MIRRegisterArgument[], trgtphis: MIRPhi[], jlabel: string) {
        this.rtype = rtype;
        this.invid = invid;
        this.largs = largs;
        this.trgtphis = trgtphis;
        this.jlabel = jlabel;
    }

    generateTempRegister(): MIRTempRegister {
        return new MIRTempRegister(this.tmpctr++);
    }

    setResultPhiEntry(srcblock: string, v: MIRRegisterArgument) {
        this.rphimap.set(srcblock, v);
    }
}

function generateTargetFunctionName(cinvoke: MIRInvokeKey, trgtlbl: string): MIRInvokeKey {
    return (cinvoke + "$$" + trgtlbl) as MIRInvokeKey;
}


function generateTailCall(bblabel: string, fenv: FunctionalizeEnv): MIRInvokeFixedFunction {
    const phiargs = fenv.trgtphis.map((phi) => phi.src.get(bblabel) as MIRRegisterArgument);
    const args = [...fenv.largs, ...phiargs];

    return new MIRInvokeFixedFunction(sinfo_undef, fenv.rtype, fenv.invid, args, fenv.generateTempRegister());
}

function updateJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJump;
    if (jop.trgtblock === fenv.jlabel) {
        const tc = generateTailCall(bb.label, fenv);
        bb.ops[bb.ops.length - 1] = tc;
        bb.ops.push(new MIRJump(sinfo_undef, "exit"));

       
    }
}

function updateCondJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

    if(jop.trueblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(tjop.sinfo, tjop.arg, ntb.label, tjop.falseblock);

        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }

    if(jop.falseblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpCond;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpCond(fjop.sinfo, fjop.arg, fjop.trueblock, ntb.label);

        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}

function updateNoneJumpOp(bb: MIRBasicBlock, fenv: FunctionalizeEnv) {
    const jop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

    if(jop.noneblock === fenv.jlabel) {
        const tjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "tbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(tjop.sinfo, tjop.arg, ntb.label, tjop.someblock);

        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }

    if(jop.someblock === fenv.jlabel) {
        const fjop = bb.ops[bb.ops.length - 1] as MIRJumpNone;

        const tc = generateTailCall(bb.label, fenv);
        const ntb = new MIRBasicBlock(bb.label + "fbb", [tc, new MIRJump(sinfo_undef, "exit")]);
        bb.ops[bb.ops.length - 1] = new MIRJumpNone(fjop.sinfo, fjop.arg, fjop.noneblock, ntb.label);

        fenv.setResultPhiEntry(ntb.label, tc.trgt);
    }
}

function replaceJumpsWithCalls(bbl: MIRBasicBlock[], fenv: FunctionalizeEnv) {
    bbl.forEach((bb) => {
        const lop = bb.ops[bb.ops.length - 1];
        switch (lop.tag) {
            case MIROpTag.MIRJump: {
                updateJumpOp(bb, fenv);
                break;
            }
            case MIROpTag.MIRJumpCond: {
                updateCondJumpOp(bb, fenv);
                break;
            }
            case MIROpTag.MIRJumpNone: {
                updateNoneJumpOp(bb, fenv);
                break;
            }
        }
    });
}

function processBodyRoundOne(invid: string, b: MIRBody): NBodyInfo | undefined {
    const links = computeBlockLinks(b.body);
    const bo = topologicalOrder(b.body);
    const lv = computeBlockLiveVars(b.body);
    const vtypes = b.vtypes as Map<string, MIRResolvedTypeKey>;

    const lidx = bo.findIndex((bb) => bb.label === "returnassign");
    const fjidx = bo.findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1);

    if(fjidx === -1 || lidx <= fjidx) {
        return undefined;
    }

    const jlabel = "returnassign";

    const phis = bo[lidx].ops.filter((op) => op instanceof MIRPhi) as MIRPhi[];
    const phivargs = phis.map((op) => op.trgt.nameID);
    const phivkill = new Set(([] as string[]).concat(...phis.map((op) => [...op.src].map((src) => src[0]))));

    const fblocks = [new MIRBasicBlock("entry", bo[lidx].ops.slice(phis.length)), ...bo.slice(lidx + 1)];
    
    
    
    
    const rblocks = bo.slice(0, lidx);

    const jvars = [...(lv.get(bo[lidx].label) as BlockLiveSet).liveEntry].filter((lvn) => !phivkill.has(lvn[0])).sort();
    const oparams = jvars.map((lvn) => new MIRFunctionParameter(lvn[0], vtypes.get(lvn[0]) as MIRResolvedTypeKey));
    const phiparams = phivargs.map((pv) => new MIRFunctionParameter(pv, vtypes.get(pv) as MIRResolvedTypeKey));

    const nparams = [...oparams, ...phiparams];
    const ninvid = generateTargetFunctionName(invid, jlabel);

    //process all call sites for b
    xxxx;

    //patch up the return assign and exit blocks for b
    xxxx;

    return {nname: ninvid, nparams: nparams, nblocks: nblocks};
}

function processBodyIter(invid: string, b: MIRBody): NBodyInfo | undefined {
}

function processBody(invid: string, b: MIRBody): NBodyInfo | undefined {
    const links = computeBlockLinks(b.body);
    const bo = topologicalOrder(b.body);
    const lv = computeBlockLiveVars(b.body);
    const vtypes = b.vtypes as Map<string, MIRResolvedTypeKey>;

    const lidx = bo.findIndex((bb) => bb.label === "returnassign");
    const fjidx = bo.findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1);

    if(fjidx === -1 || fjidx >= lidx) {
        return undefined;
    }

    const jidx = bo.length - [...bo].reverse().findIndex((bb) => (links.get(bb.label) as FlowLink).preds.size > 1);
    const jlabel = bo[jidx].label;
    
    const phis = bo[jidx].ops.filter((op) => op instanceof MIRPhi) as MIRPhi[];
    const phivargs = phis.map((op) => op.trgt.nameID);
    const phivkill = new Set(([] as string[]).concat(...phis.map((op) => [...op.src].map((src) => src[0]))));

    const fblocks = [new MIRBasicBlock("entry", bo[jidx].ops.slice(phis.length)), ...bo.slice(jidx + 1)];
    const rblocks = bo.slice(0, jidx);


    const cblocks = bo.slice(jidx + 1).map((bb) => {
        xxx;x

        return new MIRBasicBlock(bb.label, clops);
    }); 
    const nblocks = [jblock, ...cblocks];

    const jvars = [...(lv.get(bo[jidx].label) as BlockLiveSet).liveEntry].filter((lvn) => !phivkill.has(lvn)).sort();
    const oparams = jvars.map((lvn) => new MIRFunctionParameter(lvn, vtypes.get(lvn) as MIRResolvedTypeKey));
    const phiparams = phivargs.map((pv) => new MIRFunctionParameter(pv, vtypes.get(pv) as MIRResolvedTypeKey));

    const nparams = [...oparams, ...phiparams];
    const ninvid = generateTargetFunctionName(invid, jlabel);

    //process all call sites for b
    xxxx;

    //patch up the return assign and exit blocks for b
    xxxx;

    return {nname: ninvid, nparams: nparams, nblocks: nblocks};

}

