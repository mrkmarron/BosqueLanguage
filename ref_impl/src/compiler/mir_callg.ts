//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//Compute the static call graph for an assembly
//

import * as assert from "assert";
import { MIRBasicBlock, MIROpTag, MIRInvokeKey, MIRInvokeFixedFunction } from "./mir_ops";
import { MIRInvokeBodyDecl, MIRInvokePrimitiveDecl } from "./mir_assembly";

type CallGNode = {
    invoke: MIRInvokeKey,
    callees: Set<MIRInvokeKey>,
    callers: Set<MIRInvokeKey>
};

function computeCalleesInBlocks(blocks: Map<string, MIRBasicBlock>, invokeNode: CallGNode) {
    blocks.forEach((block) => {
        for (let i = 0; i < block.ops.length; ++i) {
            if (block.ops[i].tag === MIROpTag.MIRInvokeFixedFunction) {
                invokeNode.callees.add((block.ops[i] as MIRInvokeFixedFunction).mkey);
            }
            else if (block.ops[i].tag === MIROpTag.MIRInvokeFixedFunction) {
                //TODO lookup all possible vtargets and add them
                assert(false);
            }
            else {
                //ignore all other ops
            }
        }
    });
}

function sccVisit(cn: CallGNode, scc: Set<CallGNode>, marked: Set<MIRInvokeKey>, invokes: Map<MIRInvokeKey, CallGNode>) {
    if (marked.has(cn.invoke)) {
        return;
    }

    scc.add(cn);
    marked.add(cn.invoke);
    cn.callers.forEach((pred) => sccVisit(invokes.get(pred) as CallGNode, scc, marked, invokes));
}

function topoVisit(cn: CallGNode, tordered: CallGNode[], invokes: Map<MIRInvokeKey, CallGNode>) {
    if (tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
        return;
    }

    cn.callees.forEach((succ) => (invokes.get(succ) as CallGNode).callers.add(cn.invoke));
    cn.callees.forEach((succ) => topoVisit(invokes.get(succ) as CallGNode, tordered, invokes));

    tordered.push(cn);
}

function constructCallGraphInfo(entryPoints: MIRInvokeKey[], invokeDecls: Map<MIRInvokeKey, MIRInvokeBodyDecl>, primitiveInvokeDecls: Map<MIRInvokeKey, MIRInvokePrimitiveDecl>): { invokes: Map<MIRInvokeKey, CallGNode>, topologicalOrder: CallGNode[], roots: CallGNode[], recursive: (Set<CallGNode>)[] } {
    let invokes = new Map<MIRInvokeKey, CallGNode>();
    invokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: ikey, callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
        computeCalleesInBlocks(ivk.body.body, cn);
        invokes.set(ikey, cn);
    });
    primitiveInvokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: ikey, callees: new Set<MIRInvokeKey>(), callers: new Set<MIRInvokeKey>() };
        ivk.pcodes.forEach((pc) => cn.callees.add(pc.code));
        invokes.set(ikey, cn);
    });

    let roots: CallGNode[] = [];
    let tordered: CallGNode[] = [];
    entryPoints.forEach((ivk) => {
        roots.push(invokes.get(ivk) as CallGNode);
        topoVisit(invokes.get(ivk) as CallGNode, tordered, invokes);
    });
    tordered = tordered.reverse();

    let marked = new Set<MIRInvokeKey>();
    let recursive: (Set<CallGNode>)[] = [];
    for (let i = 0; i < tordered.length; ++i) {
        let scc = new Set<CallGNode>();
        sccVisit(tordered[i], scc, marked, invokes);

        if (scc.size > 1) {
            recursive.push(scc);
        }
    }

    return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
}

export { constructCallGraphInfo };
