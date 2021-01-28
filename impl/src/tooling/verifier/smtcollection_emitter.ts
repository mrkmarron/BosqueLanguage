//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTCallSimple, SMTExp, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

class RequiredListConstructors {
    //always slice
    //always append2 and append3

    fill: boolean = false;
    literalk: Map<string, number> = new Map<string, number>();
}

class RequiredListDestructors {
    //always get
}

class ListOpsInfo {
    readonly ltype: MIRType;
    readonly ctype: MIRType;

    consops: RequiredListConstructors;
    dops: RequiredListDestructors;

    constructor(ltype: MIRType, ctype: MIRType) {
        this.ltype = ltype;
        this.ctype = ctype;

        this.consops = new RequiredListConstructors();
        this.dops = new RequiredListDestructors();
    }
}

class ListOpsManager {
    vopts: VerifierOptions
    temitter: SMTTypeEmitter;

    rangenat: boolean = false;
    rangeint: boolean = false;

    ops: Map<string, ListOpsInfo> = new Map<string, ListOpsInfo>();

    constructor(vopts: VerifierOptions, temitter: SMTTypeEmitter) {
        this.vopts = vopts;
        this.temitter = temitter;
    }

    private ensureOpsFor(encltype: MIRType): ListOpsInfo {
        if (!this.ops.has(encltype.trkey)) {
            const stypeinfo = (this.temitter.assembly.entityDecls.get(encltype.trkey) as MIREntityTypeDecl).specialTemplateInfo as { tname: string, tkind: MIRResolvedTypeKey }[];
            const ctype = this.temitter.getMIRType((stypeinfo.find((tke) => tke.tname === "T") as { tname: string, tkind: MIRResolvedTypeKey }).tkind);

            this.ops.set(encltype.trkey, new ListOpsInfo(encltype, ctype));
        }

        return this.ops.get(encltype.trkey) as ListOpsInfo;
    }

    processFillOperation(encltype: MIRType, count: SMTVar, value: SMTVar): SMTExp {
        const ops = this.ensureOpsFor(encltype);
        ops.consops.fill = true;

        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(encltype), "fill");
        const llcons = this.temitter.getSMTConstructorName(encltype);
        return new SMTCallSimple(`${llcons.cons}`, [count, new SMTCallSimple(fcons, [value])]);
    }

    generateConsCallName(ltype: SMTType, opname: string): string {
        return `@@cons_${ltype.name}_${opname}`;
    }

    generateListSizeCall(larg: {vname: string, vtype: SMTType}): SMTExp {
        return new SMTCallSimple(`${larg.vtype.name}@size`, [new SMTVar(larg.vname)]);
    }

    generateListBoundsCheckCallUpper(nidx: string, upper: SMTExp): SMTExp {
        //lower bound is assumed to be 0
        return new SMTCallSimple("bvult", [new SMTVar(nidx), upper]);
    }

    generateListBoundsCheckCallBoth(nidx: string, lower: SMTExp, upper: SMTExp): SMTExp {
        return new SMTCallSimple("and", [
            new SMTCallSimple("bvule", [lower, new SMTVar(nidx)]),
            new SMTCallSimple("bvult", [new SMTVar(nidx), upper])
        ]);
    }

    generateListKnownSafeGetCall(larg: {vname: string, vtype: SMTType}, n: SMTExp): SMTExp {
        return new SMTCallSimple(`${larg.vtype.name}@get`, [new SMTVar(larg.vname), n]);
    }
}

export {
    ListOpsManager
};
