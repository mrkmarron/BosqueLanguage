//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIREntityTypeDecl, MIRType } from "../../compiler/mir_assembly";
import { MIRResolvedTypeKey } from "../../compiler/mir_ops";
import { SMTTypeEmitter } from "./smttype_emitter";
import { SMTCallGeneral, SMTCallSimple, SMTConst, SMTExp, SMTIf, SMTLet, SMTType, SMTVar, VerifierOptions } from "./smt_exp";

class RequiredListConstructors {
    //always error
    //always empty
    //always slice
    //always append2 and append3

    fill: boolean = false;
    literalk: Set<number> = new Set<number>();
    concat2: boolean = false;
}

class RequiredListDestructors {
    //always get

    haspredcheck: Set<string> = new Set<string>();
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

    private tmpvarctr = 0;

    
    generateTempName(): string {
        return `@tmpvar_cc@${this.tmpvarctr++}`;
    }

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

    processLiteralK_0(ltype: MIRType): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "empty");

        const llcons = this.temitter.getSMTConstructorName(ltype);
        return new SMTCallSimple(`${llcons.cons}`, [new SMTConst("BNat@zero"), new SMTConst(fcons)]);
    }

    processLiteralK_Pos(ltype: MIRType, k: number, values: SMTExp[]): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "k");
        ops.consops.literalk.add(k)

        const llcons = this.temitter.getSMTConstructorName(ltype);
        const kcons = new SMTCallSimple(fcons, values);
        return new SMTCallSimple(`${llcons.cons}`, [new SMTConst(`(_ BV${k} ${this.vopts.ISize})`), kcons]);
    }

    processFillOperation(ltype: MIRType, count: SMTExp, value: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "fill");
        ops.consops.fill = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [value]);
    }

    processRangeOfIntOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfInt");
        this.rangeint = true;

        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end]);
    }

    processRangeOfNatOperation(ltype: MIRType, start: SMTExp, end: SMTExp, count: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "rangeOfNat");
        this.rangenat = true;
        
        return this.generateErrorPropConsCall(ltype, count, fcons, [start, end]);
    }

    processHasPredCheck(ltype: MIRType, code: string, l: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const op = this.generateDesCallNameUsing(this.temitter.getSMTTypeFor(ltype), "hasPredCheck", code);

        ops.dops.haspredcheck.add(op);
        return new SMTCallGeneral(op, [l]);
    }

    processGet(ltype: MIRType, l: SMTExp, n: SMTExp): SMTExp {
        this.ensureOpsFor(ltype);
        const op = this.generateDesCallName(this.temitter.getSMTTypeFor(ltype), "get");
        //get always registered

        return new SMTCallGeneral(op, [l, n]);
    }

    processConcat2(ltype: MIRType, l1: SMTExp, l2: SMTExp, count: SMTExp): SMTExp {
        const ops = this.ensureOpsFor(ltype);
        const fcons = this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "concat2");

        ops.consops.concat2 = true;
        return this.generateErrorPropConsCall(ltype, count, fcons, [l1, l2]);
    }

    generateConsCallName(ltype: SMTType, opname: string): string {
        return `@@cons_${ltype.name}_${opname}`;
    }

    generateConsCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `@@cons_${ltype.name}_${opname}_using_${code}`;
    }

    generateDesCallName(ltype: SMTType, opname: string): string {
        return `@@op_${ltype.name}_${opname}`;
    }

    generateDesCallNameUsing(ltype: SMTType, opname: string, code: string): string {
        return `@@op_${ltype.name}_${opname}_using_${code}`;
    }

    generateListSizeCall(larg: {vname: string, vtype: SMTType}): SMTExp {
        return new SMTCallSimple(`${larg.vtype.name}@size`, [new SMTVar(larg.vname)]);
    }

    generateErrorPropConsCall(ltype: MIRType, count: SMTExp, ullcons: string, args: SMTExp[]): SMTExp {
        const llcons = this.temitter.getSMTConstructorName(ltype);

        const tvar = this.generateTempName();
        return new SMTLet(tvar, new SMTCallGeneral(ullcons, args),
            new SMTIf(new SMTCallSimple("=", [new SMTVar(tvar), new SMTConst(this.generateConsCallName(this.temitter.getSMTTypeFor(ltype), "error"))]),
                this.temitter.generateErrorResultAssert(ltype),
                this.temitter.generateResultTypeConstructorSuccess(ltype, new SMTCallSimple(`${llcons.cons}`, [count, new SMTVar(tvar)]))
            )
        );
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
}

export {
    ListOpsManager
};
