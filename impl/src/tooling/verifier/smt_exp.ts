//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

type VerifierLevel = "Weak" | "Strong";

class SMTMaskConstruct {
    readonly maskname: string;
    readonly entries: SMTExp[] = [];

    constructor(maskname: string) {
        this.maskname = maskname;
    }

    emitSMT2(): string {
        return `($Mask_${this.entries.length}@cons ${this.entries.map((mv) => mv.emitSMT2(undefined)).join(" ")})`;
    }
}

class SMTType {
    readonly name: string;
    
    constructor(name: string) {
        this.name = name;
    }

    isGeneralKeyType(): boolean {
        return this.name === "BKey";
    }

    isGeneralTermType(): boolean {
        return this.name === "BTerm";
    }
}

abstract class SMTExp {
    abstract emitSMT2(indent: string | undefined): string;
}

class SMTVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();

        this.vname = vname;
    }

    emitSMT2(indent: string | undefined): string {
        return this.vname;
    }
}

class SMTConst extends SMTExp {
    readonly cname: string;

    constructor(cname: string) {
        super();

        this.cname = cname;
    }

    emitSMT2(indent: string | undefined): string {
        return this.cname;
    }
}

class SMTCallSimple extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? this.fname : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")})`;
    }
}

class SMTCallGeneral extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? this.fname : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")})`;
    }
}

class SMTCallGeneralWOptMask extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];
    readonly mask: SMTMaskConstruct;

    constructor(fname: string, args: SMTExp[], mask: SMTMaskConstruct) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? `(${this.fname} ${this.mask.emitSMT2()})` : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")} ${this.mask.emitSMT2()})`;
    }
}

class SMTCallGeneralWPassThroughMask extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];
    readonly mask: string;

    constructor(fname: string, args: SMTExp[], mask: string) {
        super();

        this.fname = fname;
        this.args = args;
        this.mask = mask;
    }

    emitSMT2(indent: string | undefined): string {
        return this.args.length === 0 ? `(${this.fname} ${this.mask})` : `(${this.fname} ${this.args.map((arg) => arg.emitSMT2(undefined)).join(" ")} ${this.mask})`;
    }
}

class SMTLet extends SMTExp {
    readonly vname: string;
    readonly value: SMTExp;
    readonly inexp: SMTExp;

    constructor(vname: string, value: SMTExp, inexp: SMTExp) {
        super();

        this.vname = vname;
        this.value = value;
        this.inexp = inexp;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            return `(let ((${this.vname} ${this.value.emitSMT2(undefined)})) ${this.inexp.emitSMT2(undefined)})`;
        }
        else {
            return `(let ((${this.vname} ${this.value.emitSMT2(undefined)}))\n${indent + "  "}${this.inexp.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTLetMulti extends SMTExp {
    readonly assigns: { vname: string, value: SMTExp }[];
    readonly inexp: SMTExp

    constructor(assigns: { vname: string, value: SMTExp }[], inexp: SMTExp) {
        super();

        this.assigns = assigns;
        this.inexp = inexp;
    }

    emitSMT2(indent: string | undefined): string {
        const binds = this.assigns.map((asgn) => `(${asgn.vname} ${asgn.value.emitSMT2(undefined)})`);

        if (indent === undefined) {
            return `(let (${binds.join(" ")}) ${this.inexp.emitSMT2(undefined)})`;
        }
        else {
            return `(let (${binds.join(" ")})\n${indent + "  "}${this.inexp.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTIf extends SMTExp {
    readonly cond: SMTExp;
    readonly tval: SMTExp;
    readonly fval: SMTExp;

    constructor(cond: SMTExp, tval: SMTExp, fval: SMTExp) {
        super();

        this.cond = cond;
        this.tval = tval;
        this.fval = fval;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            return `(ite ${this.cond.emitSMT2(undefined)} ${this.tval.emitSMT2(undefined)} ${this.fval.emitSMT2(undefined)})`;
        }
        else {
            return `(ite ${this.cond.emitSMT2(undefined)}\n${indent + "  "}${this.tval.emitSMT2(indent + "  ")}\n${indent + "  "}${this.fval.emitSMT2(indent + "  ")}\n${indent})`;
        }
    }
}

class SMTCond extends SMTExp {
    readonly opts: {test: SMTExp, result: SMTExp}[];
    readonly orelse: SMTExp;

    constructor(opts: {test: SMTExp, result: SMTExp}[], orelse: SMTExp) {
        super();

        this.opts = opts;
        this.orelse = orelse;
    }

    emitSMT2(indent: string | undefined): string {
        if (indent === undefined) {
            let iopts: string = this.orelse.emitSMT2(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `(ite ${this.opts[i].test.emitSMT2(undefined)} ${this.opts[i].result.emitSMT2(undefined)} ${iopts})`
            }
            return iopts;
        }
        else {
            let iopts: string = this.orelse.emitSMT2(undefined);
            for(let i = this.opts.length - 1; i >= 0; --i) {
                iopts = `(ite ${this.opts[i].test.emitSMT2(undefined)}\n${indent + "  "}${this.opts[i].result.emitSMT2(indent + "  ")}\n${indent + "  "}${iopts}\n${indent})`
            }
            return iopts;
        }
    }
}

class SMTAxiom {
    readonly terms: { vname: string, vtype: SMTType }[];
    readonly guard: SMTExp | undefined;
    readonly clause: SMTExp;

    readonly identifier: string;
    readonly trigger: SMTExp | undefined;

    constructor(terms: { vname: string, vtype: SMTType }[], guard: SMTExp | undefined, clause: SMTExp, identifier: string, trigger: SMTExp | undefined) {
        this.terms = terms;
        this.guard = guard;
        this.clause = clause;

        this.identifier = identifier;
        this.trigger = trigger;
    }

    emitSMT2(): string {
        const terms = this.terms.map((t) => `(${t.vname} ${t.vtype.name})`);
        const guard = this.guard !== undefined ? this.guard.emitSMT2(undefined) : undefined;
        return `(assert (forall (${terms.join(" ")})${guard !== undefined ? ("\n    " + guard + " =>") : ""}\n    ${this.clause.emitSMT2(undefined)}\n))`
    }
}

class SMTErrorAxiom {
    readonly terms: { vname: string, vtype: SMTType }[];
    readonly erroridx: { vname: string, vtype: SMTType };
    readonly guard: SMTExp | undefined;
    readonly clause: SMTExp;

    readonly identifier: string;
    readonly trigger: SMTExp | undefined;

    constructor(terms: { vname: string, vtype: SMTType }[], erroridx: { vname: string, vtype: SMTType }, guard: SMTExp | undefined, clause: SMTExp, identifier: string, trigger: SMTExp | undefined) {
        this.terms = terms;
        this.erroridx = erroridx;
        this.guard = guard;
        this.clause = clause;

        this.identifier = identifier;
        this.trigger = trigger;
    }

    emitSMT2(): string {
        const terms = this.terms.map((t) => `(${t.vname} ${t.vtype.name})`);
        const guard = this.guard !== undefined ? this.guard.emitSMT2(undefined) : undefined;
        return `(assert (forall (${terms.join(" ")}) (exists (${this.erroridx.vname} ${this.erroridx.vtype.name})${guard !== undefined ? ("\n    " + guard + " =>") : ""}\n    ${this.clause.emitSMT2(undefined)}\n)))`
    }
}

export {
    VerifierLevel,
    SMTMaskConstruct,
    SMTType, SMTExp, SMTVar, SMTConst, 
    SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallGeneralWPassThroughMask,
    SMTLet, SMTLetMulti, SMTIf, SMTCond,
    SMTAxiom, SMTErrorAxiom
};
