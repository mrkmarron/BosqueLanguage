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
}

class SMTVar extends SMTExp {
    readonly vname: string;

    constructor(vname: string) {
        super();

        this.vname = vname;
    }
}

class SMTConst extends SMTExp {
    readonly cname: string;

    constructor(cname: string) {
        super();

        this.cname = cname;
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
}

class SMTCallGeneral extends SMTExp {
    readonly fname: string;
    readonly args: SMTExp[];

    constructor(fname: string, args: SMTExp[]) {
        super();

        this.fname = fname;
        this.args = args;
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
}

class SMTLetMulti extends SMTExp {
    readonly assigns: { vname: string, value: SMTExp }[];
    readonly inexp: SMTExp

    constructor(assigns: { vname: string, value: SMTExp }[], inexp: SMTExp) {
        super();

        this.assigns = assigns;
        this.inexp = inexp;
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
}

class SMTCond extends SMTExp {
    readonly mvar: SMTExp;
    readonly opts: {test: SMTExp, result: SMTExp}[];
    readonly orelse: SMTExp;

    constructor(mvar: SMTExp, opts: {test: SMTExp, result: SMTExp}[], orelse: SMTExp) {
        super();

        this.mvar = mvar;
        this.opts = opts;
        this.orelse = orelse;
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
}

export {
    VerifierLevel,
    SMTMaskConstruct,
    SMTType, SMTExp, SMTVar, SMTConst, 
    SMTCallSimple, SMTCallGeneral, SMTCallGeneralWOptMask, SMTCallGeneralWPassThroughMask,
    SMTLet, SMTLetMulti, SMTIf, SMTCond,
    SMTAxiom, SMTErrorAxiom
};
