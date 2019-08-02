//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRType } from "../../compiler/mir_assembly";

class SMTInfo {
    readonly literals = new Map<string, LiteralTerm>();
    readonly strings = new Map<string, LiteralTerm>();
    readonly consts = new Map<string, ConstantTerm>();
    readonly vars = new Map<string, NameTerm>();
    readonly funcs = new Map<string, { fname: string, argc: number }>();
}

abstract class Term {
    readonly key: string;
    readonly type: MIRType;

    constructor(key: string, type: MIRType) {
        this.key = key;
        this.type = type;
    }

    abstract smtify(info: SMTInfo): string;
}

class LiteralTerm extends Term {
    readonly value: undefined | boolean | number | string;

    private constructor(value: undefined | boolean | number | string, type: MIRType) {
        super(`Literal@${value}`, type);
        this.value = value;
    }

    smtify(info: SMTInfo): string {
        if (typeof (this.value) === "string") {
            if (!info.strings.has(this.value as string)) {
                info.strings.set(`String@${info.strings.size}`, this);
            }

            return `String@${info.strings.size - 1}`;
        }
        else {
            if (!info.literals.has(this.key)) {
                info.literals.set(this.key, this);
            }

            return this.key;
        }
    }
}

class ConstantTerm extends Term {
    readonly name: string;

    private constructor(name: string, type: MIRType) {
        super(`Constant@${name}`, type);
        this.name = name;
    }

    smtify(info: SMTInfo): string {
        if (!info.consts.has(this.key)) {
            info.consts.set(this.key, this);
        }

        return this.key;
    }
}

abstract class VTerm extends Term {

}

abstract class PCTerm extends Term {

}

class VariableTerm extends VTerm {
    readonly name: string;

    constructor(name: string, type: MIRType) {
        super(`Variable@${name}`, type);
        this.name = name;
    }

    smtify(info: SMTInfo): string {
        if (!info.vars.has(this.key)) {
            info.vars.set(this.key, this);
        }

        return this.key;
    }
}

class ExistentialVariableTerm extends VTerm {
    readonly name: string;

    constructor(name: string, type: MIRType) {
        super(`ExistV@${name}`, type);
        this.name = name;
    }

    smtify(info: SMTInfo): string {
        if (!info.vars.has(this.key)) {
            info.vars.set(this.key, this);
        }

        return this.key;
    }
}

class PCodeTerm extends PCTerm {
    readonly name: string;

    constructor(name: string, type: MIRType) {
        super(`PCode@${name}`, type);
        this.name = name;
    }

    smtify(info: SMTInfo): string {
        if (!info.vars.has(this.key)) {
            info.vars.set(this.key, this);
        }

        return this.key;
    }
}

class ExistentialPCodeTerm extends PCTerm {
    readonly name: string;

    constructor(name: string, type: MIRType) {
        super(`ExistPC@${name}`, type);
        this.name = name;
    }

    smtify(info: SMTInfo): string {
        if (!info.vars.has(this.key)) {
            info.vars.set(this.key, this);
        }

        return this.key;
    }
}

class FunctionTerm extends Term {
    readonly fname: PCTerm;
    readonly args: Term[];

    constructor(fname: PCTerm, args: Term[], type: MIRType) {
        super(`Function@${fname.key}`, type);
        this.fname = fname;
        this.args = args;
    }

    smtify(info: SMTInfo): string {
        if (!info.funcs.has(this.fname.key)) {
            info.funcs.set(this.fname.key, { fname: this.fname.key, argc: this.args.length });
        }

        return `(${[this.fname.key, ...this.args.map((arg) => arg.smtify(info))].join(" ")})`;
    }
}

class Equality {
    readonly op: "=" | "<>";
    readonly lhs: Term;
    readonly rhs: Term;
}

class Implication {
    readonly guards: Equality[];
    readonly implication: Equality[];
}
