//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

type TypeEncodingOpPack = {
    RCIncFunctor: string,
    RCDecFunctor: string,
    DisplayFunctor: string
}

type TypeEncodingOpPackKey = {
    EqualFunctor: string,
    LessFunctor: string
}

type TypeEncodingOpPackStruct = {
    RCReturnFunctor: string
}

abstract class TypeRepr {
    readonly iskey: boolean;
    readonly base: string;
    readonly std: string;

    constructor(iskey: boolean, base: string, std: string) {
        this.iskey = iskey;
        this.base = base;
        this.std = std;
    }
}

class NoneRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue");
    }
}

class StructRepr extends TypeRepr {
    readonly boxed: string;

    constructor(iskey: boolean, base: string, boxed: string) {
        super(iskey, base, base);
        this.boxed = boxed;
    }
}

class RefRepr extends TypeRepr {
    constructor(iskey: boolean, base: string, std: string) {
        super(iskey, base, std);
    }
}

class KeyValueRepr extends TypeRepr {
    constructor() {
        super(true, "KeyValue", "KeyValue");
    }
}

class ValueRepr extends TypeRepr {
    constructor() {
        super(false, "Value", "Value");
    }
}

class EphemeralListRepr extends TypeRepr {
    constructor(base: string) {
        super(false, base, base + "*");
    }
}

class UnionRepr extends TypeRepr {
    readonly opts: TypeRepr[];

    constructor(iskey: boolean, repr: string, opts: TypeRepr[]) {
        super(iskey, repr, repr);
        this.opts = opts;
    }

    static create(...trl: TypeRepr[]): UnionRepr {
        assert(trl.length > 1);
        assert(trl.every((opt) => opt instanceof NoneRepr || opt instanceof StructRepr));

        trl.sort((a, b) => a.base.localeCompare(b.base));

        const iskey = trl.every((tr) => tr.iskey);
        const repr = `std::variant<${trl.map((tr) => tr.std).join(", ")}>`;

        return new UnionRepr(iskey, repr, trl);
    }

    extendRepr(tr: TypeRepr): TypeRepr {
        if (tr instanceof NoneRepr) {
            return UnionRepr.create(tr, ...this.opts);
        }
        else if (tr instanceof StructRepr) {
            return UnionRepr.create(tr, ...this.opts);
        }
        else {
            if (this.iskey && tr.iskey) {
                return new KeyValueRepr();
            }
            else {
                return new ValueRepr();
            }
        }
    }
}

function joinTypeRepr(tr1: TypeRepr, tr2: TypeRepr): TypeRepr {
    assert(!(tr1 instanceof UnionRepr) && !(tr2 instanceof UnionRepr), "Use extend instead!!!");

    if(tr1.base === tr2.base) {
        return tr1;
    }

    if (tr1 instanceof NoneRepr) {
        if (tr2 instanceof NoneRepr) {
            return new NoneRepr();
        }
        else if (tr2 instanceof StructRepr) {
            return UnionRepr.create(tr1, tr2);
        }
        else if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
    else if (tr1 instanceof StructRepr) {
        if (tr2 instanceof NoneRepr) {
            return UnionRepr.create(tr1, tr2);
        }
        else if (tr2 instanceof StructRepr) {
            return UnionRepr.create(tr1, tr2);
        }
        else if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
    else {
        if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
}

function joinTypeReprs(...trl: TypeRepr[]): TypeRepr {
    assert(trl.length > 1);

    let ctype = trl[0];
    for(let i = 1; i < trl.length; ++i) {
        if(ctype instanceof UnionRepr) {
            ctype = ctype.extendRepr(trl[i]);
        }
        else {
            ctype = joinTypeRepr(ctype, trl[i]);
        }
    }

    return ctype;
}

export {
    TypeEncodingOpPack, TypeEncodingOpPackKey, TypeEncodingOpPackStruct,
    TypeRepr, NoneRepr, StructRepr, RefRepr, KeyValueRepr, ValueRepr, EphemeralListRepr, UnionRepr,
    joinTypeReprs
};
