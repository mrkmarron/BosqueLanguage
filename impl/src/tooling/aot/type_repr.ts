//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

abstract class TypeRepr {
    readonly iskey: boolean;
    
    readonly base: string;
    readonly std: string;

    readonly metadataName: string;
    readonly hasPointers: boolean;
    readonly realSize: number;
    readonly alignedSize: number;
    readonly packedPtrCount: number;
    readonly layoutmask: number[];

    constructor(iskey: boolean, base: string, std: string, metadataName: string, hasPointers: boolean, realSize: number, alignedSize: number, packedPtrCount: number, layoutmask: number[]) {
        this.iskey = iskey;
        this.base = base;
        this.std = std;
        
        this.metadataName = metadataName;
        this.hasPointers = hasPointers;
        this.realSize = realSize;
        this.alignedSize = alignedSize;
        this.packedPtrCount = packedPtrCount;
        this.layoutmask = layoutmask;
    }
}

class NoneRepr extends TypeRepr {
    constructor() {
        super(true, "NoneValue", "NoneValue", "MIRNominalTypeEnum_Category_Empty");
    }
}

class StructRepr extends TypeRepr {
    readonly boxed: string;
    readonly nominaltype: string;

    constructor(iskey: boolean, base: string, boxed: string, nominaltype: string, categoryinfo: string) {
        super(iskey, base, base, categoryinfo);
        this.boxed = boxed;
        this.nominaltype = nominaltype;
    }
}

class RefRepr extends TypeRepr {
    constructor(iskey: boolean, base: string, std: string, categoryinfo: string) {
        super(iskey, base, std, categoryinfo);
    }
}

class UnionRepr extends TypeRepr {
    readonly oftypes: (NoneRepr | StructRepr | RefRepr)[];

    constructor(iskey: boolean, hasPointers: boolean, realSize: number, alignedSize: number, oftypes: (NoneRepr | StructRepr | RefRepr)[]) {
        super(iskey, "UnionValue", "UnionValue", "[NO META]", hasPointers, realSize, alignedSize, -1, []);

        this.oftypes = oftypes;
    }

    static create(oftypes: (NoneRepr | StructRepr | RefRepr)[]): TypeRepr {
        const iskey = oftypes.every((tr) => tr.iskey);
        const hasptrs = oftypes.some((tr) => tr.hasPointers);
        const realSize = oftypes.reduce((acc, v) => Math.max(acc, v.realSize), 0) + 4;
        const alignedSize = oftypes.reduce((acc, v) => Math.max(acc, v.alignedSize), 0) + 4;

        return new UnionRepr(iskey, hasptrs, realSize, alignedSize, oftypes);
    }
}

class KeyValueRepr extends TypeRepr {
    constructor() {
        super(true, "KeyValue", "KeyValue", "MIRNominalTypeEnum_Category_Empty");
    }
}

class ValueRepr extends TypeRepr {
    constructor() {
        super(false, "Value", "Value", "MIRNominalTypeEnum_Category_Empty");
    }
}

class EphemeralListRepr extends TypeRepr {
    constructor(base: string) {
        super(false, base, base, "MIRNominalTypeEnum_Category_Empty");
    }
}

function joinTypeRepr(tr1: TypeRepr, tr2: TypeRepr): TypeRepr {
    if(tr1.base === tr2.base) {
        return tr1;
    }

    xxxx; //Union types!!!
    
    if (tr1 instanceof NoneRepr) {
        if (tr2 instanceof NoneRepr) {
            return new NoneRepr();
        }
        else if (tr1.iskey && tr2.iskey) {
            return new KeyValueRepr();
        }
        else {
            return new ValueRepr();
        }
    }
    else if (tr1 instanceof StructRepr) {
        if (tr1.iskey && tr2.iskey) {
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
        ctype = joinTypeRepr(ctype, trl[i]);
    }

    return ctype;
}

export {
    TypeRepr, NoneRepr, StructRepr, RefRepr, UnionRepr, KeyValueRepr, ValueRepr, EphemeralListRepr,
    joinTypeReprs
};
