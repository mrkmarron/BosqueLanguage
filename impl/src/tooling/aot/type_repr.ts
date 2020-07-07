//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

enum LayoutMaskEnum {
    End = 0,
    Scalar = 1,
    Ptr = 2,
    Union = 4
};

const MemoryByteAlignment = 8;

abstract class TypeRepr {
    readonly iskey: boolean;
    readonly base: string;
    readonly storage: string;
    readonly passing: string;

    readonly isStack: boolean; //if this must always be stored in our shaddow stack
    readonly isSimpleAssignable: boolean; //if this is always void* or smaller (then we can just = assign instead of memcopy)

    readonly metadataName: string;
    readonly hasPointers: boolean;
    readonly realSize: number;
    readonly alignedSize: number;
    readonly packedPtrCount: number;
    readonly layoutmask: LayoutMaskEnum[];

    constructor(iskey: boolean, base: string, storage: string, passing: string, isstack: boolean, issimpleassign: boolean, metadataName: string, hasPointers: boolean, realSize: number, alignedSize: number, packedPtrCount: number, layoutmask: LayoutMaskEnum[]) {
        this.iskey = iskey;
        this.base = base;
        this.storage = storage;
        this.passing = passing;
        
        this.isStack = isstack;
        this.isSimpleAssignable = issimpleassign;

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
        super(true, "NoneValue", "NoneValue", false, true, "MetaData_None", false, MemoryByteAlignment, MemoryByteAlignment, -1, [LayoutMaskEnum.Scalar]);
    }
}

class StructRepr extends TypeRepr {
    constructor(iskey: boolean, base: string, boxed: string, nominaltype: string, categoryinfo: string) {
        super(iskey, base, base, categoryinfo);
        this.boxed = boxed;
        this.nominaltype = nominaltype;
    }
}

class TRRepr extends TypeRepr {
    readonly isTuple: boolean;
    readonly isRecord: boolean;

    constructor(iskey: boolean, base: string, boxed: string, nominaltype: string, categoryinfo: string) {
        //
        //todo -- size here is the BSQX size + the data elements size
        //
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
    readonly oftypes: (NoneRepr | StructRepr | TRRepr | RefRepr)[];
    readonly datasize: number;

    constructor(iskey: boolean, hasPointers: boolean, datasize: number, realSize: number, alignedSize: number, oftypes: (NoneRepr | StructRepr | RefRepr)[]) {
        super(iskey, "UnionValue", "UnionValue", true, false, "[NO META]", hasPointers, realSize, alignedSize, -1, []);

        this.oftypes = oftypes;
        this.datasize = datasize;
    }

    static create(oftypes: (NoneRepr | StructRepr | TRRepr | RefRepr)[]): TypeRepr {
        const iskey = oftypes.every((tr) => tr.iskey);
        const hasptrs = oftypes.some((tr) => tr.hasPointers);
        const datasize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.alignedSize), 0);
        const realSize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.realSize), 0) + 4;
        const alignedSize = oftypes.reduce((acc, v) => Math.max(acc, (v instanceof RefRepr) ? MemoryByteAlignment : v.alignedSize), 0) + 4;

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
    readonly elist: TypeRepr[];

    constructor(base: string) {
        super(false, base, base, "MIRNominalTypeEnum_Category_Empty");
    }
}

function joinTypeRepr(tr1: TypeRepr, tr2: TypeRepr): TypeRepr {
    if(tr1.base === tr2.base) {
        return tr1;
    }

    xxxx; //Union types and TR types!!!
    
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
    LayoutMaskEnum, TypeRepr, NoneRepr, StructRepr, TRRepr, RefRepr, UnionRepr, KeyValueRepr, ValueRepr, EphemeralListRepr,
    joinTypeReprs,
    MemoryByteAlignment
};
