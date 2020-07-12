//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeRepr, NoneRepr, StructRepr, TRRepr, RefRepr, UnionRepr, KeyValueRepr, EphemeralListRepr, ValueRepr, PrimitiveRepr, StorageByteAlignment } from "./type_repr";

import * as assert from "assert";
import { CPPFrame } from "./cpp_frame";

enum CoerceKind {
    None,
    Direct,
    Convert,
    Construct,
    EphemeralConvert
}

function getRequiredCoerceOfPrimitive(trfrom: TypeRepr, trinto: TypeRepr): {kind: CoerceKind, alloc: number} {
    if(trfrom.mirtype.trkey === trinto.mirtype.trkey) {
        return {kind: CoerceKind.None, alloc: 0};
    }

    if(trfrom instanceof KeyValueRepr && trinto instanceof KeyValueRepr) {
        return {kind: CoerceKind.None, alloc: 0};
    }

    if(trfrom instanceof ValueRepr && trinto instanceof ValueRepr) {
        return {kind: CoerceKind.None, alloc: 0};
    }

    if (trfrom instanceof NoneRepr) {
        assert(!(trinto instanceof PrimitiveRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
    }
    else if (trfrom instanceof PrimitiveRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof PrimitiveRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            if(trinto.basetype === "double") {
                return {kind: CoerceKind.Construct, alloc: trfrom.alignedSize + StorageByteAlignment};
            }
            else {
                return {kind: CoerceKind.Direct, alloc: 0};
            }
        }
    }
    else if (trfrom instanceof StructRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof PrimitiveRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Construct, alloc: trfrom.alignedSize + StorageByteAlignment};
        }
    }
    else if (trfrom instanceof TRRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof PrimitiveRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");
        
        if(trinto instanceof TRRepr) {
            if (trinto.alignedSize === trfrom.alignedSize) {
                return {kind: CoerceKind.None, alloc: 0}; //types may differ but if the number of slots is the same then we can just reuse
            }
            else {
                return {kind: CoerceKind.Convert, alloc: 0};
            }
        }
        else if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Construct, alloc: trfrom.alignedSize + StorageByteAlignment};
        }
    }
    else if (trfrom instanceof RefRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof PrimitiveRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
    }
    else if(trfrom instanceof UnionRepr) {
        if(trinto instanceof NoneRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if(trinto instanceof PrimitiveRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if(trinto instanceof StructRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if(trinto instanceof TRRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if(trinto instanceof RefRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if(trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Construct, alloc: trfrom.alignedSize + StorageByteAlignment};
        }
    }
    else if (trfrom instanceof KeyValueRepr) {
        if (trinto instanceof NoneRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if(trinto instanceof PrimitiveRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if (trinto instanceof StructRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if(trinto instanceof TRRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if (trinto instanceof RefRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
    }
    else {
        if (trinto instanceof NoneRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if(trinto instanceof PrimitiveRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else if (trinto instanceof StructRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if(trinto instanceof TRRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if (trinto instanceof UnionRepr) {
            return {kind: CoerceKind.Convert, alloc: 0};
        }
        else if (trinto instanceof RefRepr) {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
        else {
            return {kind: CoerceKind.Direct, alloc: 0};
        }
    }
}

function getRequiredCoerce(trfrom: TypeRepr, trinto: TypeRepr): {kind: CoerceKind, alloc: number} {
    if(trfrom instanceof EphemeralListRepr && trinto instanceof EphemeralListRepr) {
        let allocs = 0;
        for(let i = 0; i < trfrom.elist.length; ++i) {
            const ccr = getRequiredCoerceOfPrimitive(trfrom.elist[i], trinto.elist[i]);
            allocs += ccr.alloc;
        }

        return {kind: CoerceKind.EphemeralConvert, alloc: allocs};
    }

    return getRequiredCoerceOfPrimitive(trfrom, trinto);
}

function coerceDirect(exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    if (trfrom instanceof NoneRepr) {
        return "BSQ_NONE_VALUE";
    }
    else if (trfrom instanceof PrimitiveRepr) {
        if(trinto.basetype === "BSQBool") {
            return `BSQ_ENCODE_VALUE_BOOL(${exp})`;
        }
        else {
            return `BSQ_ENCODE_VALUE_TAGGED_INT(${exp})`;
        }
    }
    else if (trfrom instanceof RefRepr) {
        return exp;
    }
    else if(trfrom instanceof UnionRepr) {
        if(trinto instanceof NoneRepr) {
            return "BSQ_NONE";
        }
        else if (trinto instanceof PrimitiveRepr) {
            return `${trfrom.basetype}::extractFromUnionPrimitive<${trinto.basetype}>(${exp})`;
        }
        else {
            return `${trfrom.basetype}::extractFromUnionPointer<${trinto.basetype}>(${exp})`;
        }
    }
    else if (trfrom instanceof KeyValueRepr) {
        if (trinto instanceof NoneRepr) {
            return "BSQ_NONE";
        }
        else if(trinto instanceof PrimitiveRepr) {
            if(trinto.basetype === "BSQBool") {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else {
                return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
            }
        }
        else if (trinto instanceof RefRepr) {
            return `(${trinto.storagetype})${exp}`;
        }
        else {
            return exp;
        }
    }
    else {
        if (trinto instanceof NoneRepr) {
            return "BSQ_NONE";
        }
        else if(trinto instanceof PrimitiveRepr) {
            if(trinto.basetype === "BSQBool") {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else if (trinto.basetype === "int64_t") {
                return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
            }
            else {
                return `*((double*)${exp})`;
            }
        }
        else if (trinto instanceof RefRepr) {
            return `(${trinto.storagetype})${exp}`;
        }
        else {
            return `(KeyValue)${exp}`;
        }
    }
}

function coerceConvert(trgt: string, exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    if (trfrom instanceof NoneRepr) {
        return `${trinto.basetype}::convertToUnionNone(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
    }
    else if (trfrom instanceof PrimitiveRepr) {
        return `${trinto.basetype}::convertToUnionPrimitive<${trfrom.basetype}>(${exp}, META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
    }
    else if (trfrom instanceof StructRepr) {
        return `${trinto.basetype}::convertToUnionStruct<${trfrom.basetype}>(${exp}, META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
    }
    else if (trfrom instanceof TRRepr) {
        if(trfrom.kind === "tuple") {
            if(trinto instanceof TRRepr) {
                return `${trinto.basetype}::convert<${trinto.elemcount}>(${exp}, ${trgt});`;
            }
            else {
                return `${trinto.basetype}::convertToUnionTuple<${trfrom.basetype}>(${exp}, META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
            }
        }
        else {
            if(trinto instanceof TRRepr) {
                return `${trinto.basetype}::convert<${trinto.elemcount}>(${exp}, ${trgt});`;
            }
            else {
                return `${trinto.basetype}::convertToUnionRecord<${trfrom.basetype}>(${exp}, META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
            }
        }
    }
    else if (trfrom instanceof RefRepr) {
        return `${trinto.basetype}::convertToUnionPointer<${trfrom.basetype}>(${exp}, META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trgt});`;
    }
    else if(trfrom instanceof UnionRepr) {
        if(trinto instanceof StructRepr) {
            return `${trfrom.basetype}::extractFromUnionStruct<${trinto.basetype}>(${exp}, ${trgt});`;
        }
        else if(trinto instanceof TRRepr) {
            if(trinto.kind === "tuple") {
                return `${trfrom.basetype}::extractFromUnionTuple<${trinto.basetype}>(${exp}, ${trgt});`;
            }
            else {
                return `${trfrom.basetype}::extractFromUnionRecord<${trinto.basetype}>(${exp}, ${trgt});`;
            }
        }
        else {
            return `${trfrom.basetype}::convert<${(trinto as UnionRepr).datasize}>(${exp}, ${trgt});`;
        }
    }
    else {
        if (trinto instanceof StructRepr) {
            return `GC_MEM_COPY(&${trgt}, ${exp}, GET_TYPE_META_DATA(&${exp})->datasize);`
        }
        else if(trinto instanceof TRRepr) {
            if(trinto.kind === "tuple") {
                return `${trinto.basetype}::unboxTuple(${exp}, ${trgt});`;
            }
            else {
                return `${trinto.basetype}::unboxRecord(${exp}, ${trgt});`;
            }
        }
        else {
            return `GET_TYPE_META_DATA(&${exp})->unionUnboxFromVal(${exp}, &${trgt});`;
        }
    }
}

function coerceConstruct(trgt: string, exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    if (trfrom instanceof PrimitiveRepr) {
        return `${trgt} = Allocator::GlobalAllocator.allocateSafePrimitive<${trfrom.basetype}>(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp});`;
    }
    else if (trfrom instanceof StructRepr) {
        return `${trgt} = Allocator::GlobalAllocator.allocateSafeStruct<${trfrom.basetype}>(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp});`;
    }
    else if (trfrom instanceof TRRepr) {
        if (trfrom.kind === "tuple") {
            return `${trfrom.basetype}::boxTuple(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp}, ${trgt});`;
        }
        else {
            return `${trfrom.basetype}::boxRecord(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp}, ${trgt});`;
        }
    }
    else {
        return `${trgt} = GET_TYPE_META_DATA(&${exp})->unionBoxFromVal(${exp});`;
    }
}

function coercePrimitive(cppframe: CPPFrame, exp: string, trfrom: TypeRepr, trinto: TypeRepr): [string, string[]] {
    const cop = getRequiredCoerce(trfrom, trinto);

    if(cop.kind === CoerceKind.None) {
        return [exp, []];
    }
    else if(cop.kind === CoerceKind.Direct) {
        return [coerceDirect(exp, trfrom, trinto), []];
    }
    else if(cop.kind === CoerceKind.Convert) {
        const tmp = cppframe.generateFreshName();
        cppframe.ensureLocationForVariable(tmp, trinto);

        return [tmp, [coerceConvert(tmp, exp, trfrom, trinto)]];
    }
    else {
        const tmp = cppframe.generateFreshName();
        cppframe.ensureLocationForVariable(tmp, trinto);

        return [tmp, [coerceConstruct(tmp, exp, trfrom, trinto)]];
    }
}

function coerce(cppframe: CPPFrame, exp: string, trfrom: TypeRepr, trinto: TypeRepr): [string, string[]] {
    if(trfrom instanceof EphemeralListRepr && trinto instanceof EphemeralListRepr) {
        const cop = getRequiredCoerce(trfrom, trinto);

        if(cop.kind === CoerceKind.None) {
            return [exp, []];
        }

        let cva: string[] = [];
        let ops: string[] = [];
        for(let i = 0; i < trfrom.elist.length; ++i) {
            const [icv, iops] = coercePrimitive(cppframe, `${exp}.entry_${i}`, trfrom.elist[i], trinto.elist[i]);
            cva.push(icv);
            ops = [...ops, ...iops];
        }

        const cexp = `{ ${cva.join(", ")} }`;
        return [cexp, ops];
    }

    return coercePrimitive(cppframe, exp, trfrom, trinto);
}

function assignCPPValue(trepr: TypeRepr, dst: string, src: string): string {
    if(trepr instanceof PrimitiveRepr) {
        return `${dst} = BSQ_NONE;`;
    }
    else if(trepr instanceof PrimitiveRepr) {
        return `${dst} = ${src};`;
    }
    else if(TRRepr instanceof StructRepr) {
        return `${dst} = ${src};`;
    }
    else if(TRRepr instanceof TRRepr) {
        return `GC_MEM_COPY(&${dst}, &${src}, ${trepr.alignedSize});`;
    }
    else if(TRRepr instanceof RefRepr) {
        return `${dst} = ${src};`;
    }
    else if(TRRepr instanceof UnionRepr) {
        return `GC_MEM_COPY(&${dst}, &${src}, ${trepr.alignedSize});`;
    }
    else if(TRRepr instanceof KeyValueRepr) {
        return `${dst} = ${src};`;
    }
    else if(TRRepr instanceof ValueRepr) {
        return `${dst} = ${src};`;
    }
    else {
        return `${dst} = ${src};`;
    }
}

function coerseAssignCPPValue(cppframe: CPPFrame, src: string, dst: string, trfrom: TypeRepr, trinto: TypeRepr): string[] {
    const cop = getRequiredCoerce(trfrom, trinto);

    if(cop.kind === CoerceKind.None) {
        return [assignCPPValue(trinto, dst, src)];
    }
    else if(cop.kind === CoerceKind.Direct) {
        return [assignCPPValue(trinto, dst, coerceDirect(src, trfrom, trinto))];
    }
    else if(cop.kind === CoerceKind.Convert) {
        return [coerceConvert(dst, src, trfrom, trinto)];
    }
    else if (cop.kind === CoerceKind.Construct) {
        return [coerceConstruct(dst, src, trfrom, trinto)];
    }
    else {
        let [ee, ops] = coerce(cppframe, src, trfrom, trinto);
        return [...ops, assignCPPValue(trinto, dst, ee)];
    }
}

function isDirectReturnValue(trepr: TypeRepr) {
    return trepr instanceof NoneRepr || trepr instanceof PrimitiveRepr || trepr instanceof RefRepr || trepr instanceof KeyValueRepr || trepr instanceof ValueRepr;
}

export {
    CoerceKind,
    getRequiredCoerce, coerce, assignCPPValue, coerseAssignCPPValue, isDirectReturnValue
};
