//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqkeyvalues.h"

namespace BSQ
{
    BSQBigInt BSQBigInt::negate(const BSQBigInt& v)
    {
        return BSQBigInt{nullptr, -v.simpleint};
    }

    bool BSQBigInt::eq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return l.simpleint == r.simpleint;
    }

    bool BSQBigInt::lt(const BSQBigInt& l, const BSQBigInt& r)
    {
        return l.simpleint < r.simpleint;
    }

    BSQBigInt BSQBigInt::add(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint + r.simpleint};
    }

    BSQBigInt BSQBigInt::sub(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint - r.simpleint};
    }

    BSQBigInt BSQBigInt::mult(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint * r.simpleint};
    }

    BSQBigInt BSQBigInt::div(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint / r.simpleint};
    }

    BSQBigInt BSQBigInt::mod(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{nullptr, l.simpleint % r.simpleint};
    }

    void* coerceUnionToBox_BSQBigInt(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQBigInt>(META_DATA_LOAD_DECL(MetaData_BigInt), ruv->udata);
    }

    void* coerceUnionToBox_BSQString(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQString>(META_DATA_LOAD_DECL(MetaData_String), ruv->udata);
    }

    void* coerceUnionToBox_BSQSafeString(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQString>(ruv->umeta, ruv->udata);
    }

    void* coerceUnionToBox_BSQStringOf(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQString>(ruv->umeta, ruv->udata);
    }

    void* coerceUnionToBox_BSQUUID(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQUUID>(META_DATA_LOAD_DECL(MetaData_UUID), ruv->udata);
    }

    void* coerceUnionToBox_BSQLogicalTime(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQLogicalTime>(META_DATA_LOAD_DECL(MetaData_LogicalTime), ruv->udata);
    }
    
    void* coerceUnionToBox_BSQEnum(void* uv)
    {
        UnionValue* ruv = (UnionValue*)uv;
        return Allocator::GlobalAllocator.copyNew<BSQEnum>(ruv->umeta, ruv->udata);
    }
}
