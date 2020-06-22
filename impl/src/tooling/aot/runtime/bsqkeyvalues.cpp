//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqkeyvalues.h"

namespace BSQ
{
    BSQBigInt BSQBigInt::negate(const BSQBigInt& v)
    {
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, -v.simpleint};
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
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, l.simpleint + r.simpleint};
    }

    BSQBigInt BSQBigInt::sub(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, l.simpleint - r.simpleint};
    }

    BSQBigInt BSQBigInt::mult(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, l.simpleint * r.simpleint};
    }

    BSQBigInt BSQBigInt::div(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, l.simpleint / r.simpleint};
    }

    BSQBigInt BSQBigInt::mod(const BSQBigInt& l, const BSQBigInt& r)
    {
        return BSQBigInt{META_DATA_LOAD_DECL(MetaData_BSQBigInt), nullptr, l.simpleint % r.simpleint};
    }

    void* ExtractGeneralRepr_BSQBigInt(void* v)
    {
        BSQBigInt ival = *(BSQBigInt*)(GC_GET_FIRST_DATA_LOC(v));
        return Allocator::GlobalAllocator.objectNew<Boxed_BigInt>(META_DATA_LOAD_DECL(MetaData_BSQBigInt), ival);
    }

    std::wstring DisplayFunction_BSQBigInt(void* v)
    {
        return DisplayFunctor_BSQBigInt{}(BSQ_GET_VALUE_PTR(v, Boxed_BigInt)->bval);
    }

    std::wstring DisplayFunction_BSQString(void* v)
    {
        return DisplayFunctor_BSQString{}(BSQ_GET_VALUE_PTR(v, BSQString));
    }
}
