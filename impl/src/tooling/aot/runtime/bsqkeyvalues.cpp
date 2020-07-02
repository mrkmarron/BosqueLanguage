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



    void* ExtractGeneralRepr_BSQUUID(void* v)
    {
        BSQUUID* uuidval = (BSQUUID*)(GC_GET_FIRST_DATA_LOC(v));
        return Allocator::GlobalAllocator.objectNew<Boxed_BSQUUID>(META_DATA_LOAD_DECL(MetaData_BSQUUID), *uuidval);
    }

    void* ExtractGeneralRepr_BSQLogicalTime(void* v)
    {
        BSQLogicalTime* ltval = (BSQLogicalTime*)(GC_GET_FIRST_DATA_LOC(v));
        return Allocator::GlobalAllocator.objectNew<Boxed_BSQLogicalTime>(META_DATA_LOAD_DECL(MetaData_BSQLogicalTime), *ltval);
    }

    void* ExtractGeneralRepr_BSQEnum(void* v)
    {
        BSQEnum* eval = (BSQEnum*)(v);
        return Allocator::GlobalAllocator.objectNew<BSQEnum>(eval->mdata, eval->nominalType, eval->value);
    } 

    void* ExtractGeneralRepr_BSQIdKeySimple(void* v)
    {
        BSQIdKeySimple* idval = (BSQIdKeySimple*)(v);
        return Allocator::GlobalAllocator.objectNew<BSQIdKeySimple>(idval->mdata, idval->nominalType);
    }

    void* ExtractGeneralRepr_BSQIdKeyCompound(void* v)
    {
        BSQIdKeyCompound* idval = (BSQIdKeyCompound*)(v);
        return Allocator::GlobalAllocator.objectNewPl<BSQIdKeyCompound>();
    }

    std::wstring DisplayFunction_BSQBigInt(void* v)
    {
        return DisplayFunctor_BSQBigInt{}(BSQ_GET_VALUE_PTR(v, Boxed_BigInt)->bval);
    }

    std::wstring DisplayFunction_BSQString(void* v)
    {
        return DisplayFunctor_BSQString{}(BSQ_GET_VALUE_PTR(v, BSQString));
    }

    std::wstring DisplayFunction_BSQSafeString(void* v)
    {
        return DisplayFunctor_BSQSafeString{}(BSQ_GET_VALUE_PTR(v, BSQSafeString));
    }

    std::wstring DisplayFunction_BSQStringOf(void* v)
    {
        return DisplayFunctor_BSQStringOf{}(BSQ_GET_VALUE_PTR(v, BSQStringOf));
    }

    std::wstring DisplayFunction_BSQUUID(void* v)
    {
        return DisplayFunctor_BSQUUID{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQUUID)->bval);
    }
    
    std::wstring DisplayFunction_BSQLogicalTime(void* v)
    {
        return DisplayFunctor_BSQLogicalTime{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQLogicalTime)->bval);
    }

    std::wstring DisplayFunction_BSQCryptoHash(void* v)
    {
        return DisplayFunctor_BSQCryptoHash{}(BSQ_GET_VALUE_PTR(v, BSQCryptoHash));
    }
    
    std::wstring DisplayFunction_BSQEnum(void* v)
    {
        return DisplayFunctor_BSQEnum{}(*BSQ_GET_VALUE_PTR(v, BSQEnum));
    }

    std::wstring DisplayFunction_BSQIdKeyCompound(void* v)
    {
        return DisplayFunctor_BSQIdKeySimple{}(*BSQ_GET_VALUE_PTR(v, BSQIdKeySimple));
    }

    std::wstring DisplayFunction_BSQIdKeySimple(void* v)
    {
        return DisplayFunctor_BSQIdKeyCompound{}(*BSQ_GET_VALUE_PTR(v, BSQIdKeyCompound));
    }
}
