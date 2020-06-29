//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
void* coerceUnionToBox_RefValue(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return ruv->udata;
}
void* coerceUnionToBox_BSQBool(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return BSQ_ENCODE_VALUE_BOOL(ruv->udata);
}
void* coerceUnionToBox_int64_t(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return BSQ_ENCODE_VALUE_TAGGED_INT(ruv->udata);
}
void* coerceUnionToBox_double(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    double dv = *((double*)ruv->udata);
    return Allocator::GlobalAllocator.valueNew<double>(META_DATA_LOAD_DECL(MetaData_double), dv);
}

void* ExtractGeneralRepr__double(void* v)
{
    double dval = *(double*)(GC_GET_FIRST_DATA_LOC(v));
    return Allocator::GlobalAllocator.objectNew<Boxed_double>(META_DATA_LOAD_DECL(MetaData_double), dval);
}
void* ExtractGeneralRepr_BSQISOTime(void* v)
{
    uint64_t tval = *(uint64_t*)(GC_GET_FIRST_DATA_LOC(v));
    return Allocator::GlobalAllocator.objectNew<Boxed_BSQISOTime>(META_DATA_LOAD_DECL(MetaData_BSQISOTime), tval);
}
void* ExtractGeneralRepr_Regex(void* v)
{
    std::wregex* rval = *(std::wregex**)(GC_GET_FIRST_DATA_LOC(v));
    return Allocator::GlobalAllocator.objectNew<Boxed_BSQISOTime>(META_DATA_LOAD_DECL(MetaData_BSQISOTime), rval);
}

std::wstring DisplayFunction_BSQByteBuffer(void* v)
{
    return DisplayFunctor_BSQByteBuffer{}(BSQ_GET_VALUE_PTR(v, BSQByteBuffer));
}
std::wstring DisplayFunction_BSQBuffer(void* v)
{
    return DisplayFunctor_BSQBuffer{}(BSQ_GET_VALUE_PTR(v, BSQBuffer));
}
std::wstring DisplayFunction_BSQBufferOf(void* v)
{
    return DisplayFunctor_BSQBufferOf{}(BSQ_GET_VALUE_PTR(v, BSQBufferOf));
}
std::wstring DisplayFunction_BSQISOTime(void* v)
{
    return DisplayFunctor_BSQISOTime{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQISOTime)->bval);
}
std::wstring DisplayFunction_Regex(void* v)
{
    return DisplayFunctor_BSQRegex{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQRegex)->bval);
}

MetaData* getMetaData(void* v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return META_DATA_LOAD_DECL(MetaData_NoneValue);
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return META_DATA_LOAD_DECL(MetaData_BSQBool);
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return META_DATA_LOAD_DECL(MetaData_int64_t);
    }
    else
    {
        return GET_TYPE_META_DATA(v);
    }
}

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2)
{
    if(v1 == v2) 
    {
        return true;
    }

    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) 
    {
        return false;
    }

    return kt1->eq(v1, v2);
}

bool bsqKeyValueLess(KeyValue v1, KeyValue v2)
{
    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) 
    {
        return kt1->nominaltype < kt2->nominaltype;
    }

    return kt1->less(v1, v2);
}

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_ALL_FLAG;
    }
    else {
        auto rcategory = GET_TYPE_META_DATA(v)->nominaltype;
        if(rcategory == MIRNominalTypeEnum_Tuple) {
            return BSQ_GET_VALUE_PTR(v, BSQTuple)->flag;
        }
        else if(rcategory == MIRNominalTypeEnum_Record) {
            return BSQ_GET_VALUE_PTR(v, BSQRecord)->flag;
        }
        else {
            return GET_TYPE_META_DATA(v)->dataflag;
        }
    }
}

std::wstring diagnostic_format(void* v)
{
    MetaData* mdata = getMetaData(v);
    return mdata->displayFP(v);
}
}
