//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
BSQTuple BSQTuple::_empty({}, DATA_KIND_ALL_FLAG);
BSQRecord BSQRecord::_empty({}, DATA_KIND_ALL_FLAG);

void* ExtractGeneralRepr_Identity(void* v)
{
    return (*((void**)GC_GET_FIRST_DATA_LOC(v)));
}
void* ExtractGeneralRepr_BSQBool(void* v)
{
    return BSQ_ENCODE_VALUE_BOOL(*(BSQBool*)(GC_GET_FIRST_DATA_LOC(v)));
}
void* ExtractGeneralRepr__int64_t(void* v)
{
    return BSQ_ENCODE_VALUE_TAGGED_INT(*(int64_t*)(GC_GET_FIRST_DATA_LOC(v)));
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
    std::wregex rval = *(std::wregex**)(GC_GET_FIRST_DATA_LOC(v));
    return Allocator::GlobalAllocator.objectNew<Boxed_BSQISOTime>(META_DATA_LOAD_DECL(MetaData_BSQISOTime), tval);
}

std::wstring DisplayFunction_NoneValue(void* v)
{
    return DisplayFunctor_NoneValue{}((NoneValue)v);
}
std::wstring DisplayFunction_BSQBool(void* v)
{
    return DisplayFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(v));
}
std::wstring DisplayFunction_int64_t(void* v)
{
    return DisplayFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v));
}
std::wstring DisplayFunction_double(void* v)
{
    return DisplayFunctor_double{}(BSQ_GET_VALUE_PTR(v, Boxed_double)->bval);
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
    return DisplayFunction_BSQISOTime{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQISOTime)->bval);
}
std::wstring DisplayFunction_Regex(void* v)
{
    return DisplayFunction_BSQRegex{}(BSQ_GET_VALUE_PTR(v, Boxed_BSQRegex)->bval)
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
    if(v1 == v2) {
        return true;
    }

    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) {
        return false;
    }

    if((kt1 == META_DATA_LOAD_DECL(MetaData_NoneValue)) & (kt2 == META_DATA_LOAD_DECL(MetaData_NoneValue)))
    {
        return true;
    }
    else if((kt1 == META_DATA_LOAD_DECL(MetaData_BSQBool)) & (kt2 == META_DATA_LOAD_DECL(MetaData_BSQBool)))
    {
        return EqualFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if((kt1 == META_DATA_LOAD_DECL(MetaData_int64_t)) & (kt2 == META_DATA_LOAD_DECL(MetaData_int64_t)))
    {
        return EqualFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, void*); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, void*);

        switch(kt1->typecategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::eq(BSQ_GET_VALUE_PTR(v1, BSQBigInt), BSQ_GET_VALUE_PTR(v2, BSQBigInt));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyEqual(BSQ_GET_VALUE_PTR(v1, BSQString), BSQ_GET_VALUE_PTR(v2, BSQString));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyEqual(BSQ_GET_VALUE_PTR(v1, BSQSafeString), BSQ_GET_VALUE_PTR(v2, BSQSafeString));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyEqual(BSQ_GET_VALUE_PTR(v1, BSQStringOf), BSQ_GET_VALUE_PTR(v2, BSQStringOf));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyEqual(BSQ_GET_VALUE_PTR(v1, Boxed_BSQUUID)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQUUID)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyEqual(BSQ_GET_VALUE_PTR(v1, Boxed_BSQLogicalTime)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQLogicalTime)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyEqual(BSQ_GET_VALUE_PTR(v1, BSQCryptoHash), BSQ_GET_VALUE_PTR(v2, BSQCryptoHash));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyEqual(BSQ_GET_VALUE_PTR(v1, Boxed_BSQEnum)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQEnum)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyEqual(BSQ_GET_VALUE_PTR(v1, Boxed_BSQIdKeySimple)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQIdKeySimple)->bval);
            default:
                return BSQIdKeyCompound::keyEqual(BSQ_GET_VALUE_PTR(v1, Boxed_BSQIdKeyCompound)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQIdKeyCompound)->bval);
        }
    }
}

bool bsqKeyValueLess(KeyValue v1, KeyValue v2)
{
    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) {
        return kt1->nominaltype < kt2->nominaltype;
    }

    if((kt1 == META_DATA_LOAD_DECL(MetaData_NoneValue)) & (kt2 == META_DATA_LOAD_DECL(MetaData_NoneValue)))
    {
        return false;
    }
    else if((kt1 == META_DATA_LOAD_DECL(MetaData_BSQBool)) & (kt2 == META_DATA_LOAD_DECL(MetaData_BSQBool)))
    {
        return LessFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if((kt1 == META_DATA_LOAD_DECL(MetaData_int64_t)) & (kt2 == META_DATA_LOAD_DECL(MetaData_int64_t)))
    {
        return LessFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        switch(kt1->typecategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::lt(BSQ_GET_VALUE_PTR(v1, BSQBigInt), BSQ_GET_VALUE_PTR(v2, BSQBigInt));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyLess(BSQ_GET_VALUE_PTR(v1, BSQString), BSQ_GET_VALUE_PTR(v2, BSQString));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyLess(BSQ_GET_VALUE_PTR(v1, BSQSafeString), BSQ_GET_VALUE_PTR(v2, BSQSafeString));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyLess(BSQ_GET_VALUE_PTR(v1, BSQStringOf), BSQ_GET_VALUE_PTR(v2, BSQStringOf));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyLess(BSQ_GET_VALUE_PTR(v1, Boxed_BSQUUID)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQUUID)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyLess(BSQ_GET_VALUE_PTR(v1, Boxed_BSQLogicalTime)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQLogicalTime)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyLess(BSQ_GET_VALUE_PTR(v1, BSQCryptoHash), BSQ_GET_VALUE_PTR(v2, BSQCryptoHash));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyLess(BSQ_GET_VALUE_PTR(v1, Boxed_BSQEnum)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQEnum)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyLess(BSQ_GET_VALUE_PTR(v1, Boxed_BSQIdKeySimple)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQIdKeySimple)->bval);
            default:
                return BSQIdKeyCompound::keyLess(BSQ_GET_VALUE_PTR(v1, Boxed_BSQIdKeyCompound)->bval, BSQ_GET_VALUE_PTR(v2, Boxed_BSQIdKeyCompound)->bval);
        }
    }
}

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_ALL_FLAG;
    }
    else {
        auto rcategory = GET_TYPE_META_DATA(v)->typecategory;
        if(rcategory == MIRNominalTypeEnum_Category_Tuple) {
            return BSQ_GET_VALUE_PTR(v, BSQTuple)->flag;
        }
        else if(rcategory == MIRNominalTypeEnum_Category_Record) {
            return BSQ_GET_VALUE_PTR(v, BSQRecord)->flag;
        }
        else {
            return GET_TYPE_META_DATA(v)->dataflag;
        }
    }
}

std::wstring diagnostic_format(void* v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return L"none";
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? L"true" : L"false";
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return std::to_wstring(BSQ_GET_VALUE_TAGGED_INT(v));
    }
    else
    {
        switch(GET_TYPE_META_DATA(v)->typecategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return DisplayFunctor_BSQBigInt{}(dynamic_cast<BSQBigInt*>(vv));
            case MIRNominalTypeEnum_Category_String:
                return DisplayFunctor_BSQString{}(dynamic_cast<BSQString*>(vv));
            case MIRNominalTypeEnum_Category_SafeString:
                return DisplayFunctor_BSQSafeString{}(dynamic_cast<BSQSafeString*>(vv));
            case MIRNominalTypeEnum_Category_StringOf:
                return DisplayFunctor_BSQStringOf{}(dynamic_cast<BSQStringOf*>(vv));
            case MIRNominalTypeEnum_Category_UUID:
                return DisplayFunctor_BSQUUID{}(dynamic_cast<Boxed_BSQUUID*>(vv)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return DisplayFunctor_BSQLogicalTime{}(dynamic_cast<Boxed_BSQLogicalTime*>(vv)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return DisplayFunctor_BSQCryptoHash{}(dynamic_cast<BSQCryptoHash*>(vv));
            case MIRNominalTypeEnum_Category_Enum:
                return DisplayFunctor_BSQEnum{}(dynamic_cast<Boxed_BSQEnum*>(vv)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return DisplayFunctor_BSQIdKeySimple{}(dynamic_cast<Boxed_BSQIdKeySimple*>(vv)->bval);
            case MIRNominalTypeEnum_Category_IdKeyCompound:
                return DisplayFunctor_BSQIdKeyCompound{}(dynamic_cast<Boxed_BSQIdKeyCompound*>(vv)->bval);
            case MIRNominalTypeEnum_Category_Float64:
                return DisplayFunctor_double{}(dynamic_cast<Boxed_double*>(vv)->bval);
            case MIRNominalTypeEnum_Category_ByteBuffer:
                return DisplayFunctor_BSQByteBuffer{}(dynamic_cast<BSQByteBuffer*>(vv));
            case MIRNominalTypeEnum_Category_Buffer:
                return DisplayFunctor_BSQBuffer{}(dynamic_cast<BSQBuffer*>(vv));
            case MIRNominalTypeEnum_Category_BufferOf:
                return DisplayFunctor_BSQBufferOf{}(dynamic_cast<BSQBufferOf*>(vv));
            case MIRNominalTypeEnum_Category_ISOTime:
                return DisplayFunctor_BSQISOTime{}(dynamic_cast<Boxed_BSQISOTime*>(vv)->bval);
            case MIRNominalTypeEnum_Category_Regex:
                return DisplayFunctor_BSQRegex{}(dynamic_cast<Boxed_BSQRegex*>(vv)->bval);
            case MIRNominalTypeEnum_Category_Tuple:
                return DisplayFunctor_BSQTuple{}(*dynamic_cast<BSQTuple*>(vv));
            case MIRNominalTypeEnum_Category_Record:
                return DisplayFunctor_BSQRecord{}(*dynamic_cast<BSQRecord*>(vv));
            default:
                return dynamic_cast<BSQObject*>(vv)->display();
        }
    }
}
}
