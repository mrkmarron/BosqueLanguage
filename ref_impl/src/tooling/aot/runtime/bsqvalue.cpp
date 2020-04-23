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

MIRNominalTypeEnum getNominalTypeOf_KeyValue(KeyValue v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return MIRNominalTypeEnum_None;
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return MIRNominalTypeEnum_Bool;
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return MIRNominalTypeEnum_Int;
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
        return ptr->nominalType;
    }
}

MIRNominalTypeEnum getNominalTypeOf_Value(Value v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return MIRNominalTypeEnum_None;
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return MIRNominalTypeEnum_Bool;
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return MIRNominalTypeEnum_Int;
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
        return ptr->nominalType;
    }
}

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2)
{
    if(v1 == v2) {
        return true;
    }

    if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
    {
        return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONE(v2);
    }
    else if(BSQ_IS_VALUE_BOOL(v1) && BSQ_IS_VALUE_BOOL(v2))
    {
        return EqualFunctor_bool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v1) || BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return EqualFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return false;
        }
        
        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr1->nominalType);
        switch(rcategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::eq(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyEqual(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyEqual(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyEqual(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyEqual(dynamic_cast<Boxed_BSQUUID*>(ptr1)->bval, dynamic_cast<Boxed_BSQUUID*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyEqual(dynamic_cast<Boxed_BSQLogicalTime*>(ptr1)->bval, dynamic_cast<Boxed_BSQLogicalTime*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyEqual(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyEqual(dynamic_cast<Boxed_BSQEnum*>(ptr1)->bval, dynamic_cast<Boxed_BSQEnum*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyEqual(dynamic_cast<Boxed_BSQIdKeySimple*>(ptr1)->bval, dynamic_cast<Boxed_BSQIdKeySimple*>(ptr2)->bval);
            default:
                return BSQIdKeyCompound::keyEqual(dynamic_cast<BSQIdKeyCompound*>(ptr1), dynamic_cast<BSQIdKeyCompound*>(ptr2));
        }
    }
}

bool bsqKeyValueLess(KeyValue v1, KeyValue v2)
{
    if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
    {
        return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONNONE(v2);
    }
    else if(BSQ_IS_VALUE_BOOL(v1) && BSQ_IS_VALUE_BOOL(v2))
    {
        return LessFunctor_bool{}(BSQ_GET_VALUE_BOOL(v1), BSQ_GET_VALUE_BOOL(v2));
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v1) || BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return LessFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v1), BSQ_GET_VALUE_TAGGED_INT(v2));
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef);

        if(ptr1->nominalType != ptr2->nominalType)
        {
            return ptr1->nominalType < ptr2->nominalType;
        }
        
        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr1->nominalType);
        switch(rcategory)
        {
            case MIRNominalTypeEnum_Category_BigInt:
                return BSQBigInt::lt(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
            case MIRNominalTypeEnum_Category_String:
                return BSQString::keyLess(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
            case MIRNominalTypeEnum_Category_SafeString:
                return BSQSafeString::keyLess(dynamic_cast<BSQSafeString*>(ptr1), dynamic_cast<BSQSafeString*>(ptr2));
            case MIRNominalTypeEnum_Category_StringOf:
                return BSQStringOf::keyLess(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
            case MIRNominalTypeEnum_Category_UUID:
                return BSQUUID::keyLess(dynamic_cast<Boxed_BSQUUID*>(ptr1)->bval, dynamic_cast<Boxed_BSQUUID*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_LogicalTime:
                return BSQLogicalTime::keyLess(dynamic_cast<Boxed_BSQLogicalTime*>(ptr1)->bval, dynamic_cast<Boxed_BSQLogicalTime*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_CryptoHash:
                return BSQCryptoHash::keyLess(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
            case MIRNominalTypeEnum_Category_Enum:
                return BSQEnum::keyLess(dynamic_cast<Boxed_BSQEnum*>(ptr1)->bval, dynamic_cast<Boxed_BSQEnum*>(ptr2)->bval);
            case MIRNominalTypeEnum_Category_IdKeySimple:
                return BSQIdKeySimple::keyLess(dynamic_cast<Boxed_BSQIdKeySimple*>(ptr1)->bval, dynamic_cast<Boxed_BSQIdKeySimple*>(ptr2)->bval);
            default:
                return BSQIdKeyCompound::keyLess(dynamic_cast<BSQIdKeyCompound*>(ptr1), dynamic_cast<BSQIdKeyCompound*>(ptr2));
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
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);

        auto rcategory = GET_MIR_TYPE_CATEGORY(ptr->nominalType);
        if(rcategory == MIRNominalTypeEnum_Category_Tuple) {
            return dynamic_cast<Boxed_BSQTuple*>(ptr)->bval.flag;
        }
        else if(rcategory == MIRNominalTypeEnum_Category_Record) {
            return dynamic_cast<Boxed_BSQRecord*>(ptr)->bval.flag;
        }
        else {
            return nominalDataKinds[GET_MIR_TYPE_POSITION(getNominalTypeOf_Value(v))];
        }
    }
}

std::u32string diagnostic_format(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return std::u32string(U"none");
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? std::u32string(U"true") : std::u32string(U"false");
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(std::to_string(BSQ_GET_VALUE_TAGGED_INT(v)));
    }
    else
    {
        BSQRef* vv = BSQ_GET_VALUE_PTR(v, BSQRef);
    
        auto rcategory = GET_MIR_TYPE_CATEGORY(vv->nominalType);
        switch(rcategory)
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
                return DisplayFunctor_BSQIdKeyCompound{}(dynamic_cast<BSQIdKeyCompound*>(vv));
        }



        if(dynamic_cast<const BSQBigInt*>(vv) != nullptr)
        {
            return dynamic_cast<const BSQBigInt*>(vv)->display();
        }
        else if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQString{}(dynamic_cast<const BSQString*>(vv));
        }
        else if(dynamic_cast<const BSQSafeString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQSafeString{}(dynamic_cast<const BSQSafeString*>(vv));
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQStringOf{}(dynamic_cast<const BSQStringOf*>(vv));
        }
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUID{}(dynamic_cast<const BSQGUID*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQCryptoHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQCryptoHash{}(dynamic_cast<const BSQCryptoHash*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQLogicalTime*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQLogicalTime{}(*dynamic_cast<const BSQLogicalTime*>(vv));
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQEnum{}(*dynamic_cast<const BSQEnum*>(vv));
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQIdKey{}(dynamic_cast<const BSQIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQGUIDIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUIDIdKey{}(dynamic_cast<const BSQGUIDIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQContentHashIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQContentHashIdKey{}(dynamic_cast<const BSQContentHashIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQBuffer*>(vv) != nullptr)
        {
            auto pbuf = dynamic_cast<const BSQBuffer*>(vv);
            std::u32string rvals(U"PODBuffer{");
            for (size_t i = 0; i < pbuf->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += pbuf->sdata[i];
            }
            rvals += U"}";

            return rvals;
        }
        else if(dynamic_cast<const BSQISOTime*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            return std::u32string{U"ISOTime="} + conv.from_bytes(std::to_string(dynamic_cast<const BSQISOTime*>(vv)->isotime)) + U"}";
        }
        else if(dynamic_cast<const BSQRegex*>(vv) != nullptr)
        {
            return std::u32string{U"Regex="} + dynamic_cast<const BSQRegex*>(vv)->re;
        }
        else if(dynamic_cast<const BSQTuple*>(vv) != nullptr)
        {
            auto tv = dynamic_cast<const BSQTuple*>(vv);
            std::u32string tvals(U"[");
            for(size_t i = 0; i < tv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    tvals += U", ";
                }

                tvals += diagnostic_format(tv->entries.at(i));
            }
            tvals += U"]";

            return tvals;
        }
        else if(dynamic_cast<const BSQRecord*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

            auto rv = dynamic_cast<const BSQRecord*>(vv);
            std::u32string rvals(U"{");
            bool first = true;
            for(auto iter = rv->entries.cbegin(); iter != rv->entries.cend(); ++iter)
            {
                if(!first)
                {
                    rvals += U", ";
                }
                first = false;

                rvals += conv.from_bytes(propertyNames[(int32_t)iter->first]) + U"=" + diagnostic_format(iter->second);
            }
            rvals += U"}";

            return rvals;
        }
        else
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            
            auto obj = dynamic_cast<const BSQObject*>(vv);
            return conv.from_bytes(nominaltypenames[(uint32_t) obj->nominalType]) + obj->display();
        }
    }
}
}