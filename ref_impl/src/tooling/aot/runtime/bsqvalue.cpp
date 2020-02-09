//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#define COERSE_TO_BIG_INT(X) (BSQ_IS_VALUE_TAGGED_INT(X) ? BSQ_GET_VALUE_PTR(X, BSQBigInt) : BSQ_NEW_ADD_SCOPE(scope, BSQBigInt, BSQ_GET_VALUE_TAGGED_INT(X)))

namespace BSQ
{
BSQTuple* BSQTuple::_empty = INC_REF_DIRECT(BSQTuple, new BSQTuple({}, DATA_KIND_POD_FLAG));
BSQRecord* BSQRecord::_empty = INC_REF_DIRECT(BSQRecord, new BSQRecord({}, DATA_KIND_POD_FLAG));

bool op_intLessSlow(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    return BSQBigInt::lt(COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
}

bool op_intLess(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return v1 < v2;
    }

    return op_intLessSlow(scope, v1, v2);
}

bool op_intLessEqSlow(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    return BSQBigInt::lteq(COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
}

bool op_intLessEq(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        return v1 <= v2;
    }

    return op_intLessEqSlow(scope, v1, v2);
}

IntValue op_intNegate(BSQRefScope& scope, IntValue v)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return BSQ_ENCODE_VALUE_TAGGED_INT(-BSQ_GET_VALUE_TAGGED_INT(v));
    }
    
    return BSQBigInt::negate(scope, BSQ_GET_VALUE_PTR(v, BSQBigInt));
}

IntValue op_intAddSlow(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t res = BSQ_GET_VALUE_TAGGED_INT(v1) + BSQ_GET_VALUE_TAGGED_INT(v2);
        return BSQ_NEW_ADD_SCOPE(scope, BSQBigInt, res);
    }
    else
    {
        return BSQBigInt::add(scope, COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
    }
}

IntValue op_intAdd(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t res = BSQ_GET_VALUE_TAGGED_INT(v1) + BSQ_GET_VALUE_TAGGED_INT(v2);
        if((MIN_TAGGED <= res) & (res <= MAX_TAGGED))
        {
            return BSQ_ENCODE_VALUE_TAGGED_INT(res);
        }
    }

    return op_intAddSlow(scope, v1, v2);
}

IntValue op_intSubSlow(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t res = BSQ_GET_VALUE_TAGGED_INT(v1) - BSQ_GET_VALUE_TAGGED_INT(v2);
        return BSQ_NEW_ADD_SCOPE(scope, BSQBigInt, res);
    }
    else
    {
        return BSQBigInt::sub(scope, COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
    }
}

IntValue op_intSub(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t res = BSQ_GET_VALUE_TAGGED_INT(v1) - BSQ_GET_VALUE_TAGGED_INT(v2);
        if((MIN_TAGGED <= res) & (res <= MAX_TAGGED))
        {
            return BSQ_ENCODE_VALUE_TAGGED_INT(res);
        }
    }

    return op_intSubSlow(scope, v1, v2);
}

IntValue op_intMult(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t tv1 = BSQ_GET_VALUE_TAGGED_INT(v1);
        int64_t tv2 = BSQ_GET_VALUE_TAGGED_INT(v2);
        if((MIN_TAGGED_MULT <= tv1) & (tv1 <= MAX_TAGGED_MULT) & (MIN_TAGGED_MULT <= tv2) & (tv2 <= MAX_TAGGED_MULT))
        {
            int64_t res = tv1 * tv2;
            if((MIN_TAGGED <= res) & (res <= MAX_TAGGED))
            {
                return BSQ_ENCODE_VALUE_TAGGED_INT(res);
            }
        }
    }

    return BSQBigInt::mult(scope, COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
}

IntValue op_intDiv(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t tv1 = BSQ_GET_VALUE_TAGGED_INT(v1);
        int64_t tv2 = BSQ_GET_VALUE_TAGGED_INT(v2);
        if(tv2 == 0)
        {
            return nullptr;
        }
        else
        {
            return BSQ_ENCODE_VALUE_TAGGED_INT(tv1 / tv2);
        }
    }

    return BSQBigInt::div(scope, COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
}

IntValue op_intMod(BSQRefScope& scope, IntValue v1, IntValue v2)
{
    if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        int64_t tv1 = BSQ_GET_VALUE_TAGGED_INT(v1);
        int64_t tv2 = BSQ_GET_VALUE_TAGGED_INT(v2);
        if((tv1 < 0) | (tv2 <= 0))
        {
            return nullptr;
        }
        else
        {
            return BSQ_ENCODE_VALUE_TAGGED_INT(tv1 % tv2);
        }
    }

    return BSQBigInt::mod(scope, COERSE_TO_BIG_INT(v1), COERSE_TO_BIG_INT(v2));
}

size_t bsqKeyValueHash(KeyValue v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return 0;
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return (size_t)BSQ_GET_VALUE_BOOL(v);
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return BSQ_GET_VALUE_TAGGED_INT(v);
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef); 
        if(dynamic_cast<BSQBigInt*>(ptr) != nullptr)
        {
            return dynamic_cast<BSQBigInt*>(ptr)->hash();
        }
        else if(dynamic_cast<BSQString*>(ptr) != nullptr)
        {
            return BSQString::hash(dynamic_cast<BSQString*>(ptr));
        }
         else if(dynamic_cast<BSQValidatedString*>(ptr) != nullptr)
        {
            return BSQValidatedString::hash(dynamic_cast<BSQValidatedString*>(ptr));
        }
        else if(dynamic_cast<BSQStringOf*>(ptr) != nullptr)
        {
            return BSQStringOf::hash(dynamic_cast<BSQStringOf*>(ptr));
        }
        else if(dynamic_cast<BSQGUID*>(ptr) != nullptr)
        {
            return BSQGUID::hash(dynamic_cast<BSQGUID*>(ptr));
        }
        else if(dynamic_cast<BSQDataHash*>(ptr) != nullptr)
        {
            return BSQDataHash::hash(dynamic_cast<BSQDataHash*>(ptr));
        }
        else if(dynamic_cast<BSQCryptoHash*>(ptr) != nullptr)
        {
            return BSQCryptoHash::hash(dynamic_cast<BSQCryptoHash*>(ptr));
        }
        else if(dynamic_cast<BSQEventTime*>(ptr) != nullptr)
        {
            return BSQEventTime::hash(dynamic_cast<BSQEventTime*>(ptr));
        }
        else if(dynamic_cast<BSQEnum*>(ptr) != nullptr)
        {
            return BSQEnum::hash(dynamic_cast<BSQEnum*>(ptr));
        }
        else if(dynamic_cast<BSQIdKey*>(ptr) != nullptr)
        {
            return BSQIdKey::hash(dynamic_cast<BSQIdKey*>(ptr));
        }
        else if(dynamic_cast<BSQGUIDIdKey*>(ptr) != nullptr)
        {
            return BSQGUIDIdKey::hash(dynamic_cast<BSQGUIDIdKey*>(ptr));
        }
         else if(dynamic_cast<BSQEventTimeIdKey*>(ptr) != nullptr)
        {
            return BSQEventTimeIdKey::hash(dynamic_cast<BSQEventTimeIdKey*>(ptr));
        }
        else if(dynamic_cast<BSQDataHashIdKey*>(ptr) != nullptr)
        {
            return BSQDataHashIdKey::hash(dynamic_cast<BSQDataHashIdKey*>(ptr));
        }
        else
        {
            return BSQCryptoHashIdKey::hash(dynamic_cast<BSQCryptoHashIdKey*>(ptr));
        }
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
    if(BSQ_IS_VALUE_BOOL(v1) && BSQ_IS_VALUE_BOOL(v2))
    {
        return v1 == v2;
    }
    else if(BSQ_IS_VALUE_TAGGED_INT(v1) || BSQ_IS_VALUE_TAGGED_INT(v2))
    {
        if(BSQ_IS_VALUE_TAGGED_INT(v1) && BSQ_IS_VALUE_TAGGED_INT(v2)) {
            return v1 == v2;
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(v1) && dynamic_cast<BSQBigInt*>(BSQ_GET_VALUE_PTR(v2, BSQRef)) != nullptr) {
            return dynamic_cast<BSQBigInt*>(BSQ_GET_VALUE_PTR(v2, BSQRef))->eqI64(BSQ_GET_VALUE_TAGGED_INT(v1));
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(v2) && dynamic_cast<BSQBigInt*>(BSQ_GET_VALUE_PTR(v1, BSQRef)) != nullptr) {
            return dynamic_cast<BSQBigInt*>(BSQ_GET_VALUE_PTR(v1, BSQRef))->eqI64(BSQ_GET_VALUE_TAGGED_INT(v2));
        }
        else {
            return false;
        }
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef); 
        if(dynamic_cast<BSQBigInt*>(ptr1) != nullptr && dynamic_cast<BSQBigInt*>(ptr2) != nullptr)
        {
            return BSQBigInt::eq(dynamic_cast<BSQBigInt*>(ptr1), dynamic_cast<BSQBigInt*>(ptr2));
        }
        else if(dynamic_cast<BSQString*>(ptr1) != nullptr && dynamic_cast<BSQString*>(ptr2) != nullptr)
        {
            return BSQString::keyEqual(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
        }
        else if(dynamic_cast<BSQValidatedString*>(ptr1) != nullptr && dynamic_cast<BSQValidatedString*>(ptr2) != nullptr)
        {
            return BSQValidatedString::keyEqual(dynamic_cast<BSQValidatedString*>(ptr1), dynamic_cast<BSQValidatedString*>(ptr2));
        }
        else if(dynamic_cast<BSQStringOf*>(ptr1) != nullptr && dynamic_cast<BSQStringOf*>(ptr2) != nullptr)
        {
            return BSQStringOf::keyEqual(dynamic_cast<BSQStringOf*>(ptr1), dynamic_cast<BSQStringOf*>(ptr2));
        }
        else if(dynamic_cast<BSQGUID*>(ptr1) != nullptr && dynamic_cast<BSQGUID*>(ptr2) != nullptr)
        {
            return BSQGUID::keyEqual(dynamic_cast<BSQGUID*>(ptr1), dynamic_cast<BSQGUID*>(ptr2));
        }
        else if(dynamic_cast<BSQDataHash*>(ptr1) != nullptr && dynamic_cast<BSQDataHash*>(ptr2) != nullptr)
        {
            return BSQDataHash::keyEqual(dynamic_cast<BSQDataHash*>(ptr1), dynamic_cast<BSQDataHash*>(ptr2));
        }
        else if(dynamic_cast<BSQCryptoHash*>(ptr1) != nullptr && dynamic_cast<BSQCryptoHash*>(ptr2) != nullptr)
        {
            return BSQCryptoHash::keyEqual(dynamic_cast<BSQCryptoHash*>(ptr1), dynamic_cast<BSQCryptoHash*>(ptr2));
        }
        else if(dynamic_cast<BSQEventTime*>(ptr1) != nullptr && dynamic_cast<BSQEventTime*>(ptr2) != nullptr)
        {
            return BSQEventTime::keyEqual(dynamic_cast<BSQEventTime*>(ptr1), dynamic_cast<BSQEventTime*>(ptr2));
        }
        else if(dynamic_cast<BSQEnum*>(ptr1) != nullptr && dynamic_cast<BSQEnum*>(ptr2) != nullptr)
        {
            return BSQEnum::keyEqual(dynamic_cast<BSQEnum*>(ptr1), dynamic_cast<BSQEnum*>(ptr2));
        }
        else if(dynamic_cast<BSQIdKey*>(ptr1) != nullptr && dynamic_cast<BSQIdKey*>(ptr2) != nullptr)
        {
            return BSQIdKey::keyEqual(dynamic_cast<BSQIdKey*>(ptr1), dynamic_cast<BSQIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQGUIDIdKey*>(ptr1) != nullptr && dynamic_cast<BSQGUIDIdKey*>(ptr2) != nullptr)
        {
            return BSQGUIDIdKey::keyEqual(dynamic_cast<BSQGUIDIdKey*>(ptr1), dynamic_cast<BSQGUIDIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQEventTimeIdKey*>(ptr1) != nullptr && dynamic_cast<BSQEventTimeIdKey*>(ptr2) != nullptr)
        {
            return BSQEventTimeIdKey::keyEqual(dynamic_cast<BSQEventTimeIdKey*>(ptr1), dynamic_cast<BSQEventTimeIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQDataHashIdKey*>(ptr1) != nullptr && dynamic_cast<BSQDataHashIdKey*>(ptr2) != nullptr)
        {
            return BSQDataHashIdKey::keyEqual(dynamic_cast<BSQDataHashIdKey*>(ptr1), dynamic_cast<BSQDataHashIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQCryptoHashIdKey*>(ptr1) != nullptr && dynamic_cast<BSQCryptoHashIdKey*>(ptr2) != nullptr)
        {
            return BSQCryptoHashIdKey::keyEqual(dynamic_cast<BSQCryptoHashIdKey*>(ptr1), dynamic_cast<BSQCryptoHashIdKey*>(ptr2));
        }
        else
        {
            return false;  
        }
    }
}

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

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_POD_FLAG;
    }
    else {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef);

        if(dynamic_cast<BSQTuple*>(ptr) != nullptr) {
            return dynamic_cast<BSQTuple*>(ptr)->flag;
        }
        else if(dynamic_cast<BSQRecord*>(ptr) != nullptr) {
            return dynamic_cast<BSQTuple*>(ptr)->flag;
        }
        else {
            return nominalDataKinds[(size_t)getNominalTypeOf_Value(v)];
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
        const BSQRef* vv = BSQ_GET_VALUE_PTR(v, const BSQRef);
        if(dynamic_cast<const BSQBigInt*>(vv) != nullptr)
        {
            return dynamic_cast<const BSQBigInt*>(vv)->display();
        }
        else if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQString{}(*dynamic_cast<const BSQString*>(vv));
        }
        else if(dynamic_cast<const BSQValidatedString*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQValidatedString{}(*dynamic_cast<const BSQValidatedString*>(vv));
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQStringOf{}(*dynamic_cast<const BSQStringOf*>(vv));
        }
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUID{}(*dynamic_cast<const BSQGUID*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQCryptoHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQCryptoHash{}(*dynamic_cast<const BSQCryptoHash*>(vv));
        }
        else if(dynamic_cast<const BSQDataHash*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHash{}(*dynamic_cast<const BSQDataHash*>(vv));
        }
        else if(dynamic_cast<const BSQEventTime*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQEventTime{}(*dynamic_cast<const BSQEventTime*>(vv));
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQEnum{}(*dynamic_cast<const BSQEnum*>(vv));
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQIdKey{}(*dynamic_cast<const BSQIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQGUIDIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQGUIDIdKey{}(*dynamic_cast<const BSQGUIDIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQDataHashIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQDataHashIdKey{}(*dynamic_cast<const BSQDataHashIdKey*>(vv));
        }
        else if(dynamic_cast<const BSQCryptoHashIdKey*>(vv) != nullptr)
        {
            return DisplayFunctor_BSQCryptoHashIdKey{}(*dynamic_cast<const BSQCryptoHashIdKey*>(vv));
        }




        else if(dynamic_cast<const BSQPODBuffer*>(vv) != nullptr)
        {
            auto pbuf = dynamic_cast<const BSQPODBuffer*>(vv);
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

                tvals += Runtime::diagnostic_format(tv->entries.at(i));
            }
            tvals += U"]";

            return tvals;
        }
        else if(dynamic_cast<const BSQRecord*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

            auto rv = dynamic_cast<const BSQRecord*>(vv);
            std::u32string rvals(U"{");
            for(size_t i = 0; i < rv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += conv.from_bytes(Runtime::propertyNames[(int32_t)rv->entries.at(i).first]) + U"=" + Runtime::diagnostic_format(rv->entries.at(i).second);
            }
            rvals += U"}";

            return rvals;
        }
        else
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            
            auto obj = dynamic_cast<const BSQObject*>(vv);
            return conv.from_bytes(nominaltypenames[(uint32_t) obj->ntype]) + obj->display();
        }
    }
}
}