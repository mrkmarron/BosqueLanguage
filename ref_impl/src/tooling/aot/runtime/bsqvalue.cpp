//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
BSQTuple* BSQTuple::_empty = INC_REF_DIRECT(BSQTuple, new BSQTuple({}));
BSQRecord* BSQRecord::_empty = INC_REF_DIRECT(BSQRecord, new BSQRecord({}));

size_t bsqKeyValueHash(KeyValue v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return 0;
    }
    else if(BSQ_IS_VALUE_INT(v))
    {
        return BSQ_GET_VALUE_INT(v);
    }
    else
    {
        auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef); 
        if(dynamic_cast<BSQBoxedInt*>(ptr) != nullptr)
        {
            auto bi = dynamic_cast<BSQBoxedInt*>(ptr);
            return bi->data.isInt() ? bi->data.getInt64() : bi->data.getBigInt()->hash();
        }
        else if(dynamic_cast<BSQString*>(ptr) != nullptr)
        {
            return BSQString::hash(dynamic_cast<BSQString*>(ptr));
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
        else if(dynamic_cast<BSQDataHashIdKey*>(ptr) != nullptr)
        {
            return BSQDataHashIdKey::hash(dynamic_cast<BSQDataHashIdKey*>(ptr));
        }
        else if(dynamic_cast<BSQCryptoHashIdKey*>(ptr) != nullptr)
        {
            return BSQCryptoHashIdKey::hash(dynamic_cast<BSQCryptoHashIdKey*>(ptr));
        }
        else if(dynamic_cast<BSQTuple*>(ptr) != nullptr)
        {
            return BSQTuple::hash(dynamic_cast<BSQTuple*>(ptr));
        }
        else 
        {
            return BSQRecord::hash(dynamic_cast<BSQRecord*>(ptr));
        }
    }
}

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2)
{
    if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
    {
        return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONE(v2);
    }
    else if(BSQ_IS_VALUE_INT(v1) || BSQ_IS_VALUE_INT(v2))
    {
        if(BSQ_IS_VALUE_INT(v1) && BSQ_IS_VALUE_INT(v2))
        {
            return BSQ_GET_VALUE_INT(v1) == BSQ_GET_VALUE_INT(v2);
        }
        else if (BSQ_IS_VALUE_INT(v1) && BSQ_IS_VALUE_PTR(v2) && dynamic_cast<BSQBoxedInt*>(BSQ_GET_VALUE_PTR(v2, BSQRef)) != nullptr)
        {
            return BSQ_GET_VALUE_BSQINT(v1) == BSQ_GET_VALUE_BSQINT(v2);
        }
        else if (BSQ_IS_VALUE_PTR(v1) && dynamic_cast<BSQBoxedInt*>(BSQ_GET_VALUE_PTR(v1, BSQRef)) != nullptr && BSQ_IS_VALUE_INT(v2))
        {
            return BSQ_GET_VALUE_BSQINT(v1) == BSQ_GET_VALUE_BSQINT(v2);
        }
        else
        {
            return false;
        }
    }
    else
    {
        auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
        auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef); 
        if(dynamic_cast<BSQBoxedInt*>(ptr1) != nullptr && dynamic_cast<BSQBoxedInt*>(ptr2) != nullptr)
        {
            return dynamic_cast<BSQBoxedInt*>(ptr1)->data == dynamic_cast<BSQBoxedInt*>(ptr2)->data;
        }
        else if(dynamic_cast<BSQString*>(ptr1) != nullptr && dynamic_cast<BSQString*>(ptr2) != nullptr)
        {
            return BSQString::keyEqual(dynamic_cast<BSQString*>(ptr1), dynamic_cast<BSQString*>(ptr2));
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
        else if(dynamic_cast<BSQDataHashIdKey*>(ptr1) != nullptr && dynamic_cast<BSQDataHashIdKey*>(ptr2) != nullptr)
        {
            return BSQDataHashIdKey::keyEqual(dynamic_cast<BSQDataHashIdKey*>(ptr1), dynamic_cast<BSQDataHashIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQCryptoHashIdKey*>(ptr1) != nullptr && dynamic_cast<BSQCryptoHashIdKey*>(ptr2) != nullptr)
        {
            return BSQCryptoHashIdKey::keyEqual(dynamic_cast<BSQCryptoHashIdKey*>(ptr1), dynamic_cast<BSQCryptoHashIdKey*>(ptr2));
        }
        else if(dynamic_cast<BSQTuple*>(ptr1) != nullptr && dynamic_cast<BSQTuple*>(ptr2) != nullptr)
        {
            return BSQTuple::keyEqual(dynamic_cast<BSQTuple*>(ptr1), dynamic_cast<BSQTuple*>(ptr2));
        }
        else if(dynamic_cast<BSQRecord*>(ptr1) != nullptr && dynamic_cast<BSQRecord*>(ptr2) != nullptr)
        {
            return BSQRecord::keyEqual(dynamic_cast<BSQRecord*>(ptr1), dynamic_cast<BSQRecord*>(ptr2));
        }
        else
        {
            return false;  
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
    else if(BSQ_IS_VALUE_INT(v))
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(std::to_string(BSQ_GET_VALUE_INT(v)));
    }
    else
    {
        const BSQRef* vv = BSQ_GET_VALUE_PTR(v, const BSQRef);
        if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            auto sstr = dynamic_cast<const BSQString*>(vv);
            return std::u32string(U"\"") + std::u32string(sstr->sdata.cbegin(), sstr->sdata.cend()) + std::u32string(U"\"");
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto sof = dynamic_cast<const BSQStringOf*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)sof->oftype]) + std::u32string(U"'") + sof->sdata + std::u32string(U"'");
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
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            auto guid = dynamic_cast<const BSQGUID*>(vv);
            return std::u32string(U"GUID@") + std::u32string(guid->sdata.cbegin(), guid->sdata.cend());
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto ev = dynamic_cast<const BSQEnum*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)ev->oftype]) + std::u32string(U"::") + conv.from_bytes(ev->ename);
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
            auto idv = dynamic_cast<const BSQIdKey*>(vv);

            return conv.from_bytes(s_nominaltypenames[(uint32_t)idv->oftype]) + std::u32string(U"@") + Runtime::diagnostic_format(idv->sdata);
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
            auto obj = dynamic_cast<const BSQObject*>(vv);
            if (dynamic_cast<const BSQList*>(obj) != nullptr)
            {
                
            }
            else if (dynamic_cast<const BSQSet*>(obj) != nullptr)
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
                auto set = dynamic_cast<const BSQSet*>(obj);

                std::u32string ss(U"{");
                bool first = true;
                for (auto iter = set->entries.cbegin(); iter != set->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ss += U", ";
                    }
                    first = false;

                    ss += Runtime::diagnostic_format(iter->second);
                }
                ss += U"}";

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ss;
            }
            else if (dynamic_cast<const BSQMap*>(obj) != nullptr)
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
                auto map = dynamic_cast<const BSQMap*>(vv);

                std::u32string ms(U"{");
                bool first = true;
                for (auto iter = map->entries.cbegin(); iter != map->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ms += U", ";
                    }
                    first = false;

                    ms += Runtime::diagnostic_format(iter->second);
                }
                ms += U"}";

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ms;
            }
            else
            {
                std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

                return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + obj->display();
            }
        }
    }
}
}