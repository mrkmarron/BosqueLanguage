//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
//%%STATIC_STRING_CREATE%%

//%%STATIC_INT_CREATE%%

const char* Runtime::propertyNames[] = {
    "Invalid",
//%%PROPERTY_NAMES
};

constexpr const char* s_nominaltypenames[] = {
    "[INVALID]",
//%%NOMINAL_TYPE_DISPLAY_NAMES
};

std::string Runtime::diagnostic_format(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return std::string("none");
    }
    else if(BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? "true" : "false";
    }
    else if(BSQ_IS_VALUE_INT(v))
    {
        return std::to_string(BSQ_GET_VALUE_INT(v));
    }
    else
    {
        const BSQRef* vv = BSQ_GET_VALUE_PTR(v, const BSQRef);
        if(dynamic_cast<const BSQString*>(vv) != nullptr)
        {
            auto sstr = dynamic_cast<const BSQString*>(vv);
            return std::string("\"") + std::string(sstr->sdata.cbegin(), sstr->sdata.cend()) + std::string("\"");
        }
        else if(dynamic_cast<const BSQStringOf*>(vv) != nullptr)
        {
            auto sof = dynamic_cast<const BSQStringOf*>(vv);
            return std::string(s_nominaltypenames[(uint32_t)sof->oftype]) + std::string("'") + std::string(sof->sdata.cbegin(), sof->sdata.cend()) + std::string("'");
        }
        else if(dynamic_cast<const BSQPODBuffer*>(vv) != nullptr)
        {
            auto pbuf = dynamic_cast<const BSQPODBuffer*>(vv);
            std::string rvals("PODBuffer{");
            for (size_t i = 0; i < pbuf->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += pbuf->sdata[i];
            }
            rvals += "}";

            return rvals;
        }
        else if(dynamic_cast<const BSQGUID*>(vv) != nullptr)
        {
            auto guid = dynamic_cast<const BSQGUID*>(vv);
            return std::string("GUID@") + std::string(guid->sdata.cbegin(), guid->sdata.cend());
        }
        else if(dynamic_cast<const BSQEnum*>(vv) != nullptr)
        {
            auto ev = dynamic_cast<const BSQEnum*>(vv);
            return std::string(s_nominaltypenames[(uint32_t)ev->oftype]) + std::string("::") + std::string(ev->ename);
        }
        else if(dynamic_cast<const BSQIdKey*>(vv) != nullptr)
        {
            auto idv = dynamic_cast<const BSQIdKey*>(vv);
            return std::string(s_nominaltypenames[(uint32_t)idv->oftype]) + std::string("@") + Runtime::diagnostic_format(idv->sdata);
        }
        else if(dynamic_cast<const BSQTuple*>(vv) != nullptr)
        {
            auto tv = dynamic_cast<const BSQTuple*>(vv);
            std::string tvals("[");
            for(size_t i = 0; i < tv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    tvals += ", ";
                }

                tvals += Runtime::diagnostic_format(tv->entries.at(i));
            }
            tvals += "]";

            return tvals;
        }
        else if(dynamic_cast<const BSQRecord*>(vv) != nullptr)
        {
            auto rv = dynamic_cast<const BSQRecord*>(vv);
            std::string rvals("{");
            for(size_t i = 0; i < rv->entries.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += std::string(Runtime::propertyNames[(int32_t)rv->entries.at(i).first]) + "=" + Runtime::diagnostic_format(rv->entries.at(i).second);
            }
            rvals += "}";

            return rvals;
        }
        else
        {
            auto obj = dynamic_cast<const BSQObject*>(vv);
            if (dynamic_cast<const BSQList*>(obj) != nullptr)
            {
                auto list = dynamic_cast<const BSQList*>(obj);
                std::string ls("{");
                for (size_t i = 0; i < list->entries.size(); ++i)
                {
                    if (i != 0)
                    {
                        ls += ", ";
                    }

                    ls += Runtime::diagnostic_format(list->entries.at(i));
                }
                ls += "}";

                return std::string(s_nominaltypenames[(uint32_t) obj->ntype]) + ls;
            }
            else if (dynamic_cast<const BSQSet*>(obj) != nullptr)
            {
                auto set = dynamic_cast<const BSQSet*>(obj);
                std::string ss("{");
                bool first = true;
                for (auto iter = set->entries.cbegin(); iter != set->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ss += ", ";
                    }
                    first = false;

                    ss += Runtime::diagnostic_format(iter->second);
                }
                ss += "}";

                return std::string(s_nominaltypenames[(uint32_t) obj->ntype]) + ss;
            }
            else if (dynamic_cast<const BSQMap*>(obj) != nullptr)
            {
                auto map = dynamic_cast<const BSQMap*>(vv);
                std::string ms("{");
                bool first = true;
                for (auto iter = map->entries.cbegin(); iter != map->entries.cend(); ++iter)
                {
                    if (!first)
                    {
                        ms += ", ";
                    }
                    first = false;

                    ms += Runtime::diagnostic_format(iter->second);
                }
                ms += "}";

                return std::string(s_nominaltypenames[(uint32_t) obj->ntype]) + ms;
            }
            else
            {
                return std::string(s_nominaltypenames[(uint32_t) obj->ntype]) + obj->display();
            }
        }
    }
}
} // namespace BSQ
