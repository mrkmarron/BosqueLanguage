//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
//%%STATIC_STRING_CREATE%%

const char* Runtime::propertyNames[] = {
    "Invalid",
//%%PROPERTY_NAMES%%
};

inline uint64_t hashHelper(uint64_t hash, uint64_t addtl)
{
    return (hash * addtl) % 452930477; //a mediocre hash with a largish prime
}

inline uint64_t hashStringHelper(const std::string& str, uint64_t hvbase)
{
    uint64_t hv = hvbase;
    for (size_t i = 0; i < str.size(); ++i)
    {
        hv = hashHelper(hv, str[i]);
    }
    return hv;
}

uint64_t Runtime::keyvalue_hashcode(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return 0;
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return BSQ_GET_VALUE_BOOL(v) ? 3 : 1;
    }
    else if (BSQ_IS_VALUE_INT(v))
    {
        return (uint64_t)BSQ_GET_VALUE_INT(v);
    }    
    else
    { 
        const RefCountBase* val = BSQ_GET_VALUE_PTR(v, const RefCountBase);
        if (dynamic_cast<const NSCore$cc$String*>(val) != nullptr)
        {
            return hashStringHelper(dynamic_cast<const NSCore$cc$String*>(val)->sdata, 23);
        }
        else if (dynamic_cast<const NSCore$cc$Tuple*>(val) != nullptr)
        {
            auto ttup = dynamic_cast<const NSCore$cc$Tuple*>(val);
            uint64_t hv = 33;
            for(size_t i = 0; i < ttup->m_entries.size(); ++i)
            {
                hv = hashHelper(hv, Runtime::hashcode(ttup->m_entries[i]));
            }
            return hv;
        }
        else if (dynamic_cast<const NSCore$cc$Record*>(val) != nullptr)
        {
            auto ttup = dynamic_cast<const NSCore$cc$Record*>(val);
            uint64_t hv = 53;
            for(size_t i = 0; i < ttup->m_entries.size(); ++i)
            {
                hv = hashHelper(hv, hashHelper(Runtime::hashcode(ttup->m_entries[i].second), (uint64_t)ttup->m_entries[i].first));
            }
            return hv;
        }
        else
        {
           BSQ_ASSERT(false, "NOT IMPLEMENTED -- hashcode");
           return 0;
        }
    }
}

bool Runtime::keyvalue_equality(Value lhs, Value rhs)
{
    if (lhs == rhs)
    {
        return true;
    }

    if (Runtime::hashcode(lhs) != Runtime::hashcode(rhs))
    {
        return false;
    }

    const RefCountBase* v1 = BSQ_GET_VALUE_PTR(lhs, const RefCountBase);
    const RefCountBase* v2 = BSQ_GET_VALUE_PTR(rhs, const RefCountBase);
    if (dynamic_cast<const NSCore$cc$String*>(v1) != nullptr && dynamic_cast<const NSCore$cc$String*>(v2) != nullptr)
    {
        return dynamic_cast<const NSCore$cc$String*>(v1)->sdata == dynamic_cast<const NSCore$cc$String*>(v2)->sdata;
    }
    else
    {
        if (dynamic_cast<const NSCore$cc$Tuple*>(v1) != nullptr && dynamic_cast<const NSCore$cc$Tuple*>(v2) != nullptr)
        {
            auto tv1 = dynamic_cast<const NSCore$cc$Tuple*>(v1);
            auto tv2 = dynamic_cast<const NSCore$cc$Tuple*>(v2);
            if (tv1->m_entries.size() != tv2->m_entries.size())
            {
                return false;
            }

            return std::equal(tv1->m_entries.cbegin(), tv1->m_entries.cend(), tv2->m_entries.cbegin(), tv2->m_entries.cend(), [&](const Value& a, const Value& b) {
                return Runtime::equality_op(a, b);
            });
        }
        else if (dynamic_cast<const NSCore$cc$Record*>(v1) != nullptr && dynamic_cast<const NSCore$cc$Record*>(v2) != nullptr)
        {
            auto rv1 = dynamic_cast<const NSCore$cc$Record*>(v1);
            auto rv2 = dynamic_cast<const NSCore$cc$Record*>(v2);
            if (rv1->m_entries.size()!= rv2->m_entries.size())
            {
                return false;
            }

            return std::equal(rv1->m_entries.cbegin(), rv1->m_entries.cend(), rv2->m_entries.cbegin(), rv2->m_entries.cend(), [&](const std::pair<MIRPropertyEnum, Value>& a, std::pair<MIRPropertyEnum, const Value>& b) {
                return a.first == b.first && Runtime::equality_op(a.second, b.second);
            });
        }
        else
        {
            return false;
        }
    }
}

uint64_t Runtime::hashcode(Value v)
{
    if(BSQ_IS_VALUE_NONE(v))
    {
        return 0;
    }
    if(BSQ_IS_VALUE_PTR(v) && dynamic_cast<NSCore$cc$StringOf>(BSQ_GET_VALUE_PTR(v, RefCountBase)) != nullptr)
}

bool Runtime::equality_op(Value lhs, Value rhs)
{
    BSQ_ASSERT(false, "NOT IMPLEMENTED");
    return false;
}

bool Runtime::compare_op(Value lhs, Value rhs) 
{
    BSQ_ASSERT(false, "NOT IMPLEMENTED");
    return false;
}

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
        const RefCountBase* vv = BSQ_GET_VALUE_PTR(v, const RefCountBase);
        if(dynamic_cast<const NSCore$cc$String*>(vv) != nullptr)
        {
            return dynamic_cast<const NSCore$cc$String*>(vv)->sdata;
        }
        else if(dynamic_cast<const NSCore$cc$StringOf*>(vv) != nullptr)
        {
            auto sof = dynamic_cast<const NSCore$cc$StringOf*>(vv);
            return std::string(sof->getTypeOfName()) + sof->getString()->sdata;
        }
        else if(dynamic_cast<const NSCore$cc$Tuple*>(vv) != nullptr)
        {
            auto tv = dynamic_cast<const NSCore$cc$Tuple*>(vv);
            std::string tvals("[");
            for(size_t i = 0; i < tv->m_entries.size(); ++i)
            {
                if(i != 0)
                {
                    tvals += ", ";
                }

                tvals += Runtime::diagnostic_format(tv->m_entries.at(i));
            }
            tvals += "]";

            return tvals;
        }
        else if(dynamic_cast<const NSCore$cc$Record*>(vv) != nullptr)
        {
            auto rv = dynamic_cast<const NSCore$cc$Record*>(vv);
            std::string rvals("{");
            for(size_t i = 0; i < rv->m_entries.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += std::string(Runtime::propertyNames[(int32_t)rv->m_entries.at(i).first]) + " " + Runtime::diagnostic_format(rv->m_entries.at(i).second);
            }
            rvals += "}";

            return rvals;
        }
        else
        {
            BSQ_ASSERT(false, "NOT IMPLEMENTED");
            return std::string("");
        }
        
    }
}
} // namespace BSQ
