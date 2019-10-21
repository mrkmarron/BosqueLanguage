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
            return std::string(sof->getTypeOfName()) + sof->bstr->sdata;
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
