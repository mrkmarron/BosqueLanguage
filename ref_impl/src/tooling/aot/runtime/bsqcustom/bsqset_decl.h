//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "../bsqvalue.h"
#include "bsqlist_decl.h"

#pragma once

namespace BSQ
{

template <typename T, typename RCDecF, typename DisplayF, typename T_CMP, typename T_EQ>
class BSQSet : public BSQObject 
{
public:
    std::vector<T> entries;
    
    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    Ty(MIRNominalTypeEnum ntype, std::vector<T>&& entries) : BSQObject(ntype), entries(entries) { ; }

    virtual ~Ty()
    {
        ;
    }

    virtual void destroy()
    {
        std::for_each(this->entries.begin(), this->entries.end(), [](T& v) -> void {
            RCDecF{}(v);
        });
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        std::u32string ss(U"{");
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ss += U", ";
            }
            first = false;

            ss += FDisplay{}(entries->second);
        }
        ss += U"}";

        return ss;
    }
};

}
