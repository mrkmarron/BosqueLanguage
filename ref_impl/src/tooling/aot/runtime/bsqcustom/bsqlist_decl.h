//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "../bsqvalue.h"

namespace BSQ
{

template <typename T, typename RCDecF, typename DisplayF>
class BSQList : public BSQObject {
public:
    std::vector<T> entries;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    Ty(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

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

        std::u32string ls(U"{");
        for (size_t i = 0; i < this->entries.size(); ++i)
        {
            if (i != 0)
            {
                ls += U", ";
            }
            ls += DisplayF{}(this->entries[i]);
        }
        ls += U"}";

        return ls;
    }
};

}