//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

namespace BSQ
{
template<typename T, typename FIncOp, typename FDecOp>
class BSQList : public BSQObject {
public:
    std::vector<T> entries;

    BSQList(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQList(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    virtual ~BSQList() = default;

    virtual void destroy()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            FDecOp(this->entries[i]);
        }
    }

    BSQList* unsafeAdd(const T& v) const
    {
        std::vector<T> nv(this->entries.size(), nullptr);
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            FIncOp(this->entries[i]);
            nv[i] = this->entries[i];
        }
        FIncOp(v);
        nv.push_back(v);

        return new BSQList(this->ntype, move(nv));
    }

    BSQList* unsafeSet(const BSQInt& idx, const T& v) const
    {
        std::vector<T> nv(this->entries.size(), nullptr);
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            if(i == idx)
            {
                FIncOp(v);
                nv[i] = v;
            }
            else
            {
                FIncOp(this->entries[i]);
                nv[i] = this->entries[i];
            }
        }

        return new BSQList(this->ntype, move(nv));
    }

    BSQList* destructiveAdd(const T& v)
    {
        FIncOp(v);
        this->entries.push_back(v);

        return this;
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

        std::u32string ls(U"{");
        for (size_t i = 0; i < list->entries.size(); ++i)
        {
            if (i != 0)
            {
                ls += U", ";
            }

            ls += FDisplay(list->entries.at(i));
        }
        ls += U"}";

        return conv.from_bytes(s_nominaltypenames[(uint32_t) obj->ntype]) + ls;
    }
};
}
