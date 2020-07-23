//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../bsqvalue.h"
#include "bsqlist_decl.h"
#include "bsqset_decl.h"

namespace BSQ
{
template <typename K, typename V, typename K_CMP, typename K_EQ, typename EntryT, typename OP_Key, typename OP_Val>
struct BSQMap : public BSQObject 
{
    struct MEntryCMP 
    {
        inline bool operator()(const EntryT& e1, const EntryT& e2)
        {
            return K_CMP{}(OP_Key{}(e1), OP_Key{}(e2));
        } 
    };

    struct MEntryEQ 
    {
        inline bool operator()(const EntryT& e1, const EntryT& e2)
        {
            return K_EQ{}(OP_Key{}(e1), OP_Key{}(e2));
        } 
    };

    size_t count;
    
    inline bool hasKey(const K& k)
    {
        EntryT* entries = GET_COLLECTION_START_FIXED(this, sizeof(BSQMap));
        auto ipos = std::lower_bound(entries, entries + this->count, k, [](const EntryT& a, const EntryT& b){ return MEntryCMP{}(a, b); });

        return ipos != entries + this->count && K_EQ{}(k, OP_Key{}(*ipos));
    }

    inline V& getValue(const K& k)
    {
        EntryT* entries = GET_COLLECTION_START_FIXED(this, sizeof(BSQMap));
        auto ipos = std::lower_bound(entries, entries + this->count, k, [](const T& a, const T& b){ return MEntryCMP{}(a, b); });

        return OP_Val{}(*ipos);
    }

    inline bool tryGetValue(const K& k, V& res)
    {
        EntryT* entries = GET_COLLECTION_START_FIXED(this, sizeof(BSQMap));
        auto ipos = std::lower_bound(entries, entries + this->count, k, [](const T& a, const T& b){ return MEntryCMP{}(a, b); });

        bool found = ipos != entries + this->count && K_EQ{}(k, OP_Key{}(*ipos));

        if(found)
        {
            res = OP_Val{}(*ipos);
        }

        return found;
    }

    template <typename Ty, uint16_t count>
    inline static Ty* singletonInit(MetaData* mdata, std::initializer_list<EntryT> values)
    {
        EntryT* contents = nullptr;
        Ty* alloc = Allocator::GlobalAllocator.allocateSafePlus<Ty, EntryT, count>(mdata);

        std::copy(values.begin(), values.end(), contents);
        std::stable_sort(contents, contents + count, MEntryCMP{});

        auto dup = std::adjacent_find(contents, contents + count, MEntryEQ{});
        BSQ_ASSERT(dup == contents + count, "abort -- duplicate key found in Map initialization");

        return alloc;
    }

    template <typename E_DisplayF>
    std::wstring display() const
    {
        std::wstring ms(L"{");
        xxxx;
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ms += L", ";
            }
            first = false;

            ms += E_DisplayF{}(*iter);
        }
        ms += L"}";

        return ms;
    }
};

}
