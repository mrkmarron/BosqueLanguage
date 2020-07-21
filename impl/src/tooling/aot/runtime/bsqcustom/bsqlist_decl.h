//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../bsqvalue.h"

namespace BSQ
{
template <typename T>
struct BSQList
{
    size_t count;

    template <typename Ty, uint16_t count>
    inline static Ty* singletonInit(MetaData* mdata, std::initializer_list<Value> values)
    {
        T* contents = nullptr;
        Ty* alloc = Allocator::GlobalAllocator.allocateSafePlus<Ty, T, count>(mdata);

        alloc->count = count;
        std::copy(values.begin(), values.end(), contents);

        return alloc;
    }

    inline T* begin()
    {
        return (T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t));
    }

    inline T* end()
    {
        return ((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t))) + this->count;
    }

    inline T& at(size_t i)
    {
        return *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + i);
    }

    inline void copyto(size_t ipos, BSQList* from, size_t fpos)
    {
        *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + ipos) = *((T*)GET_COLLECTION_START_FIXED(from, sizeof(size_t)) + fpos);
    }

    inline void store(size_t ipos, const T& v)
    {
        *((T*)GET_COLLECTION_START_FIXED(this, sizeof(size_t)) + ipos) = v;
    }

    template <typename DisplayF>
    std::wstring display() const
    {
        T* vals = GET_COLLECTION_START_FIXED(this, sizeof(BSQList<T>));
        std::wstring ls(L"{");
        for (size_t i = 0; i < this->count; ++i)
        {
            if (i != 0)
            {
                ls += L", ";
            }
            ls += DisplayF{}(vals[i]);
        }
        ls += L"}";

        return ls;
    }

    template <typename Ty, typename ListT>
    static Ty* list_concat(ListT& l, MetaData* mdata)
    {
        size_t totalct = std::transform_reduce(
            l->begin(), 
            l->end(), 
            0,
            [](const Ty* ll) => { return ll->count; },
            [] (size_t acc, size_t v) => { return acc + v; }
        );

        T* contents = nullptr;
        Ty* res = Allocator::GlobalAllocator.allocateTPlus<Ty, T>(mdata, totalct, &contents);
        res->count = totalct;

        size_t cpos = 0;
        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            Ty* ll = l->at(i);
            std::copy(ll->begin(), ll->end(), contents + cpos);
            
            cpos += ll->count;
        }

        return res;
    }

    template <std::execution ep>
    int64_t list_sum_int()
    {
        int64_t res = std::reduce(ep, this->begin(), this->end(), 0, [](int64_t a, int64_t b) {
            if((a == std::numeric_limits<int64_t>::max()) | (b == std::numeric_limits<int64_t>::max())) 
            {
                return std::numeric_limits<int64_t>::max();
            }
            else 
            {
                int64_t opres = 0;
                if(__builtin_add_overflow(a, b, &opres) || INT_OOF_BOUNDS(opres)) 
                {
                    opres = std::numeric_limits<int64_t>::max();
                }
                return opres;
            }
        });

        BSQ_ASSERT(res != std::numeric_limits<int64_t>::max());
        return res;
    }

    BSQBigInt* list_sum_bigint()
    {
        assert(false);
    }

    BSQBigInt* list_sum_mixed()
    {
        assert(false);
    }
};
}
