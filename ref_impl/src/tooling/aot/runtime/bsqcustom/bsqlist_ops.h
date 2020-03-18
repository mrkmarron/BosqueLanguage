//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating the various MapEntry types
//

#ifndef Ty
#define Ty TName
#define T int
#define TOps TName_Ops
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define BSCOPE
#endif

class TOps
{
public:
    template <uint16_t n>
    static Ty* createFromSingle(MIRNominalTypeEnum ntype, const T(&values)[n])
    {
        std::vector<T> entries;
        entries.reserve(n);

        std::transform(&values, &values + n, std::back_inserter(entries), [](T& v) -> T {
            return INC_RC_T(values[i]));
        });

        return BSQ_NEW_NO_RC(Ty, ntype, n, move(entries));
    }

    template <typename LambdaP>
    static bool list_all(Ty* l, LambdaP p)
    {
        return std::all_of(l->cbegin(), l->cend(), p);
    }

    template <typename LambdaP>
    static int64_t list_count(Ty* l, LambdaP p)
    {
        return (int64_t)std::count_if(l->cbegin(), l->cend(), p);
    }

    template <typename LambdaP>
    inline static int64_t list_indexof(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        auto ib = l->cbegin() + s;
        auto ie = l->cbegin() + e;

        auto uend = std::find_if(ib, ie, p);
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    inline static int64_t list_indexoflast(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        auto ib = l->rend() + s;
        auto ie = l->rend() + e;

xxxx;
        auto uend = std::index_of(ie, ib, p);
        return (int64_t)std::distance(uend, ib);
    }

    template <typename LambdaR>
    static int64_t list_reduce(Ty* l, int64_t iv, LambdaR r)
    {
        return (int64_t)std::reduce(l->cbegin(), l->cend(), r);
    }

    template <typename LambdaP>
    inline static Ty* list_filter(Ty* l, LambdaP p)
    {
        int64_t capacity = min(4, l->size);
        int64_t size = 0;
        T* entries = (T*)malloc(sizeof(T) * (capacity));

        for (int64_t i = 0; i < l->size; i++)
        {
            if(p(l->entries[i]))
            {
                if(size == capacity)
                {
                    capacity = min(capacity * 2, l->size);
                    entries = (T*)realloc(entries, sizeof(T) * capacity);
                }
                entries[size] = INC_RC_T(l->entries[i]));
                size++;
            }
        }

        return BSQ_NEW_NO_RC(Ty, l->nominalType, size, entries);
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    inline static ListU* list_oftype(Ty* l, LambdaTC tcheck, LambdaCC coerce)
    {
        int64_t capacity = min(4, l->size);
        int64_t size = 0;
        U* entries = (U*)malloc(sizeof(U) * (capacity));

        BSQRefScope BSCOPE;
        for (int64_t i = 0; i < l->size; i++)
        {
            if(tcheck(l->entries[i]))
            {
                if(size == capacity)
                {
                    capacity = min(capacity * 2, l->size);
                    entries = (U*)realloc(entries, sizeof(U) * capacity);
                }

                entries[size] = INC_RC_T(coerce(l->entries[i]));
                size++;
            }
        }

        return BSQ_NEW_NO_RC(LISTU, ntype, size, entries);
    }

    template <typename ListU, typename U, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    inline static ListU* list_cast(Ty* l, LambdaTC tcheck, LambdaCC coerce)
    {
        U* entries = (U*)malloc(sizeof(U) * l->size);

        BSQRefScope BSCOPE;
        for (int64_t i = 0; i < l->size; i++)
        {
            BSQ_ASSERT(tcheck(l->entries[i]));

            entries[i] = INC_RC_T(coerce(l->entries[i]));
        }

        return BSQ_NEW_NO_RC(LISTU, ntype, l->size, entries);
    }

    inline static Ty* list_slice(Ty* l, int64_t s, int64_t e)
    {
        T* entries = (T*)malloc(sizeof(T) * (e - s));

        for (int64_t i = 0; i < (e - s); i++)
        {
            entries[i] = INC_RC_T(l->entries[s + i]);
        }

        return BSQ_NEW_NO_RC(Ty, l->nominalType, l->size, entries);
    }

    template <typename LambdaP>
    static Ty* list_takewhile(Ty* l, LambdaP p)
    {
        int64_t pos = 0;
        for(int64_t i = s; i < e; ++i)
        {
            if(!p(l->entries[i]))
            {
                pos = i;
                break;
            }
        }

        return TOps::list_slice(l, 0, pos);
    }

    template <typename LambdaP>
    static Ty* list_discardwhile(Ty* l, LambdaP p)
    {
        int64_t pos = 0;
        for(int64_t i = s; i < e; ++i)
        {
            if(!p(l->entries[i]))
            {
                pos = i;
                break;
            }
        }

        return TOps::list_slice(l, pos, l->size);
    }

    template <typename LambdaP>
    static Ty* list_takeuntil(Ty* l, LambdaP p)
    {
        int64_t pos = 0;
        for(int64_t i = s; i < e; ++i)
        {
            if(p(l->entries[i]))
            {
                pos = i;
                break;
            }
        }

        return TOps::list_slice(l, 0, pos);
    }

    template <typename LambdaP>
    static Ty* list_discarduntil(Ty* l, LambdaP p)
    {
        int64_t pos = 0;
        for(int64_t i = s; i < e; ++i)
        {
            if(p(l->entries[i]))
            {
                pos = i;
                break;
            }
        }

        return TOps::list_slice(l, pos, l->size);
    }

    template <typename LambdaCMP, typename LambdaEQ>
    static Ty* list_unique(Ty* l, LambdaCMP cmp, LambdaEQ eq)
    {
        std::vector<T> vv(l->entries, l->entries + l->size);
        std::sort(vv.begin(), vv.end(), cmp);

        auto uend = std::unique(vv.begin(), vv.end(), eq);
        auto dist = std::distance(vv.begin(), uend);

        T* entries = (T*)malloc(sizeof(T) * dist);
        std::copy(vv.begin(), uend, entries);

        return BSQ_NEW_NO_RC(Ty, l->nominalType, dist, entries);
    }

    static Ty* list_reverse(Ty* l)
    {
        T* entries = (T*)malloc(sizeof(T) * l->size);

        for (int64_t i = l->size - 1; i >= 0; --i)
        {
            entries[i - (l->size - 1)] = INC_RC_T(l->entries[i]);
        }

        return BSQ_NEW_NO_RC(Ty, l->nominalType, l->size, entries);
    }
};

#undef Ty
#undef T
#undef TOps
#undef INC_RC_T
#undef DEC_RC_T
#undef BSCOPE
