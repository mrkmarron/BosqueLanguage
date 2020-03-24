//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqlist_decl.h"

#pragma once

namespace BSQ
{

template <typename T, typename RCIncF, typename RCDecF, typename DisplayF>
class BSQListOps
{
typedef BSQList<T, RCDecF, DisplayF> Ty;

public:
    template <uint16_t n>
    static Ty* createFromSingle(MIRNominalTypeEnum ntype, const T(&values)[n])
    {
        return BSQ_NEW_NO_RC(Ty, ntype, move(std::vector<T>(&values, &values + n)));
    }

    template <typename LambdaP>
    static bool list_all(Ty* l)
    {
        return std::all_of(l->entries.begin(), l->entries.end(), LambdaP{});
    }

    template <typename LambdaP>
    static bool list_none(Ty* l)
    {
        return std::none_of(l->entries.begin(), l->entries.end(), LambdaP{});
    }

    template <typename LambdaP>
    static bool list_any(Ty* l)
    {
        return std::any_of(l->entries.begin(), l->entries.end(), LambdaP{});
    }

    template <typename LambdaP>
    static int64_t list_count(Ty* l)
    {
        return (int64_t)std::count_if(l->entries.begin(), l->entries.end(), LambdaP{});
    }

    template <typename LambdaP>
    static int64_t list_countnot(Ty* l)
    {
        return (int64_t)l->entries.size() - (int64_t)std::count_if(l->entries.begin(), l->entries.end(), LambdaP{});
    }

    template <typename LambdaP>
    static int64_t list_indexof(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto uend = std::find_if(ib, ie, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    static int64_t list_indexofnot(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto uend = std::find_if_not(ib, ie, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    static int64_t list_indexoflast(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto rb = std::reverse_iterator(ib);
        auto re = std::reverse_iterator(ie);

        auto uend = std::find_if(ie, ib, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    static int64_t list_indexoflastnot(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->entries.begin() + s;
        auto ie = l->entries.begin() + e;

        auto rb = std::reverse_iterator(ib);
        auto re = std::reverse_iterator(ie);

        auto uend = std::find_if_not(ie, ib, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaC>
    static T list_min(Ty* l)
    {
        return std::min_element(l->entries.begin() + 1, l->entries.end(), *(l->entries.begin()), LambdaC{});
    }

    template <typename LambdaC>
    static T list_max(Ty* l)
    {
        return std::max_element(l->entries.begin() + 1, l->entries.end(), *(l->entries.begin()), LambdaC{});
    }

    template <typename LambdaR>
    static T list_sum(Ty* l, T zero)
    {
        return std::reduce(l->entries.begin(), l->entries.end(), zero, LambdaR{});
    }

    template <typename LambdaP>
    static Ty* list_filter(Ty* l)
    {
        std::vector<T> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries](T& v) -> void {
            if(LambdaP{}(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_filternot(Ty* l)
    {
        std::vector<T> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries](T& v) -> void {
            if(!LambdaP{}(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_oftype(Ty* l)
    {
        std::vector<U> entries;
        std::for_each(l->entries.begin(), l->entries.end(), [&entries](T& v) -> void {
            if(LambdaTC{}(v))
            {
                entries.push_back(LambdaCC{}(v));
            }
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_cast(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            BSQ_ASSERT(LambdaTC{}(v));

            return LambdaCC{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    static Ty* list_slice(Ty* l, int64_t s, int64_t e)
    {
        std::vector<T> entries;
        entries.reserve(e - s);

        std::transform(l->entries.begin() + s, l->entries.begin() + e, std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    static Ty* list_takewhile(Ty* l)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), LambdaP{});
        return TOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discardwhile(Ty* l)
    {
        auto uend = std::find_if_not(l->entries.begin(), l->entries.end(), LambdaP{});
        return TOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaP>
    static Ty* list_takeuntil(Ty* l)
    {
        auto uend = std::find_if(l->entries.begin(), l->entries.end(), LambdaP{});
        return TOps::list_slice(l, 0, (int64_t)std::distance(l->entries.begin(), uend));
    }

    template <typename LambdaP>
    static Ty* list_discarduntil(Ty* l)
    {
        auto uend = std::find_if(std::execution::par_unseq, l->entries.begin(), l->entries.end(), LambdaP{});
        return TOps::list_slice(l, (int64_t)std::distance(l->entries.begin(), uend), (int64_t)l->entries.size());
    }

    template <typename LambdaCMP, typename LambdaEQ>
    static Ty* list_unique(Ty* l)
    {
        std::vector<T> vv(l->entries.begin(), l->entries.end());
        std::sort(vv.begin(), vv.end(), LambdaCMP{});

        auto uend = std::unique(vv.begin(), vv.end(), LambdaEQ{});
        vv.erase(uend, vv.end());

        std::for_each(vv.begin(), vv.end(), [](T& v) -> T {
            RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    static Ty* list_reverse(Ty* l)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.crbegin(), l->entries.crend(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaF>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_map(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), (T& v) -> U {
            return LambdaF{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>)), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaF>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_mapindex(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        for(int64_t i = 0; i < (int64_t)l->entries.size(); ++i)
        {
            entries.push_back(LambdaF{}(i, v));
        }

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaGet>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_project(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            return LambdaGet{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaGet>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_tryproject(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            return LambdaGet{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaZip>
    static BSQList<U, U_RCDecF, U_DisplayF>* list_zipindex(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        for(int64_t i = 0; i < (int64_t)l->entries.size(); ++i)
        {
            entries.push_back(LambdaZip{}(i, v));
        }

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, typename RT, typename RT_RCDecF, typename RT_DisplayF, MIRNominalTypeEnum ntype, typename LambdaP, typename LambdaZip>
    static BSQList<RT, RT_RCDecF, RT_DisplayF>* list_join(Ty* l, BSQList<U, U_RCDecF, U_DisplayF>* ol)
    {
        std::vector<RT> entries;

        std::for_each(l->entries.begin(), l->entries.end(), [ol](T& v) -> void {
            std::for_each(ol->entries.begin(), ol->entries.end(), [](U& u) -> void {
                if(LambdaP{}(v, u))
                {
                    entries.push_back(LambdaZip{}(v, u));
                }
            });
        });

        return BSQ_NEW_NO_RC((BSQList<RT, RT_RCDecF, RT_DisplayF>)), ntype, move(entries));
    }

    template <typename U, typename U_RCIncF, typename U_RCDecF, typename U_DisplayF, typename RT, typename RT_RCDecF, typename RT_DisplayF, MIRNominalTypeEnum ntype, typename LambdaP, typename LambdaZip>
    static static BSQList<RT, RT_RCDecF, RT_DisplayF>* list_joingroup(Ty* l, BSQList<U, U_RCDecF, U_DisplayF>* ol)
    {
        std::vector<RT> entries;

        std::for_each(l->entries.begin(), l->entries.end(), [ol](T& v) -> void {
            std::vector<U> ue;

            std::for_each(ol->entries.begin(), ol->entries.end(), [](U& u) -> void {
                if(LambdaP{}(v, u))
                {
                    ue.push_back(U_RCIncF{}(u));
                }
            });

            entries.push_back(LambdaZip{}(v, ue));
        });

        return BSQ_NEW_NO_RC((BSQList<RT, RT_RCDecF, RT_DisplayF>)), ntype, move(entries));
    }

    static Ty* list_append(Ty* l, Ty* lp)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size() + lp->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        std::transform(lp->entries.begin(), lp->entries.end(), std::back_inserter(entries), [](T& v) -> T {
            return RCIncF{}(v);
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, MIRNominalTypeEnum ntype, typename LambdaPF> 
    static BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, T, RCDecF, DisplayF>* list_partition(Ty* l)
    {
        std::map<K, std::vector<T>, K_CMP> partitions;
        std::for_each(l->entries.begin(), l->entries.end(), [&partitions](T& v) -> void {
            auto k = LambdaPF{}(v);
            auto pp = partitions.find(k);

            if(pp != partitions.end())
            {
                pp->second.push_back(RCIncF(v));
            }
            else 
            {
                partitions.emplace(k, std::vector<T>{RCIncF(v)});
            }
        });

        std::vector<std::pair<K, Ty*>> mentries;
        mentries.reserve(partitions.size());

        auto ltype = l->nominalType;
        std::transform(partitions.begin(), partitions.end(), std::back_inserter(mentries), [ltype](std::pair<K, std::vector<T>>& me) -> std::pair<K, Ty*> {
            auto le = BSQ_NEW_NO_RC(Ty, ltype, move(me.second));
            return std::make_pair(me.first, INC_REF_DIRECT(Ty, le));
        });

        return BSQ_NEW_NO_RC((BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, T, RCDecF, DisplayF>), ntype, move(mentries));
    }

    template <typename LambdaCMP>
    static Ty* list_sort(Ty* l)
    {
        std::vector<T> entries;
        entries.reserve(l->entries.size());

        std::for_each(l->begin(), l->end(), [&entries](T& v) -> void {
            entries.push_back(RCIncF{}(v));
        });
        std::stable_sort(entries.begin(), entries.end(), LambdaCMP{});

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF, typename LambdaKF, typename V, typename LambdaVF> 
    static BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, V, V_RCDecF, V_DisplayF>* list_tomap(Ty* l, bool merge)
    {
        std::vector<std::pair<K, V>> mentries;
        mentries.reserve(l->entries.size());
        std::for_each(l->entries.begin(), l->entries.end(), [&partitions](T& v) -> void {
            auto k = LambdaKF{}(v);
            auto v = LambdaVF{}(v);
            mentries.push_back(std::make_pair(k, v));
        });

        std::stable_sort(mentries.begin(), mentries.end(), [](const K& a, const K& b) -> bool {
            return K_CMP{}(a, b);
        });

        auto dup = std::adjacent_find(mentries.begin(), mentries.end(), [](const K& a, const K& b) -> bool {
            return K_EQ{}(a, b);
        });

        bool hasdups = dup != mentries.end();
        BSQ_ASSERT(merge || !hasdups);

        if(hasdups)
        {
            while(dup != mentries.end())
            {
                auto dupend = std::find_if(dup, mentries.end(), [dup](const K& a) -> bool {
                    return !K_EQ{}(a, dup);
                });

                std::reverse(dup, dupend);
                std::for_each(std::advance(dup, 1), dupend, [](const std::pair<K, V>& rcc) -> void {
                    K_RCDecF{}(rcc.first);
                    V_RCDecF{}(rcc.second);
                });

                dup = std::adjacent_find(dupend, mentries.end(), [](const K& a, const K& b) -> bool {
                    return K_EQ{}(a, b);
                });
            }

            auto uend = std::unique(mentries.begin(), mentries.end(), [](const K& a, const K& b) -> bool {
                return K_EQ{}(a, b);
            });

            mentries.erase(uend, mentries.end());
        }

        return BSQ_NEW_NO_RC((BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, T, RCDecF, DisplayF>), ntype, move(mentries));
    }

    template <typename V, typename V_RCIncF, typename V_RCDecF, typename V_DisplayF, typename LambdaKF, typename V, typename LambdaVF> 
    static BSQMap<int64_t, RCDecFunctor_Nop, DisplayFunctor_Int, std::less<int64_t>, std::equal_to<int64_t>, V, V_RCDecF, V_DisplayF>* list_toindexmap(Ty* l)
    {
        std::vector<std::pair<int64_t, V>> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            auto v = LambdaVF{}(l->entries[i]);
            mentries.push_back(std::make_pair(i, v));
        }

        return BSQ_NEW_NO_RC((BSQMap<K, RCDecFunctor_Nop, K_DisplayF, std::less<int64_t>, std::equal_to<int64_t>, T, RCDecF, DisplayF>), ntype, move(mentries));
    }
};

}