//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqlist_decl.h"

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
        return std::all_of(l->begin(), l->end(), LambdaP{});
    }

    template <typename LambdaP>
    static bool list_none(Ty* l)
    {
        return std::none_of(l->begin(), l->end(), LambdaP{});
    }

    template <typename LambdaP>
    static bool list_any(Ty* l)
    {
        return std::any_of(l->begin(), l->end(), LambdaP{});
    }

    template <typename LambdaP>
    static int64_t list_count(Ty* l)
    {
        return (int64_t)std::count_if(l->begin(), l->end(), LambdaP{});
    }

    template <typename LambdaP>
    static int64_t list_countnot(Ty* l)
    {
        return (int64_t)l->entries.size() - (int64_t)std::count_if(l->begin(), l->end(), LambdaP{});
    }

    template <typename LambdaP>
    inline static int64_t list_indexof(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->begin() + s;
        auto ie = l->begin() + e;

        auto uend = std::find_if(ib, ie, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    inline static int64_t list_indexofnot(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->begin() + s;
        auto ie = l->begin() + e;

        auto uend = std::find_if_not(ib, ie, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    inline static int64_t list_indexoflast(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->begin() + s;
        auto ie = l->begin() + e;

        auto rb = std::reverse_iterator(ib);
        auto re = std::reverse_iterator(ie);

        auto uend = std::find_if(ie, ib, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaP>
    inline static int64_t list_indexoflastnot(Ty* l, int64_t s, int64_t e)
    {
        auto ib = l->begin() + s;
        auto ie = l->begin() + e;

        auto rb = std::reverse_iterator(ib);
        auto re = std::reverse_iterator(ie);

        auto uend = std::find_if_not(ie, ib, LambdaP{});
        return (int64_t)std::distance(ib, uend);
    }

    template <typename LambdaC=LessFunctor_IntValue>
    static T list_min(Ty* l)
    {
        return std::min_element(l->begin() + 1, l->end(), *(l->begin()), LambdaC{});
    }

    template <typename LambdaC=LessFunctor_IntValue>
    static T list_max(Ty* l)
    {
        return std::max_element(l->begin() + 1, l->end(), *(l->begin()), LambdaC{});
    }

    struct AddFunctor_IntValue
    {
        BSQRefScope* scope;

        IntValue operator()(IntValue a, IntValue b)
        {
            return op_intAdd(*scope, a, b);
        }
    };

    template <typename LambdaR=AddFunctor_IntValue>
    static T list_sum(Ty* l)
    {
        BSQRefScope rr;
        LambdaR addf = {&rr};

        RCIncF{}(std::reduce(l->begin(), l->end(), BSQ_VALUE_0, addf));
    }

    template <typename LambdaP>
    inline static Ty* list_filter(Ty* l)
    {
        std::vector<T> entries;
        std::for_each(l->begin(), l->end(), [&entries](T& v) -> void {
            if(LambdaP{}(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename LambdaP>
    inline static Ty* list_filternot(Ty* l)
    {
        std::vector<T> entries;
        std::for_each(l->begin(), l->end(), [&entries](T& v) -> void {
            if(!LambdaP{}(v))
            {
                entries.push_back(RCIncF{}(v));
            }
        });

        return BSQ_NEW_NO_RC(Ty, l->nominalType, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    inline static BSQList<U, U_RCDecF, U_DisplayF>* list_oftype(Ty* l)
    {
        std::vector<U> entries;
        std::for_each(l->begin(), l->end(), [&entries](T& v) -> void {
            if(LambdaTC{}(v))
            {
                entries.push_back(LambdaCC{}(v));
            }
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    inline static BSQList<U, U_RCDecF, U_DisplayF>* list_cast(Ty* l)
    {
        std::vector<U> entries;
        entries.reserve(l->entries.size());

        std::transform(l->entries.begin(), l->entries.end(), std::back_inserter(entries), [](T& v) -> U {
            BSQ_ASSERT(LambdaTC{}(v));

            return LambdaCC{}(v);
        });

        return BSQ_NEW_NO_RC((BSQList<U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    inline static Ty* list_slice(Ty* l, int64_t s, int64_t e)
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
            entries.push_back(LambdaF{}(BSQ_ENCODE_VALUE_TAGGED_INT(i), v));
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
            entries.push_back(LambdaZip{}(BSQ_ENCODE_VALUE_TAGGED_INT(i), v));
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
};

}