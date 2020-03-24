//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmap_decl.h"

#pragma once

namespace BSQ
{

template <typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF>
class BSQMapOps
{
public:
    typedef BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, V, V_RCDecF, V_DisplayF> Ty;

    template <typename K_RCIncF, MIRNominalTypeEnum ntype>
    static BSQList<K, K_RCDecF, K_DisplayF>* map_key_list(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC((BSQList<K, K_RCDecF, K_DisplayF>), ntype, move(entries));
    }

    template <typename K_RCIncF, MIRNominalTypeEnum ntype>
    static BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* map_key_set(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC((BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>), ntype, move(entries));
    }

    template <typename V_RCIncF, MIRNominalTypeEnum ntype>
    static BSQList<V, V_RCDecF, V_DisplayF>* map_values(Ty* m)
    {
        std::vector<V> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> v {
            return V_RCIncF{}(v.value);
        });

        return BSQ_NEW_NO_RC((BSQList<V, V_RCDecF, V_DisplayF>), ntype, move(entries));
    }

    template <typename ListT, typename MapEntryT, MIRNominalTypeEnum ntype, typename LambdaMEC>
    static ListT* map_entries(Ty* m)
    {
        std::vector<MapEntryT> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> MapEntryT {
            return LambdaMEC{}(v.key, v.value);
        });

        return BSQ_NEW_NO_RC((BSQList<K, K_RCDecF, K_DisplayF>), ntype, move(entries));
    }

    static bool map_has_all(Ty* m, BSQList<K, K_RCDecF, K_DisplayF>* kl)
    {
        return std::all_of(kl->entries.begin(), kl->entries.end(), [m](K& k) -> bool {
            MEntry<K, V> e{k};
            return std::binary_search(m->entries.begin(), m->entries.end(), e, MEntryCMP<K, V, K_CMP>{});
        });
    }

    static bool map_domainincludes(Ty* m, BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* s)
    {
        return std::all_of(s->entries.begin(), s->entries.end(), [m](K& k) -> bool {
            MEntry<K, V> e{k};
            return std::binary_search(m->entries.begin(), m->entries.end(), e, MEntryCMP<K, V, K_CMP>{});
        });
    }

    template <typename K_RCIncF, typename V_RCIncF, typename LambdaP>
    static Ty* map_submap(Ty* m)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            if(LambdaP{}(v.key, v.value))
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value))};
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename T, typename T_RCDecF, typename T_DisplayF, typename T_CMP, typename T_EQ, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>* map_oftype(Ty* m)
    {
        std::vector<MEntry<T, U>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            if(LambdaTC{}(v.key, v.value))
            {
                entries.push_back(LambdaCC{}(v.key, v.value));
            }
        });

        return BSQ_NEW_NO_RC((BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename T, typename T_RCDecF, typename T_DisplayF, typename T_CMP, typename T_EQ, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaTC, typename LambdaCC>
    static BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>* map_cast<T where KeyType, U>(m: Map<K, V>)
    {
        std::vector<MEntry<T, U>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            BSQ_ASSERT(LambdaTC{}(v.key, v.value));

            entries.push_back(LambdaCC{}(v.key, v.value));
        });

        return BSQ_NEW_NO_RC((BSQMap<T, T_RCDecF, T_DisplayF, T_CMP, T_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    static Ty* map_project(Ty* m, BSQSet<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ>* ds)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [&entries](MEntry<K, V>& v) -> void {
            bool has = std::binary_search(ds->entries.begin(), ds->entries.end(), v.key, K_CMP{});
            if(has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename U, typename U_RCDecF, typename U_DisplayF, typename LambdaF>
    static BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, U, U_RCDecF, U_DisplayF>* map_remap(Ty* m)
    {

    }

    static Ty* map_projectall(Ty* m, BSQList<K, K_RCDecF, K_DisplayF>* dl)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(dl->entries.begin(), dl->entries.end(), [&entries](K& k) -> void {
            MEntry<K, V> e{k};

            xxxx;
            bool has = std::binary_search(ds->entries.begin(), ds->entries.end(), v.key, K_CMP{});
            if(has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

};

}
