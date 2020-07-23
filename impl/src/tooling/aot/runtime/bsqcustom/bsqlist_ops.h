//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "bsqlist_decl.h"

namespace BSQ
{
template <typename Ty, typename T>
class BSQListOps
{
public:
    
    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename MEntryCons> 
    static MType* list_toindexmap(Ty* l, MEntryCons mec)
    {
        std::vector<MEntryType> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            mentries.emplace_back(mec(i, RCIncF{}(l->entries[i])));
        }

        return BSQ_NEW_NO_RC(MType, ntype, move(mentries));
    }

    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename LambdaVF, typename MEntryCons> 
    static MType* list_transformindexmap(Ty* l, LambdaVF vf, MEntryCons mec)
    {
        std::vector<MEntryType> mentries;
        mentries.reserve(l->entries.size());
        
        for(int64_t i = 0; i < l->entries.size(); ++i)
        {
            mentries.emplace_back(mec(i, vf(l->entries[i])));
        }

        return BSQ_NEW_NO_RC(MType, ntype, move(mentries));
    }

    template <typename MType, typename MEntryType, MIRNominalTypeEnum ntype, typename K, typename K_CMP, typename V, typename LambdaKF, typename LambdaVF, typename MEntryCons> 
    static MType* list_transformmap(Ty* l, LambdaKF kf, LambdaVF vf, MEntryCons mec)
    {
        std::map<K, MEntryType, K_CMP> mentries;
        
        std::transform(l->entries.begin(), l->entries.end(), std::inserter(mentries, mentries.begin()), [kf, vf, mec, &mentries](T v) {
            auto k = kf(v);
            auto vv = vf(v);

            auto epos = mentries.find(k);
            BSQ_ASSERT(epos == mentries.end(), "abort -- duplicate keys are not allowed in List<T>::toMap");

            return std::make_pair(k, mec(k, vv));
        });

        std::vector<MEntryType> rvv;
        std::transform(mentries.begin(), mentries.end(), std::back_inserter(rvv), [](const std::pair<K, MEntryType>& e) { return e.second; });
        return BSQ_NEW_NO_RC(MType, ntype, move(rvv));
    }
};

class BSQListUtilOps
{
public:
    template <typename LType1, typename LType2, typename RType, typename ZType, MIRNominalTypeEnum ntype, typename LambdaZ>
    static RType* list_zip(LType1* l1, LType2* l2, LambdaZ zc)
    {
        std::vector<ZType> entries;
        entries.reserve(l1->entries.size());

        for(size_t i = 0; i < l1->entries.size(); ++i)
        {
            entries.emplace_back(zc(l1->entries[i], l2->entries[i]));
        }

        return BSQ_NEW_NO_RC(RType, ntype, move(entries));
    }

    template <typename RType1, typename UType, MIRNominalTypeEnum ntype1, typename RType2, typename VType, MIRNominalTypeEnum ntype2, typename LType, typename LambdaUZ>
    static std::pair<RType1*, RType2*> list_unzip(LType* l, LambdaUZ uz)
    {
        std::vector<UType> uentries;
        uentries.reserve(l->entries.size());

        std::vector<VType> ventries;
        ventries.reserve(l->entries.size());

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            std::pair<UType, VType> rr = uz(l->entries[i]);

            uentries.emplace_back(rr.first);
            ventries.emplace_back(rr.second);
        }

        auto l1 = BSQ_NEW_NO_RC(RType1, ntype1, move(uentries));
        auto l2 = BSQ_NEW_NO_RC(RType2, ntype2, move(ventries));

        return std::make_pair(l1, l2);
    }

    template <typename RType, MIRNominalTypeEnum ntype>
    static RType* list_range(int64_t start, int64_t end)
    {
        std::vector<int64_t> entries;
        entries.reserve(end - start);

        for(size_t i = 0; i < (end - start); ++i)
        {
            entries.emplace_back(start + i);
        }

        return BSQ_NEW_NO_RC(RType, ntype, move(entries));
    }
};

}