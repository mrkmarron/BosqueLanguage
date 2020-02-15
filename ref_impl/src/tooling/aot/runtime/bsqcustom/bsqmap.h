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
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define T_GET_KEY(X) 0

#define U int
#define INC_RC_U(X)
#define DEC_RC_U(X)

#define K int
#define INC_RC_K(X)
#define DEC_RC_K(X)
#define K_LIST TKName
#define K_CMP(X, Y) false
#define K_EQ(X, Y) false
#define TDisplay(X)
#define UDisplay(X)

#define TMapEntry
#endif

class Ty : public BSQObject {
public:
    std::map<K, std::pair<T, U>, K_CMP> entries;
    K_LIST* keys;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries(), keys(nullptr) { ; }
    Ty(MIRNominalTypeEnum ntype, std::map<K, std::pair<T, U>, K_CMP>&& entries, K_LIST* keys) : BSQObject(ntype), entries(move(entries)), keys(keys) { ; }

    virtual ~Ty()
    {
        ;
    }

    virtual void destroy()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            DEC_RC_K(iter->first);
            DEC_RC_T(iter->second.first);
            DEC_RC_U(iter->second.second);
        }
        BSQRef::decrementChecked(keys);
    }

    template <uint_16 n>
    static Ty* createFromSingle(BSQRefScope& scope, MIRNominalTypeEnum ntype, const std::pair<T, U>(&values)[n])
    {
        std::map<K, std::pair<T, U>, K_CMP> entries;
        K_LIST* keys = nullptr;

        for (int i = 0; i < n; i++)
        {
            auto = values[i];
            auto key = T_GET_KEY(val.key);

            auto iter = entries.find(key);
            if(iter != entries.cend())
            {
                INC_RC_T(val.first);
                INC_RC_U(val.second);

                DEC_RC_T(iter->second.first);
                DEC_RC_U(iter->second.second);

                entries.insert(std::make_pair(iter->first, std::make_pair(val.first, val.second)));
            }
            else
            {
                keys = (K_LIST*)BSQRef::incrementDirect(BSQ_NEW_NO_RC(K_LIST, INC_RC_K(key), keys));

                entries.insert(std::make_pair(INC_RC_K(key), std::make_pair(INC_RC_T(val.first), INC_RC_U(val.second))));
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, Ty, ntype, move(entries), keys);
    }

    Ty* add(K key, T v, U u, K_LIST* nkeys, BSQRefScope& cscope)
    {
        std::map<K, std::pair<T, U>, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            entries.insert(std::make_pair(INC_RC_K(iter->first), std::make_pair(INC_RC_T(iter->second.first), INC_RC_U(iter->second.second))));
        }

        entries.insert(std::make_pair(INC_RC_K(key), std::make_pair(INC_RC_T(v), INC_RC_U(u))));

        BSQRef::incrementDirect(nkeys);
        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), nkeys);
    }

    Ty* update(K key, T v, U u, BSQRefScope& cscope)
    {
        std::map<K, std::pair<T, U>, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(K_EQ(key, iter->first))
            {
                entries.insert(std::make_pair(INC_RC_K(iter->first), std::make_pair(INC_RC_T(v), INC_RC_U(u))));
            }
            else
            {
                entries.insert(std::make_pair(INC_RC_K(iter->first), std::make_pair(INC_RC_T(iter->second.first), INC_RC_U(iter->second.second))));
            }
        }
       
        BSQRef::incrementDirect(this->keys);
        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), this->keys);
    }

    Ty* clearKey(K key, K_LIST* nkeys, BSQRefScope& cscope)
    {
        std::map<K, std::pair<T, U>, K_CMP> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(!K_EQ(key, iter->first)) 
            {
                entries.insert(std::make_pair(INC_RC_K(iter->first), std::make_pair(INC_RC_T(iter->second.first), INC_RC_U(iter->second.second))));
            }
        }
        
        if(nkeys != nullptr)
        {
            BSQRef::incrementDirect(nkeys);
        }

        return BSQ_NEW_ADD_SCOPE(cscope, Ty, this->nominalType, move(entries), nkeys);
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        std::u32string ms(U"{");
        bool first = true;
        for (auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            if (!first)
            {
                ms += U", ";
            }
            first = false;

            ms += TDisplay(iter->second.first) + " => " UDisplay(iter->second.second);
        }
        ms += U"}";

        return ms;
    }
};

#undef Ty
#undef T
#undef INC_RC_T
#undef DEC_RC_T
#undef T_GET_KEY
#undef K
#undef INC_RC_K
#undef DEC_RC_K
#undef K_LIST
#undef K_CMP
#undef K_EQ
#undef TDisplay
