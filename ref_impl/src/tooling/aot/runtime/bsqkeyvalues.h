//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

namespace BSQ
{
class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(), sdata(str) { ; }
    BSQString(const char* str, int64_t excount) : BSQRef(excount), sdata(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>().from_bytes(str)) { ; }

    virtual ~BSQString() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQString* str)
    {
        return std::hash<std::u32string>{}(str->sdata);
    }
    
    static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        return l->sdata == r->sdata;
    }
};

class BSQStringOf : public BSQRef
{
public:
    const std::u32string sdata;
    const MIRNominalTypeEnum oftype;
  
    BSQStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }

    virtual ~BSQStringOf() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQStringOf* str)
    {
        return HASH_COMBINE((size_t)str->oftype, std::hash<std::u32string>{}(str->sdata));
    }

    static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        return l->oftype == r->oftype && l->sdata == r->sdata;
    }
};

class BSQGUID : public BSQRef
{
public:
    const uint8_t sdata[16];

    BSQGUID(const uint8_t sdata[16]) : BSQRef(), sdata() { memcpy_s((void*)this->sdata, 16, sdata, 16); }

    virtual ~BSQGUID() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQGUID* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    static bool keyEqual(const BSQGUID* l, const BSQGUID* r)
    {
        return memcmp(l->sdata, r->sdata, 16) == 0;
    }
};

class BSQDataHash : public BSQRef
{
public:
    const uint64_t hdata;

    BSQDataHash(uint64_t hdata) : BSQRef(), hdata(hdata) { ; }
    virtual ~BSQDataHash() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQDataHash* h)
    {
        return (size_t)h->hdata;
    }

    static bool keyEqual(const BSQDataHash* l, const BSQDataHash* r)
    {
        l->hdata == r->hdata;
    }
};

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t sdata[64]) : BSQRef(), hdata() { memcpy_s((void*)this->hdata, 64, hdata, 64); }
    virtual ~BSQCryptoHash() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQCryptoHash* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }
};

class BSQEventTime : public BSQRef
{
public:
    const uint64_t timestamp;

    BSQEventTime(uint64_t timestamp) : BSQRef(), timestamp(timestamp) { ; }
    virtual ~BSQEventTime() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQEventTime* t)
    {
        return (size_t)t->timestamp;
    }

    static bool keyEqual(const BSQEventTime* l, const BSQEventTime* r)
    {
        return l->timestamp == r->timestamp;
    }
};

class BSQEnum : public BSQRef
{
public:
    const uint32_t value;
    const MIRNominalTypeEnum oftype;

    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : BSQRef(), value(value), oftype(oftype) { ; }
    virtual ~BSQEnum() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQEnum* e)
    {
        return HASH_COMBINE((size_t)e->oftype, (size_t)e->value);
    }

    static bool keyEqual(const BSQEnum* l, const BSQEnum* r)
    {
        return (l->oftype == r->oftype) & (l->value == r->value);
    }
};

class BSQIdKey : public BSQRef
{
private:
    static size_t hh(MIRNominalTypeEnum oftype, const std::vector<std::pair<MIRPropertyEnum, KeyValue>>& keys)
    {
        size_t hv = (size_t)oftype;
        for(size_t i = 0; i < keys.size(); ++i)
        {
            hv = HASH_COMBINE(hv, HASH_COMBINE((size_t)keys[i].first, bsqKeyValueHash(keys[i].second)));
        }
        return hv;
    }

public:
    const MIRNominalTypeEnum oftype;
    const size_t hash;
    const std::vector<std::pair<MIRPropertyEnum, KeyValue>> keys;

    BSQIdKey(KeyValue key, MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), hash(HASH_COMBINE((size_t)oftype, bsqKeyValueHash(key))), keys({std::make_pair(MIRPropertyEnum::Invalid, key)}) { ; }
    BSQIdKey(std::vector<std::pair<MIRPropertyEnum, KeyValue>>&& keys, MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), hash(hh(oftype, keys)), keys(move(keys)) { ; }
    virtual ~BSQIdKey() = default;

    virtual void destroy() 
    {
        for(size_t i = 0; i < this->keys.size(); ++i)
        {
            BSQRef::decrementChecked(this->keys[i].second); 
        }
    }

    static size_t hash(const BSQIdKey* k)
    {
       return k->hash;
    }

    static bool keyEqual(const BSQIdKey* l, const BSQIdKey* r)
    {
        if(l->hash != r->hash)
        {
            return false;
        }

        if(l->oftype != r->oftype || l->keys.size() != r->keys.size())
        {
            return false;
        }
        
        for(size_t i = 0; i < l->keys.size(); ++i)
        {
            if(l->keys[i].first != r->keys[i].first || !bsqKeyValueEqual(l->keys[i].second, r->keys[i].second))
            {
                return false;
            }
        }

        return true;
    }
};

class BSQGUIDIdKey : public BSQRef
{
public:
    const BSQGUID gdata;
    const MIRNominalTypeEnum oftype;

    BSQGUIDIdKey(const BSQGUID& gdata, MIRNominalTypeEnum oftype) : BSQRef(), gdata(gdata), oftype(oftype) { ; }

    virtual ~BSQGUIDIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQGUIDIdKey* g)
    {
        return HASH_COMBINE((size_t)g->oftype, BSQGUID::hash(&g->gdata));
    }

    static bool keyEqual(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r)
    {
        return l->oftype == r->oftype && memcmp(l->gdata.sdata, r->gdata.sdata, 16) == 0;
    }
};

class BSQDataHashIdKey : public BSQRef
{
public:
    const BSQDataHash hdata;
    const MIRNominalTypeEnum oftype;

    BSQDataHashIdKey(const BSQDataHash& hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    virtual ~BSQDataHashIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQDataHashIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype, BSQDataHash::hash(&k->hdata));
    }

    static bool keyEqual(const BSQDataHashIdKey* l, const BSQDataHashIdKey* r)
    {
        return (l->oftype == r->oftype) & (l->hdata.hdata == r->hdata.hdata);
    }
};

class BSQCryptoHashIdKey : public BSQRef
{
public:
    const BSQCryptoHash hdata;
    const MIRNominalTypeEnum oftype;

    BSQCryptoHashIdKey(const BSQCryptoHash& hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    virtual ~BSQCryptoHashIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQCryptoHashIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype, BSQCryptoHash::hash(&k->hdata));
    }

    static bool keyEqual(const BSQCryptoHashIdKey* l, const BSQCryptoHashIdKey* r)
    {
        return l->oftype == r->oftype && memcmp(l->hdata.hdata, r->hdata.hdata, 64) == 0;
    }
};
}
