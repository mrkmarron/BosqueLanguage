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

    inline static size_t hash(const BSQString* str)
    {
        return std::hash<std::u32string>{}(str->sdata);
    }
    
    inline static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        return l->sdata == r->sdata;
    }
};
struct HashFunctor_BSQString
{
    size_t operator()(const BSQString& s) { return BSQString::hash(&s); }
};
struct EqualFunctor_BSQString
{
    bool operator()(const BSQString& l, const BSQString& r) { return BSQString::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQString
{
    std::u32string operator()(const BSQString& s) { return std::u32string(U"\"") + std::u32string(s.sdata.cbegin(), s.sdata.cend()) + std::u32string(U"\""); }
};

class BSQValidatedStringOf : public BSQRef
{
public:
    const std::u32string sdata;
    const MIRNominalTypeEnum oftype;
  
    BSQValidatedStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }

    virtual ~BSQValidatedStringOf() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQValidatedStringOf* str)
    {
        return HASH_COMBINE((size_t)str->oftype, std::hash<std::u32string>{}(str->sdata));
    }

    inline static bool keyEqual(const BSQValidatedStringOf* l, const BSQValidatedStringOf* r)
    {
        return l->oftype == r->oftype && l->sdata == r->sdata;
    }
};
struct HashFunctor_BSQValidatedStringOf
{
    size_t operator()(const BSQValidatedStringOf& s) { return BSQValidatedStringOf::hash(&s); }
};
struct EqualFunctor_BSQValidatedStringOf
{
    bool operator()(const BSQValidatedStringOf& l, const BSQValidatedStringOf& r) { return BSQValidatedStringOf::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQValidatedStringOf
{
    std::u32string operator()(const BSQValidatedStringOf& s) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)s.oftype]) + std::u32string(U"'") + s.sdata + std::u32string(U"'"); 
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

    inline static size_t hash(const BSQStringOf* str)
    {
        return HASH_COMBINE((size_t)str->oftype, std::hash<std::u32string>{}(str->sdata));
    }

    inline static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        return l->oftype == r->oftype && l->sdata == r->sdata;
    }
};
struct HashFunctor_BSQStringOf
{
    size_t operator()(const BSQStringOf& s) { return BSQStringOf::hash(&s); }
};
struct EqualFunctor_BSQStringOf
{
    bool operator()(const BSQStringOf& l, const BSQStringOf& r) { return BSQStringOf::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQStringOf
{
    std::u32string operator()(const BSQStringOf& s) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)s.oftype]) + std::u32string(U"'") + s.sdata + std::u32string(U"'"); 
    }
};

class BSQGUID : public BSQRef
{
public:
    const uint8_t sdata[16];

    BSQGUID(const uint8_t sdata[16]) : BSQRef(), sdata() { memcpy_s((void*)this->sdata, 16, sdata, 16); }

    virtual ~BSQGUID() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQGUID* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    inline static bool keyEqual(const BSQGUID* l, const BSQGUID* r)
    {
        return memcmp(l->sdata, r->sdata, 16) == 0;
    }
};
struct HashFunctor_BSQGUID
{
    size_t operator()(const BSQGUID& g) { return BSQGUID::hash(&g); }
};
struct EqualFunctor_BSQGUID
{
    bool operator()(const BSQGUID& l, const BSQGUID& r) { return BSQGUID::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQGUID
{
    std::u32string operator()(const BSQGUID& g) { return std::u32string(U"DataHash@") + std::u32string(g.sdata, g.sdata + 16); }
};

class BSQEventTime : public BSQRef
{
public:
    uint64_t timestamp;

    BSQEventTime() : BSQRef() { ; }
    BSQEventTime(uint64_t timestamp) : BSQRef(), timestamp(timestamp) { ; }

    BSQEventTime(const BSQEventTime& src) : BSQRef(), timestamp(src.timestamp)
    { 
        ; 
    }

    BSQEventTime& operator=(const BSQEventTime& src)
    {
        this->timestamp = src.timestamp;
        return *this;
    }

    virtual ~BSQEventTime() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQEventTime* t)
    {
        return (size_t)t->timestamp;
    }

    inline static bool keyEqual(const BSQEventTime* l, const BSQEventTime* r)
    {
        return l->timestamp == r->timestamp;
    }
};
struct HashFunctor_BSQEventTime
{
    size_t operator()(const BSQEventTime& et) { return BSQEventTime::hash(&et); }
};
struct EqualFunctor_BSQEventTime
{
    bool operator()(const BSQEventTime& l, const BSQEventTime& r) { return BSQEventTime::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQEventTime
{
    std::u32string operator()(const BSQEventTime& et) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return std::u32string(U"EventTime@") + conv.from_bytes(std::to_string(et.timestamp)); 
    }
};

class BSQDataHash : public BSQRef
{
public:
    uint64_t hdata;

    BSQDataHash() : BSQRef() { ; }
    BSQDataHash(uint64_t hdata) : BSQRef(), hdata(hdata) { ; }

    BSQDataHash(const BSQDataHash& src) : BSQRef(), hdata(src.hdata)
    { 
        ; 
    }

    BSQDataHash& operator=(const BSQDataHash& src)
    {
        this->hdata = src.hdata;
        return *this;
    }

    virtual ~BSQDataHash() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQDataHash* h)
    {
        return (size_t)h->hdata;
    }

    inline static bool keyEqual(const BSQDataHash* l, const BSQDataHash* r)
    {
        l->hdata == r->hdata;
    }
};
struct HashFunctor_BSQDataHash
{
    size_t operator()(const BSQDataHash& h) { return BSQDataHash::hash(&h); }
};
struct EqualFunctor_BSQDataHash
{
    bool operator()(const BSQDataHash& l, const BSQDataHash& r) { return BSQDataHash::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQDataHash
{
    std::u32string operator()(const BSQDataHash& h) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return std::u32string(U"DataHash@") + conv.from_bytes(std::to_string(h.hdata)); 
    }
};

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t sdata[64]) : BSQRef(), hdata() { memcpy_s((void*)this->hdata, 64, hdata, 64); }
    virtual ~BSQCryptoHash() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQCryptoHash* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    inline static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }
};
struct HashFunctor_BSQCryptoHash
{
    size_t operator()(const BSQCryptoHash& h) { return BSQCryptoHash::hash(&h); }
};
struct EqualFunctor_BSQCryptoHash
{
    bool operator()(const BSQCryptoHash& l, const BSQCryptoHash& r) { return BSQCryptoHash::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQCryptoHash
{
    std::u32string operator()(const BSQCryptoHash& h) { return std::u32string(U"CryptoHash@") + std::u32string(h.hdata, h.hdata + 64); }
};

class BSQEnum : public BSQRef
{
public:
    uint32_t value;
    MIRNominalTypeEnum oftype;

    BSQEnum() : BSQRef() { ; }
    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : BSQRef(), value(value), oftype(oftype) { ; }

    BSQEnum(const BSQEnum& src) : BSQRef(), value(src.value), oftype(src.oftype)
    { 
        ; 
    }

    BSQEnum& operator=(const BSQEnum& src)
    {
        this->value = src.value;
        this->oftype = src.oftype;
        return *this;
    }

    virtual ~BSQEnum() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQEnum* e)
    {
        return HASH_COMBINE((size_t)e->oftype, (size_t)e->value);
    }

    inline static bool keyEqual(const BSQEnum* l, const BSQEnum* r)
    {
        return (l->oftype == r->oftype) & (l->value == r->value);
    }
};
struct HashFunctor_BSQEnum
{
    size_t operator()(const BSQEnum& e) { return BSQEnum::hash(&e); }
};
struct EqualFunctor_BSQEnum
{
    bool operator()(const BSQEnum& l, const BSQEnum& r) { return BSQEnum::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQEnum
{
    std::u32string operator()(const BSQEnum& e) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)e.oftype]) + std::u32string(U"::") + conv.from_bytes(std::to_string(e.value)); 
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
    const size_t vhash;
    const std::vector<std::pair<MIRPropertyEnum, KeyValue>> keys;

    BSQIdKey(KeyValue key, MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), vhash(HASH_COMBINE((size_t)oftype, bsqKeyValueHash(key))), keys({std::make_pair(MIRPropertyEnum::Invalid, key)}) { ; }
    BSQIdKey(std::vector<std::pair<MIRPropertyEnum, KeyValue>>&& keys, MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), vhash(hh(oftype, keys)), keys(move(keys)) { ; }
    virtual ~BSQIdKey() = default;

    virtual void destroy() 
    {
        for(size_t i = 0; i < this->keys.size(); ++i)
        {
            BSQRef::decrementChecked(this->keys[i].second); 
        }
    }

    inline static size_t hash(const BSQIdKey* k)
    {
       return k->vhash;
    }

    inline static bool keyEqual(const BSQIdKey* l, const BSQIdKey* r)
    {
        if(l->vhash != r->vhash)
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
struct HashFunctor_BSQIdKey
{
    size_t operator()(const BSQIdKey& idk) { return BSQIdKey::hash(&idk); }
};
struct EqualFunctor_BSQIdKey
{
    bool operator()(const BSQIdKey& l, const BSQIdKey& r) { return BSQIdKey::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQIdKey
{
    std::u32string operator()(const BSQIdKey& idk) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        std::u32string rvals = conv.from_bytes(nominaltypenames[(uint32_t)idk.oftype]);
        if(idk.keys.size() == 1) 
        {
            return rvals + U" of " + diagnostic_format(idk.keys[0].second);
        }
        else
        {
            rvals +=  U" of { ";
            for(size_t i = 0; i < idk.keys.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += U", ";
                }

                rvals += conv.from_bytes(propertyNames[(int32_t)idk.keys[i].first]) + U"=" + diagnostic_format(idk.keys[i].second);
            }
            rvals += U" }"; 
        }
    }
};

class BSQGUIDIdKey : public BSQRef
{
public:
    const uint8_t sdata[16];
    const MIRNominalTypeEnum oftype;

    BSQGUIDIdKey(const uint8_t sdata[16], MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), sdata() { memcpy_s((void*)this->sdata, 16, sdata, 16); }

    virtual ~BSQGUIDIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQGUIDIdKey* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    inline static bool keyEqual(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r)
    {
        return memcmp(l->sdata, r->sdata, 16) == 0;
    }
};
struct HashFunctor_BSQGUIDIdKey
{
    size_t operator()(const BSQGUIDIdKey& idg) { return BSQGUIDIdKey::hash(&idg); }
};
struct EqualFunctor_BSQGUIDIdKey
{
    bool operator()(const BSQGUIDIdKey& l, const BSQGUIDIdKey& r) { return BSQGUIDIdKey::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQGUIDIdKey
{
    std::u32string operator()(const BSQGUIDIdKey& idg) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)idg.oftype]) + std::u32string(U"::") + std::u32string(idg.sdata, idg.sdata + 16); 
    }
};

class BSQEventTimeIdKey : public BSQRef
{
public:
    uint64_t timestamp;
    MIRNominalTypeEnum oftype;

    BSQEventTimeIdKey() : BSQRef() { ; }
    BSQEventTimeIdKey(uint64_t timestamp, MIRNominalTypeEnum oftype) : BSQRef(), timestamp(timestamp), oftype(oftype) { ; }

    BSQEventTimeIdKey(const BSQEventTimeIdKey& src) : BSQRef(), timestamp(src.timestamp), oftype(src.oftype)
    { 
        ; 
    }

    BSQEventTimeIdKey& operator=(const BSQEventTimeIdKey& src)
    {
        this->timestamp = src.timestamp;
        this->oftype = src.oftype;
        return *this;
    }

    virtual ~BSQEventTimeIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQEventTimeIdKey* tid)
    {
        return HASH_COMBINE((size_t)tid->oftype, tid->timestamp);
    }

    inline static bool keyEqual(const BSQEventTimeIdKey* l, const BSQEventTimeIdKey* r)
    {
        return l->oftype == r->oftype && l->timestamp == r->timestamp;
    }
};
struct HashFunctor_BSQEventTimeIdKey
{
    size_t operator()(const BSQEventTimeIdKey& idt) { return BSQEventTimeIdKey::hash(&idt); }
};
struct EqualFunctor_BSQEventTimeIdKey
{
    bool operator()(const BSQEventTimeIdKey& l, const BSQEventTimeIdKey& r) { return BSQEventTimeIdKey::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQEventTimeIdKey
{
    std::u32string operator()(const BSQEventTimeIdKey& idt) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)idt.oftype]) + std::u32string(U"::") + conv.from_bytes(std::to_string(idt.timestamp)); 
    }
};

class BSQDataHashIdKey : public BSQRef
{
public:
    uint64_t hdata;
    MIRNominalTypeEnum oftype;

    BSQDataHashIdKey() : BSQRef() { ; }
    BSQDataHashIdKey(uint64_t hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    BSQDataHashIdKey(const BSQDataHashIdKey& src) : BSQRef(), hdata(src.hdata), oftype(src.oftype)
    { 
        ; 
    }

    BSQDataHashIdKey& operator=(const BSQDataHashIdKey& src)
    {
        this->hdata = src.hdata;
        this->oftype = src.oftype;
        return *this;
    }

    virtual ~BSQDataHashIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQDataHashIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype,k->hdata);
    }

    inline static bool keyEqual(const BSQDataHashIdKey* l, const BSQDataHashIdKey* r)
    {
        return (l->oftype == r->oftype) & (l->hdata == r->hdata);
    }
};
struct HashFunctor_BSQDataHashIdKey
{
    size_t operator()(const BSQDataHashIdKey& ihd) { return BSQDataHashIdKey::hash(&ihd); }
};
struct EqualFunctor_BSQDataHashIdKey
{
    bool operator()(const BSQDataHashIdKey& l, const BSQDataHashIdKey& r) { return BSQDataHashIdKey::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQDataHashIdKey
{
    std::u32string operator()(const BSQDataHashIdKey& idh) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)idh.oftype]) + std::u32string(U"::") + conv.from_bytes(std::to_string(idh.hdata)); 
    }
};

class BSQCryptoHashIdKey : public BSQRef
{
public:
    const uint8_t hdata[64];
    const MIRNominalTypeEnum oftype;

    BSQCryptoHashIdKey(const uint8_t hdata[64], MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), hdata() { memcpy_s((void*)this->hdata, 64, hdata, 64); }

    virtual ~BSQCryptoHashIdKey() = default;
    virtual void destroy() { ; }

    inline static size_t hash(const BSQCryptoHashIdKey* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    inline static bool keyEqual(const BSQCryptoHashIdKey* l, const BSQCryptoHashIdKey* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }
};
struct HashFunctor_BSQCryptoHashIdKey
{
    size_t operator()(const BSQCryptoHashIdKey& ihc) { return BSQCryptoHashIdKey::hash(&ihc); }
};
struct EqualFunctor_BSQCryptoHashIdKey
{
    bool operator()(const BSQCryptoHashIdKey& l, const BSQCryptoHashIdKey& r) { return BSQCryptoHashIdKey::keyEqual(&l, &r); }
};
struct DisplayFunctor_BSQCryptoHashIdKey
{
    std::u32string operator()(const BSQCryptoHashIdKey& ihc) 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(nominaltypenames[(uint32_t)ihc.oftype]) + std::u32string(U"::") + std::u32string(ihc.hdata, ihc.hdata + 64); 
    }
};
}
