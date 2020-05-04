//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

namespace BSQ
{
class BSQBigInt : public BSQRef
{
public:
    BSQBigInt(int64_t value) : BSQRef(MIRNominalTypeEnum_BigInt) { ; }
    BSQBigInt(const char* bigstr) : BSQRef(MIRNominalTypeEnum_Int) { ; }

    BSQBigInt(const BSQBigInt& src) : BSQRef(MIRNominalTypeEnum_BigInt) 
    { 
        ; 
    }

    BSQBigInt(BSQBigInt&& src) : BSQRef(MIRNominalTypeEnum_BigInt) 
    { 
        ;
    }

    BSQBigInt& operator=(const BSQBigInt& src) {
        if(this == &src) {
            return *this;
        }

        return *this;
    }

    BSQBigInt& operator=(BSQBigInt&& src) {
        if(this == &src) {
            return *this;
        }

        return *this;
    }

    ~BSQBigInt() { ; }
    virtual void destroy() { ; }

    std::u32string display() const
    {
        return U"[NOT IMPLEMENTED]";
    }

    static BSQBigInt* negate(BSQRefScope& scope, const BSQBigInt* v)
    {
        return nullptr;
    }

    bool eqI64(int64_t v) const
    {
        return false;
    }

    bool ltI64(int64_t v) const
    {
        return false;
    }

    static bool eq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool lt(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static BSQBigInt* add(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* sub(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mult(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* div(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mod(BSQRefScope& scope, const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }
};
struct RCIncFunctor_BSQBigInt
{
    inline BSQBigInt* operator()(BSQBigInt* i) const { return INC_REF_DIRECT(BSQBigInt, i); }
};
struct RCDecFunctor_BSQBigInt
{
    inline void operator()(BSQBigInt* i) const { BSQRef::decrementDirect(i); }
};
struct EqualFunctor_BSQBigInt
{
    inline bool operator()(BSQBigInt* l, BSQBigInt* r) const { return BSQBigInt::eq(l, r); }
};
struct LessFunctor_BSQBigInt
{
    inline bool operator()(BSQBigInt* l, BSQBigInt* r) const { return BSQBigInt::lt(l, r); }
};
struct DisplayFunctor_BSQBigInt
{
    std::u32string operator()(BSQBigInt* i) const { return i->display(); }
};

class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(MIRNominalTypeEnum_String), sdata(str) { ; }
    BSQString(const char32_t* str, int64_t excount) : BSQRef(excount, MIRNominalTypeEnum_String), sdata(str) { ; }

    virtual ~BSQString() = default;

    inline static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        return l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQString* l, const BSQString* r)
    {
        return l->sdata < r->sdata;
    }
};
struct RCIncFunctor_BSQString
{
    inline BSQString* operator()(BSQString* s) const { return INC_REF_DIRECT(BSQString, s); }
};
struct RCDecFunctor_BSQString
{
    inline void operator()(BSQString* s) const { BSQRef::decrementDirect(s); }
};
struct EqualFunctor_BSQString
{
    inline bool operator()(const BSQString* l, const BSQString* r) const { return BSQString::keyEqual(l, r); }
};
struct LessFunctor_BSQString
{
    inline bool operator()(const BSQString* l, const BSQString* r) const { return BSQString::keyLess(l, r); }
};
struct DisplayFunctor_BSQString
{
    std::u32string operator()(const BSQString* s) const { return std::u32string(U"\"") + std::u32string(s->sdata.cbegin(), s->sdata.cend()) + std::u32string(U"\""); }
};

class BSQSafeString : public BSQRef
{
public:
    const std::u32string sdata;
  
    BSQSafeString(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

    virtual ~BSQSafeString() = default;

    inline static bool keyEqual(const BSQSafeString* l, const BSQSafeString* r)
    {
        return l->nominalType == r->nominalType && l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQSafeString* l, const BSQSafeString* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : (l->sdata < r->sdata);
    }
};
struct RCIncFunctor_BSQSafeString
{
    inline BSQSafeString* operator()(BSQSafeString* s) const { return INC_REF_DIRECT(BSQSafeString, s); }
};
struct RCDecFunctor_BSQSafeString
{
    inline void operator()(BSQSafeString* s) const { BSQRef::decrementDirect(s); }
};
struct EqualFunctor_BSQSafeString
{
    inline bool operator()(const BSQSafeString* l, const BSQSafeString* r) const { return BSQSafeString::keyEqual(l, r); }
};
struct LessFunctor_BSQSafeString
{
    inline bool operator()(const BSQSafeString* l, const BSQSafeString* r) const { return BSQSafeString::keyLess(l, r); }
};
struct DisplayFunctor_BSQSafeString
{
    std::u32string operator()(const BSQSafeString* s) const 
    { 
        return nominaltypenames[GET_MIR_TYPE_POSITION(s->nominalType)] + std::u32string(U"'") + s->sdata + std::u32string(U"'"); 
    }
};

class BSQStringOf : public BSQRef
{
public:
    const std::u32string sdata;
  
    BSQStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

    virtual ~BSQStringOf() = default;

    inline static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        return l->nominalType == r->nominalType && l->sdata == r->sdata;
    }

    inline static bool keyLess(const BSQStringOf* l, const BSQStringOf* r)
    {
        return (l->nominalType != r->nominalType) ? (l->nominalType < r->nominalType) : (l->sdata < r->sdata);
    }
};
struct RCIncFunctor_BSQStringOf
{
    inline BSQStringOf* operator()(BSQStringOf* s) const { return INC_REF_DIRECT(BSQStringOf, s); }
};
struct RCDecFunctor_BSQStringOf
{
    inline void operator()(BSQStringOf* s) const { BSQRef::decrementDirect(s); }
};
struct EqualFunctor_BSQStringOf
{
    inline bool operator()(const BSQStringOf* l, const BSQStringOf* r) const { return BSQStringOf::keyEqual(l, r); }
};
struct LessFunctor_BSQStringOf
{
    inline bool operator()(const BSQStringOf* l, const BSQStringOf* r) const { return BSQStringOf::keyLess(l, r); }
};
struct DisplayFunctor_BSQStringOf
{
    std::u32string operator()(const BSQStringOf* s) const 
    { 
        return nominaltypenames[GET_MIR_TYPE_POSITION(s->nominalType)] + std::u32string(U"'") + s->sdata + std::u32string(U"'"); 
    }
};

class BSQUUID
{
public:
    uint8_t sdata[16];

    BSQUUID() { ; }
    BSQUUID(const uint8_t(&sdata)[16]) : sdata() { memcpy(this->sdata, sdata, 16); }

    BSQUUID(const BSQUUID& src) = default;
    BSQUUID(BSQUUID&& src) = default;

    BSQUUID& operator=(const BSQUUID&) = default;
    BSQUUID& operator=(BSQUUID&&) = default;

    inline static bool keyEqual(const BSQUUID& l, const BSQUUID& r)
    {
        return memcmp(l.sdata, r.sdata, 16) == 0;
    }

    inline static bool keyLess(const BSQUUID& l, const BSQUUID& r)
    {
        return memcmp(l.sdata, r.sdata, 16) < 0;
    }
};
struct RCIncFunctor_BSQUUID
{
    inline BSQUUID operator()(BSQUUID uuid) const { return uuid; }
};
struct RCDecFunctor_BSQUUID
{
    inline void operator()(BSQUUID uuid) const { ; }
};
struct RCReturnFunctor_BSQUUID
{
    inline void operator()(BSQUUID& uuid, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_BSQUUID
{
    inline bool operator()(const BSQUUID& l, const BSQUUID& r) const { return BSQUUID::keyEqual(l, r); }
};
struct LessFunctor_BSQUUID
{
    inline bool operator()(const BSQUUID& l, const BSQUUID& r) const { return BSQUUID::keyLess(l, r); }
};
struct DisplayFunctor_BSQUUID
{
    std::u32string operator()(const BSQUUID& u) const { return std::u32string(U"DataHash@") + std::u32string(u.sdata, u.sdata + 16); }
};
typedef BSQBoxed<BSQUUID, RCDecFunctor_BSQUUID> Boxed_BSQUUID;

class BSQLogicalTime
{
public:
    uint64_t timestamp;

    BSQLogicalTime() { ; }
    BSQLogicalTime(uint64_t timestamp) : timestamp(timestamp) { ; }

    BSQLogicalTime(const BSQLogicalTime& src) = default;
    BSQLogicalTime(BSQLogicalTime&& src) = default;

    BSQLogicalTime& operator=(const BSQLogicalTime& src) = default;
    BSQLogicalTime& operator=(BSQLogicalTime&& src) = default;

    inline static bool keyEqual(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp == r.timestamp;
    }

    inline static bool keyLess(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp < r.timestamp;
    }
};
struct RCIncFunctor_BSQLogicalTime
{
    inline BSQLogicalTime operator()(BSQLogicalTime lt) const { return lt; }
};
struct RCDecFunctor_BSQLogicalTime
{
    inline void operator()(BSQLogicalTime lt) const { ; }
};
struct RCReturnFunctor_BSQLogicalTime
{
    inline void operator()(BSQLogicalTime& lt, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_BSQLogicalTime
{
    inline bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyEqual(l, r); }
};
struct LessFunctor_BSQLogicalTime
{
    inline bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyLess(l, r); }
};
struct DisplayFunctor_BSQLogicalTime
{
    std::u32string operator()(const BSQLogicalTime& et) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return std::u32string(U"LogicalTime@") + conv.from_bytes(std::to_string(et.timestamp)); 
    }
};
typedef BSQBoxed<BSQLogicalTime, RCDecFunctor_BSQLogicalTime> Boxed_BSQLogicalTime;

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t(&sdata)[64]) : BSQRef(MIRNominalTypeEnum_CryptoHash), hdata() { memcpy((void*)this->hdata, hdata, 64); }
    
    virtual ~BSQCryptoHash() = default;

    inline static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }

    inline static bool keyLess(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) < 0;
    }
};
struct RCIncFunctor_BSQCryptoHash
{
    inline BSQCryptoHash* operator()(BSQCryptoHash* h) const { return INC_REF_DIRECT(BSQCryptoHash, h); }
};
struct RCDecFunctor_BSQCryptoHash
{
    inline void operator()(BSQCryptoHash* h) const { BSQRef::decrementDirect(h); }
};
struct EqualFunctor_BSQCryptoHash
{
    inline bool operator()(const BSQCryptoHash* l, const BSQCryptoHash* r) const { return BSQCryptoHash::keyEqual(l, r); }
};
struct LessFunctor_BSQCryptoHash
{
    inline bool operator()(const BSQCryptoHash* l, const BSQCryptoHash* r) const { return BSQCryptoHash::keyLess(l, r); }
};
struct DisplayFunctor_BSQCryptoHash
{
    std::u32string operator()(const BSQCryptoHash* h) const { return std::u32string(U"CryptoHash@") + std::u32string(h->hdata, h->hdata + 64); }
};

class BSQEnum
{
public:
    MIRNominalTypeEnum nominalType;
    uint32_t value;

    BSQEnum() { ; }
    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : nominalType(oftype), value(value) { ; }

    BSQEnum(const BSQEnum& src) = default;
    BSQEnum(BSQEnum&& src) = default;

    BSQEnum& operator=(const BSQEnum& src) = default;
    BSQEnum& operator=(BSQEnum&& src) = default;
    
    inline static bool keyEqual(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType == r.nominalType) & (l.value == r.value);
    }

    inline static bool keyLess(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType != r.nominalType) ? (l.nominalType < r.nominalType) : (l.value < r.value);
    }
};
struct RCIncFunctor_BSQEnum
{
    inline BSQEnum operator()(BSQEnum e) const { return e; }
};
struct RCDecFunctor_BSQEnum
{
    inline void operator()(BSQEnum e) const { ; }
};
struct RCReturnFunctor_BSQEnum
{
    inline void operator()(BSQEnum& e, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_BSQEnum
{
    inline bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyEqual(l, r); }
};
struct LessFunctor_BSQEnum
{
    inline bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyLess(l, r); }
};
struct DisplayFunctor_BSQEnum
{
    std::u32string operator()(const BSQEnum& e) const 
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return nominaltypenames[GET_MIR_TYPE_POSITION(e.nominalType)] + std::u32string(U"::") + conv.from_bytes(std::to_string(e.value)); 
    }
};
typedef BSQBoxed<BSQEnum, RCDecFunctor_BSQEnum> Boxed_BSQEnum;

//TODO: may want to make this into a fully specialized set of types with some FP dispatch for KeyValue ops at some point
class BSQIdKeySimple
{
public:
    KeyValue key;
    MIRNominalTypeEnum nominalType;

    BSQIdKeySimple() { ; }
    BSQIdKeySimple(KeyValue key, MIRNominalTypeEnum oftype) : key(key), nominalType(oftype) { ; }
    
    BSQIdKeySimple(const BSQIdKeySimple& src) = default;
    BSQIdKeySimple(BSQIdKeySimple&& src) = default;

    BSQIdKeySimple& operator=(const BSQIdKeySimple& src) = default;
    BSQIdKeySimple& operator=(BSQIdKeySimple&& src) = default;

    inline static bool keyEqual(const BSQIdKeySimple& l, const BSQIdKeySimple& r)
    {
        return (l.nominalType == r.nominalType) && bsqKeyValueEqual(l.key, r.key);
    }

    inline static bool keyLess(const BSQIdKeySimple& l, const BSQIdKeySimple& r)
    {
        if(l.nominalType != r.nominalType)
        {
            return l.nominalType < r.nominalType;
        }

        return bsqKeyValueLess(l.key, r.key);
    }
};
struct RCIncFunctor_BSQIdKeySimple
{
    inline BSQIdKeySimple operator()(BSQIdKeySimple idk) const 
    { 
        BSQRef::incrementChecked(idk.key);
        return idk;
    }
};
struct RCDecFunctor_BSQIdKeySimple
{
    inline void operator()(BSQIdKeySimple idk) const 
    { 
        BSQRef::decrementChecked(idk.key); 
    }
};
struct RCReturnFunctor_BSQIdKeySimple
{
    inline void operator()(BSQIdKeySimple& idk, BSQRefScope& scope) const 
    { 
        scope.processReturnChecked(idk.key); 
    }
};
struct EqualFunctor_BSQIdKeySimple
{
    inline bool operator()(const BSQIdKeySimple& l, const BSQIdKeySimple& r) const { return BSQIdKeySimple::keyEqual(l, r); }
};
struct LessFunctor_BSQIdKeySimple
{
    inline bool operator()(const BSQIdKeySimple& l, const BSQIdKeySimple& r) const { return BSQIdKeySimple::keyLess(l, r); }
};
struct DisplayFunctor_BSQIdKeySimple
{
    std::u32string operator()(const BSQIdKeySimple& idk) const 
    { 
        std::u32string rvals = nominaltypenames[GET_MIR_TYPE_POSITION(idk.nominalType)];
        return rvals + U" of " + diagnostic_format(idk.key);
    }
};
typedef BSQBoxed<BSQIdKeySimple, RCDecFunctor_BSQIdKeySimple> Boxed_BSQIdKeySimple;

class BSQIdKeyCompound
{
public:
    std::vector<KeyValue> keys;
    MIRNominalTypeEnum nominalType;

    BSQIdKeyCompound() { ; }
    BSQIdKeyCompound(std::vector<KeyValue>&& keys, MIRNominalTypeEnum oftype) : keys(move(keys)), nominalType(oftype) { ; }

    BSQIdKeyCompound(const BSQIdKeyCompound& src) : keys(src.keys), nominalType(src.nominalType) { ; };
    BSQIdKeyCompound(BSQIdKeyCompound&& src) : keys(move(src.keys)), nominalType(src.nominalType) { ; }

    BSQIdKeyCompound& operator=(const BSQIdKeyCompound& src)
    {
        if(this == &src)
        {
            return *this;
        }

        this->keys = src.keys;
        this->nominalType = src.nominalType;
        return *this;
    }

    BSQIdKeyCompound& operator=(BSQIdKeyCompound&& src)
    {
        if(this == &src)
        {
            return *this;
        }

        this->keys = std::move(src.keys);
        this->nominalType = src.nominalType;
        return *this;
    }

    static bool keyEqual(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r)
    {
        if(l.nominalType != r.nominalType || l.keys.size() != r.keys.size())
        {
            return false;
        }
        
        for(size_t i = 0; i < l.keys.size(); ++i)
        {
            if(!bsqKeyValueEqual(l.keys[i], r.keys[i]))
            {
                return false;
            }
        }

        return true;
    }

    static bool keyLess(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r)
    {
        if(l.nominalType != r.nominalType)
        {
            return l.nominalType < r.nominalType;
        }

        if(l.keys.size() != r.keys.size())
        {
            return l.keys.size() < r.keys.size();
        }
        
        for(size_t i = 0; i < l.keys.size(); ++i)
        {
            if(!bsqKeyValueEqual(l.keys[i], r.keys[i]))
            {
                return bsqKeyValueLess(l.keys[i], r.keys[i]);
            }
        }

        return true;
    }
};
struct RCIncFunctor_BSQIdKeyCompound
{
    inline BSQIdKeyCompound operator()(BSQIdKeyCompound idk) const 
    { 
        for(size_t i = 0; i < idk.keys.size(); ++i)
        {
            BSQRef::incrementChecked(idk.keys[i]);
        }
        return idk; 
    }
};
struct RCDecFunctor_BSQIdKeyCompound
{
    inline void operator()(BSQIdKeyCompound idk) const
    { 
        for(size_t i = 0; i < idk.keys.size(); ++i)
        {
            BSQRef::decrementChecked(idk.keys[i]);
        }
    }
};
struct EqualFunctor_BSQIdKeyCompound
{
    inline bool operator()(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r) const { return BSQIdKeyCompound::keyEqual(l, r); }
};
struct LessFunctor_BSQIdKeyCompound
{
    inline bool operator()(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r) const { return BSQIdKeyCompound::keyLess(l, r); }
};
struct DisplayFunctor_BSQIdKeyCompound
{
    std::u32string operator()(const BSQIdKeyCompound& idk) const 
    { 
        std::u32string rvals = nominaltypenames[GET_MIR_TYPE_POSITION(idk.nominalType)];
        rvals +=  U" of ( ";
        for(size_t i = 0; i < idk.keys.size(); ++i)
        {
            if(i != 0)
            {
                rvals += U", ";
            }

            rvals += diagnostic_format(idk.keys[i]);
        }
        rvals += U" )"; 

        return rvals;
    }
};
typedef BSQBoxed<BSQIdKeyCompound, RCDecFunctor_BSQIdKeyCompound> Boxed_BSQIdKeyCompound;
}
