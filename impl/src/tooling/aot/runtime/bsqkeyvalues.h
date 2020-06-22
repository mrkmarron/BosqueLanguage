//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "bsqvalue.h"

namespace BSQ
{
struct BSQBigInt
{
    MetaData* mdata;
    void* bigint; //right now this should always be null and ignored
    int64_t simpleint;

    std::wstring display() const
    {
        return std::to_wstring(this->simpleint);
    }

    bool eqI64(int64_t v) const
    {
        return this->simpleint == v;
    }

    bool ltI64(int64_t v) const
    {
        return this->simpleint < v;
    }

    static BSQBigInt negate(const BSQBigInt& v);

    static bool eq(const BSQBigInt& l, const BSQBigInt& r);
    static bool lt(const BSQBigInt& l, const BSQBigInt& r);

    static BSQBigInt add(const BSQBigInt& l, const BSQBigInt& r);
    static BSQBigInt sub(const BSQBigInt& l, const BSQBigInt& r);
    static BSQBigInt mult(const BSQBigInt& l, const BSQBigInt& r);
    static BSQBigInt div(const BSQBigInt& l, const BSQBigInt& r);
    static BSQBigInt mod(const BSQBigInt& l, const BSQBigInt& r);
};
struct EqualFunctor_BSQBigInt
{
    inline bool operator()(const BSQBigInt& l, const BSQBigInt& r) const { return BSQBigInt::eq(l, r); }
};
struct LessFunctor_BSQBigInt
{
    inline bool operator()(const BSQBigInt& l, const BSQBigInt& r) const { return BSQBigInt::lt(l, r); }
};

typedef BSQBoxedWithMeta<BSQBigInt> Boxed_BigInt;
struct DisplayFunctor_BSQBigInt
{
    std::wstring operator()(BSQBigInt i) const { return i.display(); }
};

void* ExtractGeneralRepr_BSQBigInt(void* v);
std::wstring DisplayFunction_BSQBigInt(void* v);
constexpr MetaData MetaData_BSQBigInt = {
    MIRNominalTypeEnum_BigInt,
    MIRNominalTypeEnum_Category_BigInt,
    DATA_KIND_ALL_FLAG,
    ExtractFlag::StructAllocNoMeta,
    sizeof(Boxed_BigInt),
    ObjectLayoutKind::Packed,
    1,
    nullptr,
    0,
    L"BigInt",
    &DisplayFunction_BSQBigInt,
    &ExtractGeneralRepr_Identity
};

struct BSQString
{
    MetaData* mdata;
    size_t count;

    inline static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        if(l->count != r->count)
        {
            return false;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(l);
            const wchar_t* rdata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(r);
            std::equal(ldata, ldata + l->count, rdata, rdata + r->count);
        }
    }

    inline static bool keyLess(const BSQString* l, const BSQString* r)
    {
        if(l->count != r->count)
        {
            return l->count - r->count;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(l);
            const wchar_t* rdata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(r);
            auto mmiter = std::mismatch(ldata, ldata + l->count, rdata, rdata + r->count);

            if(mmiter.first == ldata + l->count)
            {
                return 0;
            }
            else
            {
                return *(mmiter.first) - *(mmiter.second);
            }
        }
    }
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
    std::wstring operator()(const BSQString* s) const 
    {
        const wchar_t* data = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(s); 
        return std::wstring(L"\"") + std::wstring(data, data + s->count) + std::wstring(L"\""); 
    }
};

std::wstring DisplayFunction_BSQString(void* v);
constexpr MetaData MetaData_BSQString = {
    MIRNominalTypeEnum_String,
    MIRNominalTypeEnum_Category_String,
    DATA_KIND_API_FLAG,
    ExtractFlag::Pointer,
    sizeof(BSQString),
    ObjectLayoutKind::CollectionNoRef,
    0,
    nullptr,
    1,
    L"String",
    &DisplayFunction_BSQString,
    &ExtractGeneralRepr_Identity
};

struct BSQSafeString
{
    MetaData* mdata;
    BSQString* sdata;
  
    BSQSafeString(const std::string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

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
    std::string operator()(const BSQSafeString* s) const 
    { 
        return nominaltypenames[GET_MIR_TYPE_POSITION(s->nominalType)] + std::string("'") + s->sdata + std::string("'"); 
    }
};

class BSQStringOf : public BSQRef
{
public:
    const std::string sdata;
  
    BSQStringOf(const std::string& str, MIRNominalTypeEnum oftype) : BSQRef(oftype), sdata(str) { ; }

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
    std::string operator()(const BSQStringOf* s) const 
    { 
        return nominaltypenames[GET_MIR_TYPE_POSITION(s->nominalType)] + std::string("'") + s->sdata + std::string("'"); 
    }
};

class BSQUUID
{
public:
    uint8_t sdata[16];

    BSQUUID() { ; }
    BSQUUID(const uint8_t(&sdata)[16]) { memcpy(this->sdata, sdata, 16); }

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
    std::string operator()(const BSQUUID& u) const { return std::string("DataHash@") + std::string(u.sdata, u.sdata + 16); }
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
    std::string operator()(const BSQLogicalTime& et) const 
    { 
        return std::string("LogicalTime@") + std::to_string(et.timestamp); 
    }
};
typedef BSQBoxed<BSQLogicalTime, RCDecFunctor_BSQLogicalTime> Boxed_BSQLogicalTime;

class BSQCryptoHash : public BSQRef
{
public:
    uint8_t hdata[64];

    BSQCryptoHash(const uint8_t(&sdata)[64]) : BSQRef(MIRNominalTypeEnum_CryptoHash) { memcpy((void*)this->hdata, hdata, 64); }
    
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
    std::string operator()(const BSQCryptoHash* h) const { return std::string("CryptoHash@") + std::string(h->hdata, h->hdata + 64); }
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
    std::string operator()(const BSQEnum& e) const 
    { 
        return nominaltypenames[GET_MIR_TYPE_POSITION(e.nominalType)] + std::string("::") + std::to_string(e.value); 
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
    std::string operator()(const BSQIdKeySimple& idk) const 
    { 
        std::string rvals = nominaltypenames[GET_MIR_TYPE_POSITION(idk.nominalType)];
        return rvals + " of " + diagnostic_format(idk.key);
    }
};
typedef BSQBoxed<BSQIdKeySimple, RCDecFunctor_BSQIdKeySimple> Boxed_BSQIdKeySimple;

class BSQIdKeyCompound
{
public:
    //
    //TODO: when we add back unions this needs to be changed to a template <n> thing since vector is not POD
    //
    std::vector<KeyValue> keys;
    MIRNominalTypeEnum nominalType;

    BSQIdKeyCompound() { ; }
    BSQIdKeyCompound(std::vector<KeyValue>&& keys, MIRNominalTypeEnum oftype) : keys(std::move(keys)), nominalType(oftype) { ; }
    
    BSQIdKeyCompound(const BSQIdKeyCompound& src) = default;
    BSQIdKeyCompound(BSQIdKeyCompound&& src) = default;

    BSQIdKeyCompound& operator=(const BSQIdKeyCompound& src) = default;
    BSQIdKeyCompound& operator=(BSQIdKeyCompound&& src) = default;

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

        for(size_t i = 0; i < l.keys.size(); ++i)
        {
            if(!bsqKeyValueEqual(l.keys[i], r.keys[i]))
            {
                return bsqKeyValueLess(l.keys[i], r.keys[i]);
            }
        }

        return false;
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
struct RCReturnFunctor_BSQIdKeyCompound
{
    inline void operator()(BSQIdKeyCompound& idk, BSQRefScope& scope) const 
    { 
        for(size_t i = 0; i < idk.keys.size(); ++i)
        {
            scope.processReturnChecked(idk.keys[i]);
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
    std::string operator()(const BSQIdKeyCompound& idk) const 
    { 
        std::string rvals = nominaltypenames[GET_MIR_TYPE_POSITION(idk.nominalType)];
        rvals +=  " of ( ";
        for(size_t i = 0; i < idk.keys.size(); ++i)
        {
            if(i != 0)
            {
                rvals += ", ";
            }

            rvals += diagnostic_format(idk.keys[i]);
        }
        rvals += " )"; 

        return rvals;
    }
};
typedef BSQBoxed<BSQIdKeyCompound, RCDecFunctor_BSQIdKeyCompound> Boxed_BSQIdKeyCompound;
}
