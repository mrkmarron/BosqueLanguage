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

typedef BSQBoxed<BSQBigInt> Boxed_BigInt;
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

    static bool keyEqual(const BSQString* l, const BSQString* r)
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

    static bool keyLess(const BSQString* l, const BSQString* r)
    {
        if(l->count != r->count)
        {
            return l->count < r->count;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(l);
            const wchar_t* rdata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(r);
            auto mmiter = std::mismatch(ldata, ldata + l->count, rdata, rdata + r->count);

            if(mmiter.first == ldata + l->count)
            {
                return false;
            }
            else
            {
                return *(mmiter.first) < *(mmiter.second);
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
    size_t count;
    MIRNominalTypeEnum nominalType;

    static bool keyEqual(const BSQSafeString* l, const BSQSafeString* r)
    {
        if(l->nominalType != r->nominalType)
        {
            return false;
        }
        else
        {
            if (l->count != r->count)
            {
                return false;
            }
            else
            {
                const wchar_t *ldata = (wchar_t *)GC_GET_FIRST_COLLECTION_LOC(l);
                const wchar_t *rdata = (wchar_t *)GC_GET_FIRST_COLLECTION_LOC(r);
                std::equal(ldata, ldata + l->count, rdata, rdata + r->count);
            }
        }
    }

    static bool keyLess(const BSQSafeString* l, const BSQSafeString* r)
    {
        if(l->nominalType != r->nominalType)
        {
            return l->nominalType < r->nominalType;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(l);
            const wchar_t* rdata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(r);
            auto mmiter = std::mismatch(ldata, ldata + l->count, rdata, rdata + r->count);

            if(mmiter.first == ldata + l->count)
            {
                return false;
            }
            else
            {
                return *(mmiter.first) < *(mmiter.second);
            }
        }
    }
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
    std::wstring operator()(const BSQSafeString* s) const 
    {
        const wchar_t* data = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(s);
        return std::wstring(s->mdata->displayname) + std::wstring(L"'") + std::wstring(data, data + s->count) + std::wstring(L"'"); 
    }
};
std::wstring DisplayFunction_BSQSafeString(void* v);
constexpr MetaData MetaData_BSQSafeString_Constructor(MIRNominalTypeEnum oftype, const wchar_t* displayname) 
{
    return {
        oftype,
        MIRNominalTypeEnum_Category_SafeString,
        DATA_KIND_ALL_FLAG,
        ExtractFlag::Pointer,
        sizeof(BSQSafeString),
        ObjectLayoutKind::CollectionNoRef,
        0,
        nullptr,
        1,
        displayname,
        &DisplayFunction_BSQSafeString,
        &ExtractGeneralRepr_Identity
    };
}

struct BSQStringOf
{
    MetaData* mdata;
    size_t count;
    MIRNominalTypeEnum nominalType;

    static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        if(l->mdata->nominaltype != r->mdata->nominaltype)
        {
            return false;
        }
        else
        {
            if (l->count != r->count)
            {
                return false;
            }
            else
            {
                const wchar_t *ldata = (wchar_t *)GC_GET_FIRST_COLLECTION_LOC(l);
                const wchar_t *rdata = (wchar_t *)GC_GET_FIRST_COLLECTION_LOC(r);
                std::equal(ldata, ldata + l->count, rdata, rdata + r->count);
            }
        }
    }

    static bool keyLess(const BSQStringOf* l, const BSQStringOf* r)
    {
        if(l->nominalType != r->nominalType)
        {
            return l->nominalType < r->nominalType;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(l);
            const wchar_t* rdata = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(r);
            auto mmiter = std::mismatch(ldata, ldata + l->count, rdata, rdata + r->count);

            if(mmiter.first == ldata + l->count)
            {
                return false;
            }
            else
            {
                return *(mmiter.first) < *(mmiter.second);
            }
        }
    }
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
    std::wstring operator()(const BSQStringOf* s) const 
    { 
        const wchar_t* data = (wchar_t*)GC_GET_FIRST_COLLECTION_LOC(s);
        return std::wstring(s->mdata->displayname) + std::wstring(L"'") + std::wstring(data, data + s->count) + std::wstring(L"'");  
    }
};
std::wstring DisplayFunction_BSQStringOf(void* v);
constexpr MetaData MetaData_BSQStringOf_Constructor(MIRNominalTypeEnum oftype, const wchar_t* displayname) 
{
    return {
        oftype,
        MIRNominalTypeEnum_Category_StringOf,
        DATA_KIND_CLEAR_FLAG,
        ExtractFlag::Pointer,
        sizeof(BSQStringOf),
        ObjectLayoutKind::CollectionNoRef,
        0,
        nullptr,
        1,
        displayname,
        &DisplayFunction_BSQStringOf,
        &ExtractGeneralRepr_Identity
    };
}

struct BSQUUID
{
    uint8_t sdata[16];

    inline static bool keyEqual(const BSQUUID& l, const BSQUUID& r)
    {
        return memcmp(l.sdata, r.sdata, 16) == 0;
    }

    inline static bool keyLess(const BSQUUID& l, const BSQUUID& r)
    {
        return memcmp(l.sdata, r.sdata, 16) < 0;
    }
};
struct EqualFunctor_BSQUUID
{
    inline bool operator()(const BSQUUID& l, const BSQUUID& r) const { return BSQUUID::keyEqual(l, r); }
};
struct LessFunctor_BSQUUID
{
    inline bool operator()(const BSQUUID& l, const BSQUUID& r) const { return BSQUUID::keyLess(l, r); }
};

typedef BSQBoxed<BSQUUID> Boxed_BSQUUID;
struct DisplayFunctor_BSQUUID
{
    std::wstring operator()(const BSQUUID& u) const { return std::wstring(L"UUID@") + std::wstring(u.sdata, u.sdata + 16); }
};

void* ExtractGeneralRepr_BSQUUID(void* v);
std::wstring DisplayFunction_BSQUUID(void* v);
constexpr MetaData MetaData_BSQUUID = {
    MIRNominalTypeEnum_UUID,
    MIRNominalTypeEnum_Category_UUID,
    DATA_KIND_ALL_FLAG,
    ExtractFlag::StructAllocNoMeta,
    sizeof(Boxed_BSQUUID),
    ObjectLayoutKind::NoRef,
    0,
    nullptr,
    0,
    L"UUID",
    &DisplayFunction_BSQUUID,
    &ExtractGeneralRepr_BSQUUID
};

struct BSQLogicalTime
{
    uint64_t timestamp;

    inline static bool keyEqual(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp == r.timestamp;
    }

    inline static bool keyLess(const BSQLogicalTime& l, const BSQLogicalTime& r)
    {
        return l.timestamp < r.timestamp;
    }
};
struct EqualFunctor_BSQLogicalTime
{
    inline bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyEqual(l, r); }
};
struct LessFunctor_BSQLogicalTime
{
    inline bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyLess(l, r); }
};

typedef BSQBoxed<BSQLogicalTime> Boxed_BSQLogicalTime;
struct DisplayFunctor_BSQLogicalTime
{
    std::wstring operator()(const BSQLogicalTime& et) const 
    { 
        return std::wstring(L"LogicalTime@") + std::to_wstring(et.timestamp); 
    }
};

void* ExtractGeneralRepr_BSQLogicalTime(void* v);
std::wstring DisplayFunction_BSQLogicalTime(void* v);
constexpr MetaData MetaData_BSQLogicalTime = {
    MIRNominalTypeEnum_LogicalTime,
    MIRNominalTypeEnum_Category_LogicalTime,
    DATA_KIND_ALL_FLAG,
    ExtractFlag::StructAllocNoMeta,
    sizeof(Boxed_BSQLogicalTime),
    ObjectLayoutKind::NoRef,
    0,
    nullptr,
    0,
    L"LogicalTime",
    &DisplayFunction_BSQLogicalTime,
    &ExtractGeneralRepr_BSQLogicalTime
};

struct BSQCryptoHash
{
    uint8_t hdata[64];

    inline static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }

    inline static bool keyLess(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) < 0;
    }
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
    std::wstring operator()(const BSQCryptoHash* h) const { return std::wstring(L"CryptoHash@") + std::wstring(h->hdata, h->hdata + 64); }
};
std::wstring DisplayFunction_BSQCryptoHash(void* v);
constexpr MetaData MetaData_BSQCryptoHash = {
    MIRNominalTypeEnum_CryptoHash,
    MIRNominalTypeEnum_Category_CryptoHash,
    DATA_KIND_ALL_FLAG,
    ExtractFlag::Pointer,
    sizeof(BSQCryptoHash),
    ObjectLayoutKind::CollectionNoRef,
    0,
    nullptr,
    1,
    L"CryptoHash",
    &DisplayFunction_BSQCryptoHash,
    &ExtractGeneralRepr_Identity
};

struct BSQEnum
{
public:
    MetaData* mdata;
    MIRNominalTypeEnum nominalType;
    uint32_t value;

    inline static bool keyEqual(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType == r.nominalType) & (l.value == r.value);
    }

    inline static bool keyLess(const BSQEnum& l, const BSQEnum& r)
    {
        return (l.nominalType != r.nominalType) ? (l.nominalType < r.nominalType) : (l.value < r.value);
    }
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
    std::wstring operator()(const BSQEnum& e) const 
    { 
        return std::wstring(L"Enum") + std::wstring(L"::") + std::to_wstring(e.value); 
    }
};

void* ExtractGeneralRepr_BSQEnum(void* v);
std::wstring DisplayFunction_BSQEnum(void* v);
constexpr MetaData MetaData_BSQEnum_Constructor(MIRNominalTypeEnum oftype, const wchar_t* displayname) 
{
    return {
        oftype,
        MIRNominalTypeEnum_Category_Enum,
        DATA_KIND_API_FLAG,
        ExtractFlag::StructAllocNoMeta,
        sizeof(BSQEnum),
        ObjectLayoutKind::NoRef,
        0,
        nullptr,
        0,
        displayname,
        &DisplayFunction_BSQEnum,
        &ExtractGeneralRepr_BSQEnum
    };
}

struct BSQIdKeySimple
{
    MetaData* mdata;
    KeyValue key;
    MIRNominalTypeEnum nominalType;

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

void* ExtractGeneralRepr_BSQIdKeySimple(void* v);
std::wstring DisplayFunction_BSQIdKeySimple(void* v);
constexpr MetaData MetaData_BSQIdKeySimple_Constructor(MIRNominalTypeEnum oftype, const wchar_t* displayname) 
{
    return {
        oftype,
        MIRNominalTypeEnum_Category_IdKeySimple,
        DATA_KIND_API_FLAG,
        ExtractFlag::StructFullSize,
        sizeof(BSQIdKeySimple),
        ObjectLayoutKind::Packed,
        1,
        nullptr,
        0,
        displayname,
        &DisplayFunction_BSQIdKeySimple,
        &ExtractGeneralRepr_BSQIdKeySimple
    };
}

struct BSQIdKeyCompound
{
    MetaData* mdata;
    size_t count;
    MIRNominalTypeEnum nominalType;

    static bool keyEqual(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r)
    {
        if(l.nominalType != r.nominalType)
        {
            return false;
        }
        else
        {
            if (l.count != r.count)
            {
                return false;
            }
            else
            {
                const KeyValue* ldata = (KeyValue*)GC_GET_FIRST_COLLECTION_LOC(&l);
                const KeyValue* rdata = (KeyValue*)GC_GET_FIRST_COLLECTION_LOC(&r);
                std::equal(ldata, ldata + l.count, rdata, rdata + r.count, [](KeyValue v1, KeyValue v2) -> bool {
                    return bsqKeyValueEqual(v1, v2);
                });
            }
        }
    }

    static bool keyLess(const BSQIdKeyCompound& l, const BSQIdKeyCompound& r)
    {
        if(l.nominalType != r.nominalType)
        {
            return l.nominalType < r.nominalType;
        }
        else
        {
            const KeyValue* ldata = (KeyValue*)GC_GET_FIRST_COLLECTION_LOC(&l);
            const KeyValue* rdata = (KeyValue*)GC_GET_FIRST_COLLECTION_LOC(&r);
            auto mmiter = std::mismatch(ldata, ldata + l.count, rdata, rdata + r.count, [](KeyValue v1, KeyValue v2) -> bool {
                return bsqKeyValueLess(v1, v2);
            });

            if(mmiter.first == ldata + l.count)
            {
                return false;
            }
            else
            {
                return bsqKeyValueLess(*(mmiter.first), *(mmiter.second));
            }
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

void* ExtractGeneralRepr_BSQIdKeyCompound(void* v);
std::wstring DisplayFunction_BSQIdKeyCompound(void* v);
constexpr MetaData MetaData_BSQIdKeyCompound_Constructor(MIRNominalTypeEnum oftype, const wchar_t* displayname) 
{
    return {
        oftype,
        MIRNominalTypeEnum_Category_IdKeyCompound,
        DATA_KIND_API_FLAG,
        ExtractFlag::StructFullSizePlus,
        sizeof(BSQIdKeyCompound),
        ObjectLayoutKind::CollectionPacked,
        0,
        nullptr,
        sizeof(KeyValue),
        displayname,
        &DisplayFunction_BSQIdKeyCompound,
        &ExtractGeneralRepr_BSQIdKeyCompound
    };
}
}
