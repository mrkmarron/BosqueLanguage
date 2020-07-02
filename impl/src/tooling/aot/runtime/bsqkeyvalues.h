//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"
#include "bsqvalue.h"

#define META_DATA_DECLARE_SPECIAL_TYPED_STRING(NAME, TYPE, CUNION, DISPLAY, DSTR) META_DATA_DECLARE_PTR_PACKED_KEY(NAME, TYPE, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQString)), 1, LessFunctor_BSQString::less, EqualFunctor_BSQString::eq, CUNION, DISPLAY, DSTR)

namespace BSQ
{
struct BigIntFullRepr
{

};

struct BSQBigInt
{
    BigIntFullRepr* bigint; //right now this should always be null and ignored
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
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQBigInt{}(*((BSQBigInt*)l), *((BSQBigInt*)r)); }
};
struct LessFunctor_BSQBigInt
{
    inline bool operator()(const BSQBigInt& l, const BSQBigInt& r) const { return BSQBigInt::lt(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQBigInt{}(*((BSQBigInt*)l), *((BSQBigInt*)r)); }
};
struct DisplayFunctor_BSQBigInt
{
    std::wstring operator()(BSQBigInt i) const { return i.display(); }
    static std::wstring display(void* v) { return DisplayFunctor_BSQBigInt{}(*((BSQBigInt*)v)); }
};
void* coerceUnionToBox_BSQBigInt(void* uv);
META_DATA_DECLARE_PTR_PACKED_KEY(MetaData_BigInt, MIRNominalTypeEnum_BigInt, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQBigInt)), 1, LessFunctor_BSQBigInt::less, EqualFunctor_BSQBigInt::eq, coerceUnionToBox_BSQBigInt, DisplayFunctor_BSQBigInt::display, L"BigInt");

struct BSQStringInlineContents
{
    wchar_t data[4];

    static bool keyEqual(const BSQStringInlineContents& l, const BSQStringInlineContents& r)
    {
        if(l.data[3] != r.data[3])
        {
            return false;
        }
        else
        {
            std::equal(l.data, l.data + l.data[3], r.data, r.data + r.data[3]);
        }
    }

    static bool keyLess(const BSQStringInlineContents& l, const BSQStringInlineContents& r)
    {
        if(l.data[3] != r.data[3])
        {
            return l.data[3] < r.data[3];
        }
        else
        {
            auto mmiter = std::mismatch(l.data, l.data + l.data[3], r.data, r.data + r.data[3]);

            if(mmiter.first == l.data + 3)
            {
                return false;
            }
            else
            {
                return *(mmiter.first) < *(mmiter.second);
            }
        }
    }

    static std::wstring display(const BSQStringInlineContents& v)
    {
        return std::wstring(v.data, v.data + v.data[3]);
    }
};
struct BSQStringFlatContents
{
    size_t count;

    static bool keyEqual(const BSQStringFlatContents* l, const BSQStringFlatContents* r)
    {
        if(l->count != r->count)
        {
            return false;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GET_COLLECTION_START(l);
            const wchar_t* rdata = (wchar_t*)GET_COLLECTION_START(r);
            std::equal(ldata, ldata + l->count, rdata, rdata + r->count);
        }
    }

    static bool keyLess(const BSQStringFlatContents* l, const BSQStringFlatContents* r)
    {
        if(l->count != r->count)
        {
            return l->count < r->count;
        }
        else
        {
            const wchar_t* ldata = (wchar_t*)GET_COLLECTION_START(l);
            const wchar_t* rdata = (wchar_t*)GET_COLLECTION_START(r);
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

    static std::wstring display(const BSQStringFlatContents* v)
    {
        const wchar_t* data = (wchar_t*)GET_COLLECTION_START(v); 
        return std::wstring(data, data + v->count);
    }
};
META_DATA_DECLARE_NO_PTR_COLLECTION(MetaData_StringFlatContents, MIRNominalTypeEnum::Invalid, DATA_KIND_CLEAR_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQStringFlatContents)), sizeof(wchar_t), nullptr, nullptr, L"[StringFlatContents]");
//
//TODO: in the future we want other contents types so we can do substring and string append fast -- like JavaScript
//

struct BSQString
{
    union
    {
        void* u_sdata; //pointer to contents
        BSQStringInlineContents u_inline;
    };

    inline static void initializeSmall(size_t count, wchar_t* chars, BSQString* into)
    {
        into->u_sdata = nullptr;
        GC_MEM_COPY(into->u_inline.data, chars, count);
        into->u_inline.data[4] = (wchar_t)count;
    }

    static void initializeLargeFlat(size_t count, wchar_t* chars, BSQString* into)
    {
        wchar_t* contents = nullptr;
        into->u_sdata = Allocator::GlobalAllocator.collectionNew<BSQStringFlatContents, wchar_t>(META_DATA_LOAD_DECL(MetaData_StringFlatContents), count, &contents, count);
        GC_MEM_COPY(contents, chars, count);
    }

    inline static bool keyEqual(const BSQString& l, const BSQString& r)
    {
        if(l.u_sdata == nullptr)
        {
            return r.u_sdata == nullptr; 
        }
        else if(!BSQ_IS_VALUE_PTR(l.u_sdata))
        {
            if(BSQ_IS_VALUE_PTR(r.u_sdata))
            {
                return false;
            }
            else
            {
                return BSQStringInlineContents::keyEqual(l.u_inline, r.u_inline);
            }
        }
        else
        {
            if(BSQ_IS_VALUE_PTR(r.u_sdata))
            {
                return false;
            }
            else
            {
                return BSQStringFlatContents::keyEqual((BSQStringFlatContents*)l.u_sdata, (BSQStringFlatContents*)r.u_sdata);
            }
        }
    }

    inline static bool keyLess(const BSQString& l, const BSQString& r)
    {
        if(l.u_sdata == nullptr)
        {
            return r.u_sdata != nullptr; //empty string is less than everything 
        }
        else if(!BSQ_IS_VALUE_PTR(l.u_sdata))
        {
            if(BSQ_IS_VALUE_PTR(r.u_sdata))
            {
                return true; //always shorter then
            }
            else
            {
                return BSQStringInlineContents::keyLess(l.u_inline, r.u_inline);
            }
        }
        else
        {
            if(!BSQ_IS_VALUE_PTR(r.u_sdata))
            {
                return false; //always longer
            }
            else
            {
                return BSQStringFlatContents::keyEqual((BSQStringFlatContents*)l.u_sdata, (BSQStringFlatContents*)r.u_sdata);
            }
        }
    }

    static std::wstring display(const BSQString& v)
    {
        if(BSQ_IS_VALUE_TAGGED_INT(v.u_sdata))
        {
            return BSQStringInlineContents::display(v.u_inline);
        }
        else
        {
            return BSQStringFlatContents::display((BSQStringFlatContents*)v.u_sdata);
        }
    }
};
constexpr BSQString EmptyString = {nullptr};

struct EqualFunctor_BSQString
{
    inline bool operator()(const BSQString& l, const BSQString& r) const { return BSQString::keyEqual(l, r); }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQString{}(*((BSQString*)l), *((BSQString*)r)); }
};
struct LessFunctor_BSQString
{
    inline bool operator()(const BSQString& l, const BSQString& r) const { return BSQString::keyLess(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQString{}(*((BSQString*)l), *((BSQString*)r)); }
};
struct DisplayFunctor_BSQString
{
    std::wstring operator()(const BSQString& s) const { return std::wstring(L"\"") +BSQString::display(s) + std::wstring(L"\""); }
    static std::wstring display(void* v) { return DisplayFunctor_BSQString{}(*((BSQString*)v)); }
};
void* coerceUnionToBox_BSQString(void* uv);
META_DATA_DECLARE_PTR_PACKED_KEY(MetaData_String, MIRNominalTypeEnum_String, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQString)), 1, LessFunctor_BSQString::less, EqualFunctor_BSQString::eq, coerceUnionToBox_BSQString, DisplayFunctor_BSQString::display, L"String");

//
//SafeString and StringOf only differ from string in their metadata so we just define that and use the same string representation
//-- See META_DATA_DECLARE_SPECIAL_TYPED_STRING
//

struct DisplayFunctor_BSQSafeString
{
    std::wstring operator()(const BSQString& s) const { return std::wstring(L"'") + BSQString::display(s) + std::wstring(L"'"); }
    static std::wstring display(void* v) 
    { 
        const MetaData* mdata = GET_TYPE_META_DATA(v);
        return std::wstring(mdata->displayname) + DisplayFunctor_BSQSafeString{}(*((BSQString*)v)); 
    }
};
void* coerceUnionToBox_BSQSafeString(void* uv);

struct DisplayFunctor_BSQStringOf
{
    std::wstring operator()(const BSQString& s) const { return std::wstring(L"'") + BSQString::display(s) + std::wstring(L"'"); }
    static std::wstring display(void* v) 
    { 
        const MetaData* mdata = GET_TYPE_META_DATA(v);
        return std::wstring(mdata->displayname) + DisplayFunctor_BSQStringOf{}(*((BSQString*)v)); 
    }
};
void* coerceUnionToBox_BSQStringOf(void* uv);

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
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQUUID{}(*((BSQUUID*)l), *((BSQUUID*)r)); }
};
struct LessFunctor_BSQUUID
{
    inline bool operator()(const BSQUUID& l, const BSQUUID& r) const { return BSQUUID::keyLess(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQUUID{}(*((BSQUUID*)l), *((BSQUUID*)r)); }
};
struct DisplayFunctor_BSQUUID
{
    std::wstring operator()(const BSQUUID& u) const { return std::wstring(L"UUID@") + std::wstring(u.sdata, u.sdata + 16); }
    static std::wstring display(void* v) { return DisplayFunctor_BSQUUID{}(*((BSQUUID*)v)); }
};
void* coerceUnionToBox_BSQUUID(void* uv);
META_DATA_DECLARE_NO_PTR_KEY(MetaData_UUID, MIRNominalTypeEnum_UUID, DATA_KIND_ALL_FLAG, sizeof(BSQUUID), LessFunctor_BSQUUID::less, EqualFunctor_BSQUUID::eq, coerceUnionToBox_BSQUUID, DisplayFunctor_BSQUUID::display, L"UUID");

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
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQLogicalTime{}(*((BSQLogicalTime*)l), *((BSQLogicalTime*)r)); }
};
struct LessFunctor_BSQLogicalTime
{
    inline bool operator()(const BSQLogicalTime& l, const BSQLogicalTime& r) const { return BSQLogicalTime::keyLess(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQLogicalTime{}(*((BSQLogicalTime*)l), *((BSQLogicalTime*)r)); }
};
struct DisplayFunctor_BSQLogicalTime
{
    std::wstring operator()(const BSQLogicalTime& et) const { return std::wstring(L"LogicalTime@") + std::to_wstring(et.timestamp); }
    static std::wstring display(void* v) { return DisplayFunctor_BSQLogicalTime{}(*((BSQLogicalTime*)v)); }
};
void* coerceUnionToBox_BSQLogicalTime(void* uv);
META_DATA_DECLARE_NO_PTR_KEY(MetaData_LogicalTime, MIRNominalTypeEnum_LogicalTime, DATA_KIND_ALL_FLAG, sizeof(BSQLogicalTime), LessFunctor_BSQLogicalTime::less, EqualFunctor_BSQLogicalTime::eq, coerceUnionToBox_BSQLogicalTime, DisplayFunctor_BSQLogicalTime::display, L"LogicalTime");

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
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQCryptoHash{}((BSQCryptoHash*)l, (BSQCryptoHash*)r); }
};
struct LessFunctor_BSQCryptoHash
{
    inline bool operator()(const BSQCryptoHash* l, const BSQCryptoHash* r) const { return BSQCryptoHash::keyLess(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQCryptoHash{}((BSQCryptoHash*)l, (BSQCryptoHash*)r); }
};
struct DisplayFunctor_BSQCryptoHash
{
    std::wstring operator()(const BSQCryptoHash* h) const { return std::wstring(L"CryptoHash@") + std::wstring(h->hdata, h->hdata + 64); }
    static std::wstring display(void* v) { return DisplayFunctor_BSQCryptoHash{}((BSQCryptoHash*)v); }
};
META_DATA_DECLARE_NO_PTR_KEY(MetaData_CryptoHash, MIRNominalTypeEnum_CryptoHash, DATA_KIND_ALL_FLAG, sizeof(BSQCryptoHash), LessFunctor_BSQCryptoHash::less, EqualFunctor_BSQCryptoHash::eq, coerceUnionToBox_RefValue, DisplayFunctor_BSQCryptoHash::display, L"CryptoHash");

struct BSQEnum
{
public:
    uint32_t value;

    inline static bool keyEqual(const BSQEnum& l, const BSQEnum& r)
    {
        return l.value == r.value;
    }

    inline static bool keyLess(const BSQEnum& l, const BSQEnum& r)
    {
        return l.value < r.value;
    }
};
struct EqualFunctor_BSQEnum
{
    inline bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyEqual(l, r); }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQEnum{}(*((BSQEnum*)l), *((BSQEnum*)r)); }
};
struct LessFunctor_BSQEnum
{
    inline bool operator()(const BSQEnum& l, const BSQEnum& r) const { return BSQEnum::keyLess(l, r); }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQEnum{}(*((BSQEnum*)l), *((BSQEnum*)r)); }
};
struct DisplayFunctor_BSQEnum
{
    std::wstring operator()(const BSQEnum& e) const { return std::to_wstring(e.value); }
    static std::wstring display(void* v) 
    { 
        const MetaData* mdata = GET_TYPE_META_DATA(v);
        return std::wstring(mdata->displayname) + std::wstring(L"::") + DisplayFunctor_BSQEnum{}(*((BSQEnum*)v)); 
    }
};
void* coerceUnionToBox_BSQEnum(void* uv);

//
//Auto generate the code for each simple and compound key type since they need to specialize per the types of keys
//
}
