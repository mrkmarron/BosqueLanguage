//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "bsqmetadata.h"
#include "bsqmemory.h"

#include <set>

////
//Value ops

typedef uint8_t BSQBool;
#define BSQTRUE 1
#define BSQFALSE 0

#define MIN_BSQ_INT -9007199254740991
#define MAX_BSQ_INT 9007199254740991

#define INT_OOF_BOUNDS(X) (((X) < MIN_BSQ_INT) | ((X) > MAX_BSQ_INT))

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_TAGGED_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)

#define BSQ_GET_VALUE_BOOL(V) ((BSQBool)(((uintptr_t)(V)) & 0x1))
#define BSQ_GET_VALUE_TAGGED_INT(V) (int64_t)(((int64_t)(V)) >> 0x3)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_TAGGED_INT(I) ((void*)((((uint64_t) I) << 0x3) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) ((BSQBool)(((uintptr_t)(V)) & 0x1))

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(BSQTRUE)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(BSQFALSE)

#define META_DATA_DECLARE_SPECIAL_BUFFER(NAME, TYPE, DSTR) META_DATA_DECLARE_PTR_PACKED(NAME, TYPE, DATA_KIND_CLEAR_FLAG, sizeof(BSQBuffer), 1, coerceUnionToBox_RefValue, DisplayFunctor_BSQByteBuffer::display, DSTR);

////
//Type ops

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

enum class MIRRecordPropertySetsEnum
{
    ps__ = 0,
//%%RECORD_PROPERTY_SETS_ENUM_DECLARE%%
};

constexpr const wchar_t* propertyNames[] = {
    L"Invalid",
//%%PROPERTY_NAMES%%
};

typedef void* NoneValue;
typedef void* KeyValue;
typedef void* Value;

void* coerceUnionToBox_RefValue(void* uv);

struct UnionValue
{
    MetaData* umeta;
    void* udata;
};

struct EqualFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return true; }
    static bool eq(KeyValue v1, KeyValue v2) { return true; }
};
struct LessFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return false; }
    static bool less(KeyValue v1, KeyValue v2) { return false; }
};
struct DisplayFunctor_NoneValue
{
    std::wstring operator()(NoneValue n) const { return L"none"; }
    static std::wstring display(void* v) { return L"none"; }
};
std::wstring DisplayFunction_NoneValue(void* Uv);
constexpr MetaData MetaData_None = {
    MIRNominalTypeEnum_None,
    DATA_KIND_ALL_FLAG,
    0,
    -1,
    -1,
    0,
    nullptr,
    nullptr,
    LessFunctor_NoneValue::less,
    EqualFunctor_NoneValue::eq,
    coerceUnionToBox_RefValue,
    nullptr,
    nullptr,
    nullptr,
    nullptr,
    DisplayFunctor_NoneValue::display,
    false
};

struct EqualFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return l == r; }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(l), BSQ_GET_VALUE_BOOL(r)); }
};
struct LessFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return (!l) & r; }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(l), BSQ_GET_VALUE_BOOL(r)); }
};
struct DisplayFunctor_BSQBool
{
    std::wstring operator()(BSQBool b) const { return b ? L"true" : L"false"; }
    static std::wstring display(void* v) { return DisplayFunctor_BSQBool{}(BSQ_GET_VALUE_BOOL(v)); }
};
void* coerceUnionToBox_BSQBool(void* uv);
META_DATA_DECLARE_NO_PTR_KEY(MetaData_Bool, MIRNominalTypeEnum_Bool, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQBool)), LessFunctor_BSQBool::less, EqualFunctor_BSQBool::eq, coerceUnionToBox_BSQBool, DisplayFunctor_BSQBool::display, L"Bool");

struct EqualFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l == r; }
    static bool eq(KeyValue l, KeyValue r) { return EqualFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(l), BSQ_GET_VALUE_TAGGED_INT(r)); }
};
struct LessFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l < r; }
    static bool less(KeyValue l, KeyValue r) { return LessFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(l), BSQ_GET_VALUE_TAGGED_INT(r)); }
};
struct DisplayFunctor_int64_t
{
    std::wstring operator()(int64_t i) const { return std::to_wstring(i); }
    static std::wstring display(void* v) { return DisplayFunctor_int64_t{}(BSQ_GET_VALUE_TAGGED_INT(v)); }
};
void* coerceUnionToBox_int64_t(void* uv);
META_DATA_DECLARE_NO_PTR_KEY(MetaData_Int, MIRNominalTypeEnum_Int, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(int64_t)), LessFunctor_int64_t::less, EqualFunctor_int64_t::eq, coerceUnionToBox_int64_t, DisplayFunctor_int64_t::display, L"Int");

struct DisplayFunctor_double
{
    std::wstring operator()(double d) const { return std::to_wstring(d); }
    static std::wstring display(void* v) { return DisplayFunctor_double{}(*((double*)v)); }
};
void* coerceUnionToBox_double(void* uv);
META_DATA_DECLARE_NO_PTR(MetaData_Float64, MIRNominalTypeEnum_Float64, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(double)), coerceUnionToBox_double, DisplayFunctor_double::display, L"Float64");

MetaData* getMetaData(void* v);

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);
bool bsqKeyValueLess(KeyValue v1, KeyValue v2);

DATA_KIND_FLAG getDataKindFlag(Value v);

std::wstring diagnostic_format(void* v);

struct DisplayFunctor_BSQRef
{
    std::wstring operator()(void* v) const { return diagnostic_format(v); }
};

struct EqualFunctor_KeyValue
{
    bool operator()(KeyValue l, KeyValue r) const { return bsqKeyValueEqual(l, r); }
};
struct LessFunctor_KeyValue
{
    bool operator()(KeyValue l, KeyValue r) const { return bsqKeyValueLess(l, r); }
};
struct DisplayFunctor_KeyValue
{
    std::wstring operator()(KeyValue k) const { return diagnostic_format(k); }
};

struct DisplayFunctor_Value
{
    std::wstring operator()(Value v) const { return diagnostic_format(v); }
};

enum class BSQBufferFormat {
    Text,
    Bosque,
    Json
};

enum class BSQBufferEncoding {
    UTF8,
    Binary
};

enum class BSQBufferCompression {
    Off,
    Time,
    Space
};

struct BSQByteBuffer
{
    size_t count;
    BSQBufferCompression compression;

    std::wstring display_contents() const
    {
        std::wstring rvals(L"");
        if(this->compression == BSQBufferCompression::Off)
        {
            uint8_t* sdata = GET_COLLECTION_START(this);
            rvals += std::wstring(sdata, sdata + this->count);
        }
        else
        {
            uint8_t* sdata = GET_COLLECTION_START(this);
            for (size_t i = 0; i < this->count; ++i)
            {
                if(i != 0)
                {
                    rvals += L", ";
                }

                rvals += sdata[i];
            }
        }
        return rvals;
    }
};
struct DisplayFunctor_BSQByteBuffer
{
    std::wstring operator()(const BSQByteBuffer* bb) const 
    {
        std::wstring rvals(L"ByteBuffer{");
        rvals += bb->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQByteBuffer{}((BSQByteBuffer*)v);
    }
};
META_DATA_DECLARE_NO_PTR_COLLECTION(MetaData_ByteBuffer, MIRNominalTypeEnum_ByteBuffer, DATA_KIND_CLEAR_FLAG, sizeof(BSQByteBuffer), sizeof(uint8_t), coerceUnionToBox_RefValue, DisplayFunctor_BSQByteBuffer::display, L"ByteBuffer");

struct BSQBuffer
{
    BSQByteBuffer* sdata;
    
    BSQBufferFormat format;
    BSQBufferEncoding encoding;
};
struct DisplayFunctor_BSQBuffer
{
    std::wstring operator()(const BSQBuffer* buff) const 
    {
        std::wstring rvals(GET_TYPE_META_DATA(buff)->displayname);
        rvals += L"{";
        rvals += buff->sdata->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQBuffer{}((BSQBuffer*)v);
    }
};
//Declare metadata for each instantiation

struct BSQBufferOf
{
    BSQByteBuffer* sdata;

    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;
};
struct DisplayFunctor_BSQBufferOf
{
    std::wstring operator()(const BSQBufferOf* buff) const 
    {
        std::wstring rvals(GET_TYPE_META_DATA(buff)->displayname);
        rvals += L"{";
        rvals += buff->sdata->display_contents();
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v)
    {
        return DisplayFunctor_BSQBufferOf{}((BSQBufferOf*)v);
    }
};
//Declare metadata for each instantiation

struct BSQISOTime
{
    uint64_t isotime;
};
struct DisplayFunctor_BSQISOTime
{
    std::wstring operator()(const BSQISOTime& t) const { return std::wstring{L"ISOTime={"} + std::to_wstring(t.isotime) + L"}";}
    static std::wstring display(void* v) { return DisplayFunctor_BSQISOTime{}(*((BSQISOTime*)v)); }
};
void* coerceUnionToBox_BSQISOTime(void* uv);
META_DATA_DECLARE_NO_PTR(MetaData_ISOTime, MIRNominalTypeEnum_ISOTime, DATA_KIND_ALL_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQISOTime)), coerceUnionToBox_BSQISOTime, DisplayFunctor_BSQISOTime::display, L"ISOTime");

struct BSQRegex
{
    const std::wregex* re; //these are all constant to this is a scalar as far as GC is concerned
};
struct DisplayFunctor_BSQRegex
{
    std::wstring operator()(const BSQRegex& r) const { return L"[REGEX]"; }
    static std::wstring display(void* v) { return DisplayFunctor_BSQRegex{}(*((BSQRegex*)v)); }
};
void* coerceUnionToBox_BSQRegex(void* uv);
META_DATA_DECLARE_NO_PTR(MetaData_Regex, MIRNominalTypeEnum_Regex, DATA_KIND_CLEAR_FLAG, BSQ_ALIGN_ALLOC_SIZE(sizeof(BSQRegex)), coerceUnionToBox_BSQRegex, DisplayFunctor_BSQRegex::display, L"Regex");

struct BSQTuple
{
    size_t count;
    DATA_KIND_FLAG flag;

    template <size_t count, DATA_KIND_FLAG flag>
    inline static void createFromSingle(BSQTuple* into, std::initializer_list<Value> values)
    {
        into->count = count;
        into->flag = flag;

        Value* tcurr = (Value*)GET_COLLECTION_START(into);
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <size_t count>
    inline static void createFromSingle<DATA_KIND_UNKNOWN_FLAG>(BSQTuple* into, std::initializer_list<Value> values)
    {
        auto fv = flag;
        for(size_t i = 0; i < values.size(); ++i)
        {
            fv &= getDataKindFlag(values[i]);
        }

        into->count = count;
        into->flag = flag;

        Value* tcurr = (Value*)GET_COLLECTION_START(into);
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <uint16_t idx>
    inline bool hasIndex() const
    {
        return idx < this->count;
    }

    template <uint16_t idx>
    inline Value atFixed() const
    {
        if (idx < this->count)
        {
            return *(((Value*)GET_COLLECTION_START(this)) + idx);
        }
        else
        {
            return BSQ_VALUE_NONE;
        }
    }
};
struct DisplayFunctor_BSQTuple
{
    std::wstring operator()(const BSQTuple& tt) const 
    {
        Value* values = (Value*)GET_COLLECTION_START(&tt);
        std::wstring tvals(L"[");
        for(size_t i = 0; i < tt.count; ++i)
        {
            if(i != 0)
            {
                tvals += L", ";
            }

            tvals += diagnostic_format(values[i]);
        }
        tvals += L"]";

        return tvals;
    }
    static std::wstring display(void* v) 
    { 
        return DisplayFunctor_BSQTuple{}(*((BSQTuple*)v)); 
    }
};
void* coerceUnionToBox_BSQTuple(void* uv);
META_DATA_DECLARE_PTR_PACKED_COLLECTON_DIRECT(MetaData_Tuple, MIRNominalTypeEnum_Tuple, DATA_KIND_UNKNOWN_FLAG, sizeof(BSQTuple), coerceUnionToBox_BSQTuple, DisplayFunctor_BSQTuple::display, L"Tuple");

class BSQDynamicPropertySetEntry
{
public:
    std::vector<MIRPropertyEnum> propertySet;
    std::map<MIRPropertyEnum, BSQDynamicPropertySetEntry*> extensions;

    BSQDynamicPropertySetEntry() : propertySet(), extensions() 
    { 
        ; 
    }

    BSQDynamicPropertySetEntry(std::vector<MIRPropertyEnum>&& properties) : propertySet(move(properties)), extensions() 
    { 
        ; 
    }

    ~BSQDynamicPropertySetEntry()
    {
        for(auto iter = this->extensions.begin(); iter != this->extensions.end(); iter++)
        {
            delete iter->second;
        }
    }
};

struct BSQRecord
{
    size_t count;
    MIRPropertyEnum* properties;
    DATA_KIND_FLAG flag;

    static std::map<MIRRecordPropertySetsEnum, std::vector<MIRPropertyEnum>> knownRecordPropertySets;
    static BSQDynamicPropertySetEntry emptyDynamicPropertySetEntry;

    static BSQDynamicPropertySetEntry* getExtendedProperties(BSQDynamicPropertySetEntry* curr, MIRPropertyEnum ext);

    template <size_t count, DATA_KIND_FLAG flag>
    static BSQRecord createFromSingle(BSQRecord* into, MIRPropertyEnum* properties, std::initializer_list<Value> values)
    {
        into->count = count;
        into->properties = properties;
        into->flag = flag;

        Value* tcurr = (Value*)GET_COLLECTION_START(into);
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <size_t count>
    static BSQRecord createFromSingle<DATA_KIND_UNKNOWN_FLAG>(BSQRecord* into, MIRPropertyEnum* properties, std::initializer_list<Value> values)
    {
        auto fv = flag;
        for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
        {
            fv &= getDataKindFlag(iter->second);
        }

        into->count = count;
        into->properties = properties;
        into->flag = fv;

        Value* tcurr = (Value*)GET_COLLECTION_START(into);
        std::copy(values.begin(), values.end(), tcurr);
    }

    template <size_t maxsize, DATA_KIND_FLAG flag>
    static BSQRecord createFromUpdate(BSQRecord* into, const BSQRecord* src, std::initializer_list<std::pair<MIRPropertyEnum, Value>>&& nvals)
    {
        Value values[maxsize];
        size_t valuespos = 0;

        BSQDynamicPropertySetEntry* pse = &BSQRecord::emptyDynamicPropertySetEntry
        auto fv = flag;

        auto srcdata = (Value*)GET_COLLECTION_START(src);
        auto srcpos = 0;
        auto nvalspos = nvals.begin();
        auto nvalend = nvals.end();

        while(srcpos != src->count || nvalspos != nvalend)
        {
            if(srcpos == src->count || nvalspos->first < src->properties[srcpos])
            {
                values[valuespos] = nvalspos->second;
                pse = BSQRecord::getExtendedProperties(pse, nvalspos->first);

                nvalspos++;
            }
            else if(nvalspos == nvalend || src->properties[srcpos] < nvalspos->first)
            {
                values[valuespos] = srcdata[srcpos];
                pse = BSQRecord::getExtendedProperties(pse, src->properties[srcpos]);

                srcpos++;
            }
            else
            {
                values[valuespos] = nvalspos->second;
                pse = BSQRecord::getExtendedProperties(pse, nvalspos->first);

                nvalspos++;
                srcpos++;
            }

            if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
            {
                fv &= getDataKindFlag(values[valuespos]);
            }
            valuespos++;
        }

        into->count = valuespos;
        into->properties = pse->propertySet.data();
        into->flag = fv;

        Value* tcurr = (Value*)GET_COLLECTION_START(into);
        std::copy(values, values + valuespos, tcurr);
    }

    template <MIRPropertyEnum p>
    inline bool hasProperty() const
    {
        return std::find(this->properties, this->properties + this->count, p) != this->properties + this->count;
    }

    template <MIRPropertyEnum p>
    inline Value atFixed() const
    {
        auto iter = std::find(this->properties, this->properties + this->count, p) != this->properties + this->count;
        return iter != this->properties + this->count ? *((Value*)GET_COLLECTION_START(this) + std::distance(this->properties, iter)) : BSQ_VALUE_NONE;
    }

    bool checkPropertySet(int n, ...) const
    {
        MIRPropertyEnum val;
        std::set<MIRPropertyEnum> props;

        va_list vl;
        va_start(vl, n);
        for (int i = 0; i < n; i++)
        {
            val = va_arg(vl, MIRPropertyEnum);
            props.insert(val);
        }
        va_end(vl);

        for(size_t i = 0; i < this->count; ++i) 
        {
            if(props.find(this->properties[i]) == props.cend()) 
            {
                return false;
            }
        }

        return true;
    }
};
struct DisplayFunctor_BSQRecord
{
    std::wstring operator()(const BSQRecord& rr) const 
    { 
        Value* values = (Value*)GET_COLLECTION_START(&rr);

        std::wstring rvals(L"{");
        for(size_t i = 0; i < rr.count; ++i)
        {
            if(i != 0)
            {
                rvals += L", ";
            }

            rvals += std::wstring{propertyNames[(size_t)rr.properties[i]]} + L"=" + diagnostic_format(values[i]);
        }
        rvals += L"}";

        return rvals;
    }
    static std::wstring display(void* v) 
    { 
        return DisplayFunctor_BSQRecord{}(*((BSQRecord*)v)); 
    }
};
void* coerceUnionToBox_BSQRecord(void* uv);
META_DATA_DECLARE_PTR_PACKED_COLLECTON_DIRECT(MetaData_Record, MIRNominalTypeEnum_Record, DATA_KIND_UNKNOWN_FLAG, sizeof(BSQRecord), coerceUnionToBox_BSQRecord, DisplayFunctor_BSQRecord::display, L"Record");

template<int32_t k>
inline bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
{
    if constexpr (k < 16)
    {
        for(int32_t i = 0; i < k; ++i)
        {
            if(etypes[i] == tt)
            {
                return true;
            }
        }
        return false;
    }
    else
    {
            return BSQObject::checkSubtypeSlow<k>(tt, etypes);
    }
}

template<int32_t k>
bool checkSubtypeSlow(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
{
    return std::binary_search(&etypes[0], &etypes[k], tt); 
}
} // namespace BSQ
