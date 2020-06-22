//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "common.h"

#include "bsqmetadata.h"
#include "bsqmemory.h"

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

////
//Type ops

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

constexpr const wchar_t* propertyNames[] = {
    L"Invalid",
//%%PROPERTY_NAMES%%
};

typedef void* NoneValue;
typedef void* KeyValue;
typedef void* Value;

template <typename T>
struct BSQBoxedDirect
{
    T bval;
};

template <typename T>
struct BSQBoxedWithMeta
{
    MetaData* mdata;
    T bval;
};

struct EqualFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return true; }
};
struct LessFunctor_NoneValue
{
    inline bool operator()(NoneValue l, NoneValue r) const { return false; }
};
struct DisplayFunctor_NoneValue
{
    std::wstring operator()(NoneValue n) const { return L"none"; }
};

struct EqualFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return l == r; }
};
struct LessFunctor_BSQBool
{
    inline bool operator()(BSQBool l, BSQBool r) const { return (!l) & r; }
};
struct DisplayFunctor_BSQBool
{
    std::wstring operator()(BSQBool b) const { return b ? L"true" : L"false"; }
};

struct EqualFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l == r; }
};
struct LessFunctor_int64_t
{
    inline bool operator()(int64_t l, int64_t r) const { return l < r; }
};
struct DisplayFunctor_int64_t
{
    std::wstring operator()(int64_t i) const { return std::to_wstring(i); }
};

struct DisplayFunctor_double
{
    std::wstring operator()(double d) const { return std::to_wstring(d); }
};
typedef BSQBoxedWithMeta<double> Boxed_double;

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
    Char,
    Bosque,
    EBosque,
    Json
};

enum class BSQBufferEncoding {
    UTF8,
    URI,
    Base64,
    Binary
};

enum class BSQBufferCompression {
    Off,
    RLE,
    Time,
    Space
};

struct BSQByteBuffer
{
    MetaData* mdata;
    BSQBufferCompression compression;
    //std::vector<uint8_t> sdata;

    std::string display_contents() const
    {
        std::string rvals("");
        if(this->compression == BSQBufferCompression::Off)
        {
            rvals += std::string((char*)this->sdata.data(), (char*)this->sdata.data() + this->sdata.size());
        }
        else
        {
            for (size_t i = 0; i < this->sdata.size(); ++i)
            {
                if(i != 0)
                {
                    rvals += ", ";
                }

                rvals += this->sdata[i];
            }
        }
        return rvals;
    }
};
struct DisplayFunctor_BSQByteBuffer
{
    std::string operator()(const BSQByteBuffer* bb) const 
    {
        std::string rvals("ByteBuffer{");
        rvals += bb->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQBuffer : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;

    BSQByteBuffer* sdata;

    BSQBuffer(BSQBufferFormat format, BSQBufferEncoding encoding, BSQByteBuffer* sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), sdata(sdata) { ; }
    
    virtual ~BSQBuffer() = default;
    
    virtual void destroy() 
    { 
        BSQRef::decrementDirect(this->sdata);
    }
};
struct DisplayFunctor_BSQBuffer
{
    std::string operator()(const BSQBuffer* buff) const 
    {
        std::string rvals(nominaltypenames[GET_MIR_TYPE_POSITION(buff->nominalType)]);
        rvals += "{";
        rvals += buff->sdata->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQBufferOf : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;

    BSQByteBuffer* sdata;

    BSQBufferOf(BSQBufferFormat format, BSQBufferEncoding encoding, BSQByteBuffer* sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), sdata(sdata) { ; }
    
    virtual ~BSQBufferOf() = default;
    
    virtual void destroy() 
    { 
        BSQRef::decrementDirect(this->sdata);
    }
};
struct DisplayFunctor_BSQBufferOf
{
    std::string operator()(const BSQBufferOf* buff) const 
    {
        std::string rvals(nominaltypenames[GET_MIR_TYPE_POSITION(buff->nominalType)]);
        rvals += "{";
        rvals += buff->sdata->display_contents();
        rvals += "}";

        return rvals;
    }
};

class BSQISOTime
{
public:
    uint64_t isotime;

    BSQISOTime() { ; }
    BSQISOTime(uint64_t isotime) : isotime(isotime) { ; }

    BSQISOTime(const BSQISOTime& src) = default;
    BSQISOTime(BSQISOTime&& src) = default;

    BSQISOTime& operator=(const BSQISOTime& src) = default;
    BSQISOTime& operator=(BSQISOTime&& src) = default;
};
struct RCIncFunctor_BSQISOTime
{
    inline BSQISOTime operator()(BSQISOTime t) const { return t; }
};
struct RCDecFunctor_BSQISOTime
{
    inline void operator()(BSQISOTime t) const { ; }
};
struct RCReturnFunctor_BSQISOTime
{
    inline void operator()(BSQISOTime& t, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_BSQISOTime
{
    std::string operator()(const BSQISOTime& t) const 
    { 
        return std::string{"ISOTime={"} + std::to_string(t.isotime) + "}";
    }
};
typedef BSQBoxed<BSQISOTime, RCDecFunctor_BSQISOTime> Boxed_BSQISOTime;

class BSQRegex
{
public:
    const std::regex* re;

    BSQRegex() { ; }
    BSQRegex(std::regex* re) : re(re) { ; }

    BSQRegex(const BSQRegex& src) = default;
    BSQRegex(BSQRegex&& src) = default;

    BSQRegex& operator=(const BSQRegex& src) = default;
    BSQRegex& operator=(BSQRegex&& src) = default;
};
struct RCIncFunctor_BSQRegex
{
    inline BSQRegex operator()(BSQRegex re) const { return re; }
};
struct RCDecFunctor_BSQRegex
{
    inline void operator()(BSQRegex re) const { ; }
};
struct RCReturnFunctor_BSQRegex
{
    inline void operator()(BSQRegex& re, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_BSQRegex
{
    std::string operator()(const BSQRegex& r) const 
    { 
        return std::string{"[REGEX]"};
    }
};
typedef BSQBoxed<BSQRegex, RCDecFunctor_BSQRegex> Boxed_BSQRegex;

class BSQTuple : public BSQRef
{
public:
    std::vector<Value> entries;
    DATA_KIND_FLAG flag;

    BSQTuple() : BSQRef(MIRNominalTypeEnum_Tuple) { ; }
    BSQTuple(std::vector<Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Tuple), entries(move(entries)), flag(flag) { ; }

    BSQTuple(const BSQTuple& src) : BSQRef(MIRNominalTypeEnum_Tuple), entries(src.entries), flag(src.flag) { ; }
    BSQTuple(BSQTuple&& src) : BSQRef(MIRNominalTypeEnum_Tuple), entries(move(src.entries)), flag(src.flag) { ; }

    virtual ~BSQTuple() = default;
    
    virtual void destroy() 
    { 
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::decrementChecked(this->entries[i]);
        }
    }

    BSQTuple& operator=(const BSQTuple& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = src.entries;
        this->flag = src.flag;
        return *this;
    }

    BSQTuple& operator=(BSQTuple&& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = std::move(src.entries);
        this->flag = src.flag;
        return *this;
    }

    template <DATA_KIND_FLAG flag>
    inline static BSQTuple createFromSingle(std::vector<Value>&& values)
    {
        auto fv = flag;
        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < values.size(); ++i)
            {
                fv &= getDataKindFlag(values[i]);
            }
        }

        return BSQTuple(move(values), fv);
    }

    static BSQTuple _empty;

    template <uint16_t idx>
    inline bool hasIndex() const
    {
        return idx < this->entries.size();
    }

    template <uint16_t idx>
    inline Value atFixed() const
    {
        if (idx < this->entries.size())
        {
            return this->entries[idx];
        }
        else
        {
            return BSQ_VALUE_NONE;
        }
    }
};
struct RCIncFunctor_BSQTuple
{
    inline BSQTuple operator()(BSQTuple tt) const 
    { 
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            BSQRef::incrementChecked(tt.entries[i]);
        }
        return tt;
    }
};
struct RCDecFunctor_BSQTuple
{
    inline void operator()(BSQTuple tt) const 
    { 
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            BSQRef::decrementChecked(tt.entries[i]);
        }
    }
};
struct RCReturnFunctor_BSQTuple
{
    inline void operator()(BSQTuple& tt, BSQRefScope& scope) const 
    {
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            scope.processReturnChecked(tt.entries[i]);
        }
    }
};
struct DisplayFunctor_BSQTuple
{
    std::string operator()(const BSQTuple& tt) const 
    { 
        std::string tvals("[");
        for(size_t i = 0; i < tt.entries.size(); ++i)
        {
            if(i != 0)
            {
                tvals += ", ";
            }

            tvals += diagnostic_format(tt.entries[i]);
        }
        tvals += "]";

        return tvals;
    }
};

class BSQRecord : public BSQRef
{
public:
    std::map<MIRPropertyEnum, Value> entries;
    DATA_KIND_FLAG flag;

    BSQRecord() : BSQRef(MIRNominalTypeEnum_Record) { ; }
    BSQRecord(std::map<MIRPropertyEnum, Value>&& entries, DATA_KIND_FLAG flag) : BSQRef(MIRNominalTypeEnum_Record), entries(move(entries)), flag(flag) { ; }

    BSQRecord(const BSQRecord& src) : BSQRef(MIRNominalTypeEnum_Record), entries(src.entries), flag(src.flag) { ; }
    BSQRecord(BSQRecord&& src) : BSQRef(MIRNominalTypeEnum_Record), entries(move(src.entries)), flag(src.flag) { ; }

    virtual ~BSQRecord() = default;
    
    virtual void destroy() 
    { 
        for(auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter)
        {
            BSQRef::decrementChecked(iter->second);
        }
    }

    BSQRecord& operator=(const BSQRecord& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = src.entries;
        this->flag = src.flag;
        return *this;
    }

    BSQRecord& operator=(BSQRecord&& src)
    {
        if(this == &src)
        {
            return *this;
        }

        //always same nominal type by construction
        this->entries = std::move(src.entries);
        this->flag = src.flag;
        return *this;
    }

    template <DATA_KIND_FLAG flag>
    static BSQRecord createFromSingle(std::map<MIRPropertyEnum, Value>&& values)
    {
        auto fv = flag;
        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
            {
                fv &= getDataKindFlag(iter->second);
            }
        }

        return BSQRecord(move(values), fv);
    }

    template <DATA_KIND_FLAG flag>
    static BSQRecord createFromUpdate(const BSQRecord* src, std::map<MIRPropertyEnum, Value>&& values)
    {
        auto fv = flag;

        for(auto iter = src->entries.begin(); iter != src->entries.end(); ++iter) {
            auto pos = values.lower_bound(iter->first);
            if(pos == values.cend() || pos->first != iter->first)
            {
                values.emplace_hint(pos, *iter);
            }
        }

        if constexpr (flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = values.cbegin(); iter != values.cend(); ++iter)
            {
                fv &= getDataKindFlag(iter->second);
            }
        }

        return BSQRecord(move(values), fv);
    }

    static BSQRecord _empty;

    template <MIRPropertyEnum p>
    inline bool hasProperty() const
    {
        return this->entries.find(p) != this->entries.end();
    }

    template <MIRPropertyEnum p>
    inline Value atFixed() const
    {
        auto iter = this->entries.find(p);
        return iter != this->entries.end() ? iter->second : BSQ_VALUE_NONE;
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

        for(auto iter = this->entries.cbegin(); iter != this->entries.cend(); ++iter) {
            if(props.find(iter->first) == props.cend()) {
                return false;
            }
        }

        return true;
    }
};
struct RCIncFunctor_BSQRecord
{
    inline BSQRecord operator()(BSQRecord rr) const 
    { 
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
           BSQRef::incrementChecked(iter->second);
        }
        return rr;
    }
};
struct RCDecFunctor_BSQRecord
{
    inline void operator()(BSQRecord rr) const 
    { 
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
           BSQRef::decrementChecked(iter->second);
        }
    }
};
struct RCReturnFunctor_BSQRecord
{
    inline void operator()(BSQRecord& rr, BSQRefScope& scope) const 
    {
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
            scope.processReturnChecked(iter->second);
        } 
    }
};
struct DisplayFunctor_BSQRecord
{
    std::string operator()(const BSQRecord& rr) const 
    { 
        std::string rvals("{");
        bool first = true;
        for(auto iter = rr.entries.cbegin(); iter != rr.entries.cend(); ++iter)
        {
            if(!first)
            {
                rvals += ", ";
            }
            first = false;

            rvals += std::string{propertyNames[(int32_t)iter->first]} + "=" + diagnostic_format(iter->second);
        }
        rvals += "}";

        return rvals;
    }
};

class BSQObject : public BSQRef
{
public:
    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(ntype) { ; }
    virtual ~BSQObject() = default;

    virtual std::string display() const = 0;

    template<int32_t k>
    inline static bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
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
    static bool checkSubtypeSlow(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
    {
        return std::binary_search(&etypes[0], &etypes[k], tt); 
    }
};

template <typename T, typename DestroyFunctor>
class BSQBoxedObject : public BSQObject
{
public:
    T bval;

    BSQBoxedObject(MIRNominalTypeEnum nominalType, const T& bval) : BSQObject(nominalType), bval(bval) { ; }
    virtual ~BSQBoxedObject() { ; }

    virtual void destroy() 
    { 
        DestroyFunctor{}(this->bval); 
    }
};
} // namespace BSQ
