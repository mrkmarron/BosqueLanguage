//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

////
//Value ops

#define MIN_BSQ_INT -9007199254740991
#define MAX_BSQ_INT 9007199254740991

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_TAGGED_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_TAGGED_INT(V) (int64_t)(((int64_t)(V)) >> 0x3)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_TAGGED_INT(I) ((void*)((((uint64_t) I) << 0x3) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(true)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(false)

////
//Reference counting ops

#define BSQ_NEW_NO_RC(T, ...) (new T(__VA_ARGS__))
#define BSQ_NEW_ADD_SCOPE(SCOPE, T, ...) ((T*)((SCOPE).addAllocRefDirect(BSQ_NEW_NO_RC(T, __VA_ARGS__))))

#define INC_REF_DIRECT(T, V) ((T*) BSQRef::incrementDirect(V))
#define INC_REF_CHECK(T, V) ((T*) BSQRef::incrementChecked(V))

////
//Type ops

//Note POD => API
typedef uint32_t DATA_KIND_FLAG;
#define DATA_KIND_CLEAR_FLAG 0x0
#define DATA_KIND_API_FLAG 0x1
#define DATA_KIND_POD_FLAG 0x3
#define DATA_KIND_PARSABLE_FLAG 0x4
#define DATA_KIND_ALL_FLAG (DATA_KIND_API_FLAG | DATA_KIND_POD_FLAG | DATA_KIND_PARSABLE_FLAG)
#define DATA_KIND_UNKNOWN_FLAG 0xFF

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE%%
};

//Category tags to embed in the type enums
#define MIRNominalTypeEnum_Category_BigInt 0x1
#define MIRNominalTypeEnum_Category_String 0x2
#define MIRNominalTypeEnum_Category_SafeString 0x3
#define MIRNominalTypeEnum_Category_StringOf 0x4
#define MIRNominalTypeEnum_Category_UUID 0x5
#define MIRNominalTypeEnum_Category_LogicalTime 0x6
#define MIRNominalTypeEnum_Category_CryptoHash 0x7
#define MIRNominalTypeEnum_Category_Enum 0x8
#define MIRNominalTypeEnum_Category_IdKeySimple 0x9
#define MIRNominalTypeEnum_Category_IdKeyCompound 0xA

#define BUILD_MIR_NOMINAL_TYPE(C, T) (MIRNominalTypeEnum)((T << 8) | T)
#define GET_MIR_TYPE_CATEGORY(T) ((int32_t)T & 0xFF)
#define GET_MIR_TYPE_POSITION(T) ((int32_t)T >> 8)

enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE%%
};

constexpr const char32_t* propertyNames[] = {
    U"Invalid",
//%%PROPERTY_NAMES%%
};

constexpr const char32_t* nominaltypenames[] = {
    U"[INVALID]",
//%%NOMINAL_TYPE_DISPLAY_NAMES%%
};

//%%CONCEPT_SUBTYPE_RELATION_DECLARE%%

constexpr DATA_KIND_FLAG nominalDataKinds[] = {
  DATA_KIND_CLEAR_FLAG,
//%%NOMINAL_TYPE_TO_DATA_KIND%%
};

//%%SPECIAL_NAME_BLOCK_BEGIN%%
#define MIRNominalTypeEnum_None MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Bool MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Int MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_BigInt MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Float64 MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_String MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_UUID MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ByteBuffer MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Tuple MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Record MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Regex MIRNominalTypeEnum::Invalid
//%%SPECIAL_NAME_BLOCK_END%%

typedef void* NoneValue;
typedef void* KeyValue;
typedef void* Value;

class BSQRef
{
private:
    uint64_t count;

public:
    MIRNominalTypeEnum nominalType;

    BSQRef() : count(0), nominalType(MIRNominalTypeEnum::Invalid) { ; }
    BSQRef(MIRNominalTypeEnum nominalType) : count(0), nominalType(nominalType) { ; }
    BSQRef(int64_t excount, MIRNominalTypeEnum nominalType) : count(excount), nominalType(nominalType) { ; }

    virtual ~BSQRef() { ; }
    virtual void destroy() { ; }

    inline void increment()
    {
        this->count++;
    }

    inline void decrement()
    {
        this->count--;

        if(this->count == 0)
        {
            this->destroy();
            BSQ_DELETE(this);    
        }
    }

    inline static void* incrementDirect(void* v)
    {
        ((BSQRef*)v)->increment();
        return v;
    }

    inline static Value incrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->increment();
        }
        return v;
    }

    inline static void decrementDirect(void* v)
    {
        ((BSQRef*)v)->decrement();
    }

    inline static void decrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->decrement();
        }
    }
};

template <typename T, typename DestroyFunctor>
class BSQBoxed : public BSQRef
{
public:
    T bval;

    BSQBoxed(MIRNominalTypeEnum nominalType, const T& bval) : BSQRef(nominalType), bval(bval) { ; }

    virtual ~BSQRef() { ; }

    virtual void destroy() 
    { 
        DestroyFunctor{}(this->bval); 
    }
};

class BSQRefScope
{
private:
    std::vector<BSQRef*> opts;

public:
    BSQRefScope() : opts()
    {
        ;
    }

    ~BSQRefScope()
    {
        for(uint16_t i = 0; i < this->opts.size(); ++i)
        {
           this->opts[i]->decrement();
        }
    }

    inline BSQRef* addAllocRefDirect(BSQRef* ptr)
    {
        ptr->increment();
        this->opts.push_back(ptr);

        return ptr;
    }

    inline Value addAllocRefChecked(Value v)
    {
        if (BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef* ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
            ptr->increment();
            this->opts.push_back(ptr);
        }

        return v;
    }

    inline void callReturnDirect(BSQRef* ptr)
    {
        ptr->increment();
        this->opts.push_back(ptr);
    }

    inline void processReturnChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef* ptr = BSQ_GET_VALUE_PTR(v, BSQRef);
            ptr->increment();
            this->opts.push_back(ptr);
        }
    }
};

struct RCIncFunctor_NoneValue
{
    inline void* operator()(void* n) const { return n; }
};
struct RCDecFunctor_NoneValue
{
    inline void operator()(void* n) const { ; }
};
struct RCReturnFunctor_NoneValue
{
    inline void operator()(BSQEnum& e, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_NoneValue
{
    inline bool operator()(void* l, void* r) const { return true; }
};
struct LessFunctor_NoneValue
{
    inline bool operator()(void* l, void* r) const { return false; }
};
struct DisplayFunctor_NoneValue
{
    std::u32string operator()(void* n) const { return U"none"; }
};

struct RCIncFunctor_bool
{
    inline bool operator()(bool b) const { return b; }
};
struct RCDecFunctor_bool
{
    inline void operator()(bool b) const { ; }
};
struct RCReturnFunctor_bool
{
    inline void operator()(bool b, BSQRefScope& scope) const { ; }
};
struct EqualFunctor_bool
{
    inline bool operator()(bool l, bool r) const { return l == r; }
};
struct LessFunctor_bool
{
    inline bool operator()(bool l, bool r) const { return (!l) & r; }
};
struct DisplayFunctor_bool
{
    std::u32string operator()(bool b) const { return b ? U"true" : U"false"; }
};

struct RCIncFunctor_int64_t
{
    inline int64_t operator()(int64_t i) const { return i; }
};
struct RCDecFunctor_int64_t
{
    inline void operator()(int64_t i) const { ; }
};
struct RCReturnFunctor_int64_t
{
    inline void operator()(int64_t i, BSQRefScope& scope) const { ; }
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
    std::u32string operator()(int64_t i) const 
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(std::to_string(i));  
    }
};

struct RCIncFunctor_double
{
    inline double operator()(double d) const { return d; }
};
struct RCDecFunctor_double
{
    inline void operator()(double d) const { ; }
};
struct RCReturnFunctor_double
{
    inline void operator()(double d, BSQRefScope& scope) const { ; }
};
struct DisplayFunctor_double
{
    std::u32string operator()(double d) const 
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return conv.from_bytes(std::to_string(d));  
    }
};

MIRNominalTypeEnum getNominalTypeOf_KeyValue(KeyValue v);
MIRNominalTypeEnum getNominalTypeOf_Value(Value v);

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);
bool bsqKeyValueLess(KeyValue v1, KeyValue v2);

DATA_KIND_FLAG getDataKindFlag(Value v);

std::u32string diagnostic_format(Value v);

struct RCIncFunctor_KeyValue
{
    inline KeyValue operator()(KeyValue k) const { INC_REF_CHECK(KeyValue, k); }
};
struct RCDecFunctor_KeyValue
{
    inline void operator()(KeyValue k) const { BSQRef::decrementChecked(k); }
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
    std::u32string operator()(KeyValue k) const { return diagnostic_format(k); }
};

class BSQBuffer : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;
    const BSQBufferCompression compression;

    const std::vector<uint8_t> sdata;

    BSQBuffer(BSQBufferFormat format, BSQBufferEncoding encoding, BSQBufferCompression compression, std::vector<uint8_t>&& sdata, MIRNominalTypeEnum oftype) : BSQRef(oftype), format(format), encoding(encoding), compression(compression), sdata(move(sdata)) { ; }
    
    virtual ~BSQBuffer() = default;
    virtual void destroy() { ; }
};

class BSQISOTime : public BSQRef
{
public:
    const uint64_t isotime;

    BSQISOTime(uint64_t isotime) : BSQRef(MIRNominalTypeEnum_ISOTime), isotime(isotime) { ; }
    virtual ~BSQISOTime() = default;
    virtual void destroy() { ; }
};

class BSQRegex : public BSQRef
{
public:
    const std::u32string re;

    BSQRegex(const std::u32string& re) : BSQRef(MIRNominalTypeEnum_Regex), re(re) { ; }
    virtual ~BSQRegex() = default;
};

class BSQTuple
{
public:
    const std::vector<Value> entries;
    const DATA_KIND_FLAG flag;

    BSQTuple(std::vector<Value>&& entries, DATA_KIND_FLAG flag) : entries(move(entries)), flag(flag) { ; }

    template <uint16_t n>
    static BSQTuple* createFromSingle(BSQRefScope& scope, DATA_KIND_FLAG flag, const Value(&values)[n])
    {
        Value val;
        std::vector<Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val);
            entries.push_back(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < entries.size(); ++i)
            {
                flag &= getDataKindFlag(entries[i]);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQTuple, move(entries), flag);
    }

    static BSQTuple* createFromSingleDynamic(BSQRefScope& scope, DATA_KIND_FLAG flag, const std::vector<Value>& values)
    {
        Value val;
        std::vector<Value> entries;

        for (int i = 0; i < values.size(); i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val);
            entries.push_back(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(size_t i = 0; i < entries.size(); ++i)
            {
                flag &= getDataKindFlag(entries[i]);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQTuple, move(entries), flag);
    }

    virtual ~BSQTuple() = default;

    virtual void destroy()
    {
        for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
        {
            BSQRef::decrementChecked(*iter);
        }
    }

    static BSQTuple _empty;

    inline bool hasIndex(uint16_t idx) const
    {
        return idx < this->entries.size();
    }

    inline Value atFixed(uint16_t idx) const
    {
        return (idx < this->entries.size()) ? this->entries[idx] : BSQ_VALUE_NONE;
    }

    static void _push(std::vector<Value>& entries, Value v)
    {
        BSQRef::incrementChecked(v);
        entries.push_back(v);
    }
};

class BSQRecord
{
public:
    const std::map<MIRPropertyEnum, Value> entries;
    const DATA_KIND_FLAG flag;

    BSQRecord(std::map<MIRPropertyEnum, Value>&& entries, DATA_KIND_FLAG flag) : entries(move(entries)), flag(flag) { ; }

    template <uint16_t n>
    static BSQRecord* createFromSingle(BSQRefScope& scope, DATA_KIND_FLAG flag, const std::pair<MIRPropertyEnum, Value>(&values)[n])
    {
        std::pair<MIRPropertyEnum, Value> val;
        std::map<MIRPropertyEnum, Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val.second);
            entries.insert(val);
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
            {
                flag &= getDataKindFlag(iter->second);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQRecord, move(entries), flag);
    }

    template <uint16_t n>
    static BSQRecord* createFromUpdate(BSQRefScope& scope, BSQRecord* src, DATA_KIND_FLAG flag, const std::pair<MIRPropertyEnum, Value>(&values)[n])
    {
        std::pair<MIRPropertyEnum, Value> val;
        std::map<MIRPropertyEnum, Value> entries;

        for (int i = 0; i < n; i++)
        {
            val = values[i];

            BSQRef::incrementChecked(val.second);
            entries.insert(val);
        }

        for(auto iter = src->entries.begin(); iter != src->entries.end(); ++iter) {
            auto pos = entries.lower_bound(iter->first);
            if(pos != src->entries.cend() && pos->first != iter->first)
            {
                BSQRef::incrementChecked(iter->second);
                entries.emplace_hint(pos, *iter);
            }
        }

        if(flag == DATA_KIND_UNKNOWN_FLAG)
        {
            for(auto iter = entries.cbegin(); iter != entries.cend(); ++iter)
            {
                flag &= getDataKindFlag(iter->second);
            }
        }

        return BSQ_NEW_ADD_SCOPE(scope, BSQRecord, move(entries), flag);
    }

    virtual ~BSQRecord() = default;

    virtual void destroy()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::decrementChecked(iter->second);
        }
    }

    static BSQRecord _empty;

    inline bool hasProperty(MIRPropertyEnum p) const
    {
        return this->entries.find(p) != this->entries.end();
    }

    inline Value atFixed(MIRPropertyEnum p) const
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

class BSQObject : public BSQRef
{
public:
    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(ntype) { ; }
    virtual ~BSQObject() = default;

    virtual std::u32string display() const = 0;

    template<int32_t k>
    inline static bool checkSubtype(MIRNominalTypeEnum tt, const MIRNominalTypeEnum(&etypes)[k])
    {
        if(k < 16)
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
} // namespace BSQ
