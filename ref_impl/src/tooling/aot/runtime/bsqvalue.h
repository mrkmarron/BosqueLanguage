//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#include <unordered_map>

#pragma once

////
//Value ops

#define MIN_TAGGED -9007199254740991
#define MAX_TAGGED 9007199254740991

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_TAGGED_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x3)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_TAGGED_INT(V) (int64_t)(((int64_t)(V)) >> 0x4)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_TAGGED_INT(I) ((void*)((((uint64_t) I) << 0x3) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(true)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(false)

#define BSQ_VALUE_0 BSQ_IS_VALUE_TAGGED_INT(0)
#define BSQ_VALUE_POS_1 BSQ_IS_VALUE_TAGGED_INT(1)
#define BSQ_VALUE_NEG_1 BSQ_IS_VALUE_TAGGED_INT(-1)

#define HASH_COMBINE(H1, H2) (((527 + H1) * 31) + H2)

////
//Reference counting ops


#define BSQ_NEW_NO_RC(T, ...) (new T(__VA_ARGS__))
#define BSQ_NEW_ADD_SCOPE(SCOPE, T, ...) ((T*)((SCOPE).addAllocRef(BSQ_NEW_NO_RC(T, __VA_ARGS__))))

#define INC_REF_DIRECT(T, V) ((T*) BSQRef::incrementDirect(V))
#define INC_REF_CHECK(T, V) ((T*) BSQRef::incrementChecked(V))

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE
};

enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE
};

constexpr char* propertyNames[] = {
    "Invalid",
//%%PROPERTY_NAMES
};

constexpr const char* nominaltypenames[] = {
    "[INVALID]",
//%%NOMINAL_TYPE_DISPLAY_NAMES
};

//%%CONCEPT_SUBTYPE_RELATION_DECLARE

typedef void* IntValue;
typedef void* KeyValue;
typedef void* Value;

class BSQRef
{
private:
    int64_t count;

public:
    BSQRef() : count(0) { ; }
    BSQRef(int64_t excount) : count(excount) { ; }
    virtual ~BSQRef() { ; }

    virtual void destroy() = 0;

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

    inline static BSQRef* incrementDirect(BSQRef* v)
    {
        v->increment();
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

    inline static void decrementDirect(BSQRef* v)
    {
        v->decrement();
    }

    inline static void decrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->decrement();
        }
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

struct HashFunctor_bool
{
    size_t operator()(bool b) { return (size_t)b; }
};
struct EqualFunctor_bool
{
    bool operator()(bool l, bool r) { return l == r; }
};
struct DisplayFunctor_bool
{
    std::u32string operator()(bool b) { return b ? U"true" : U"false"; }
};

//A big integer class for supporting Bosque -- right now it does not do much
class BSQBigInt : public BSQRef
{
public:
    BSQBigInt(int64_t value) { ; }
    BSQBigInt(const char* bigstr) { ; }

    ~BSQBigInt()
    {
        ;
    }

    virtual void destroy() 
    { 
        ; 
    }

    size_t hash() const
    {
        return 0;
    }

    std::u32string display() const
    {
        return U"[NOT IMPLEMENTED]";
    }

    bool isZero() const
    {
        return false;
    }

    BSQBigInt* negate() const
    {
        return nullptr;
    }

    bool eqI64(int64_t v) const
    {
        return false;
    }

    static bool eq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool neq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool lt(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool lteq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

     static bool gt(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static bool gteq(const BSQBigInt* l, const BSQBigInt* r)
    {
        return false;
    }

    static BSQBigInt* add(const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* sub(const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mult(const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* div(const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }

    static BSQBigInt* mod(const BSQBigInt* l, const BSQBigInt* r)
    {
        return nullptr;
    }
};
struct HashFunctor_IntValue
{
    size_t operator()(IntValue i) { return BSQ_IS_VALUE_TAGGED_INT(i) ? BSQ_GET_VALUE_TAGGED_INT(i) : BSQ_GET_VALUE_PTR(i, BSQBigInt)->hash(); }
};
struct EqualFunctor_IntValue
{
    bool operator()(IntValue l, IntValue r) 
    { 
        if(BSQ_IS_VALUE_TAGGED_INT(l) && BSQ_IS_VALUE_TAGGED_INT(r)) {
            return l == r;
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(l)) {
            return BSQ_GET_VALUE_PTR(r, BSQBigInt)->eqI64(BSQ_GET_VALUE_TAGGED_INT(l));
        }
        else if(BSQ_IS_VALUE_TAGGED_INT(r)) {
            return BSQ_GET_VALUE_PTR(l, BSQBigInt)->eqI64(BSQ_GET_VALUE_TAGGED_INT(r));
        }
        else {
            return BSQBigInt::eq(BSQ_GET_VALUE_PTR(l, BSQBigInt), BSQ_GET_VALUE_PTR(r, BSQBigInt));
        }
    }
};
struct DisplayFunctor_IntValue
{
    std::u32string operator()(IntValue i)
    { 
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;
        return BSQ_IS_VALUE_TAGGED_INT(i) ? conv.from_bytes(std::to_string(BSQ_GET_VALUE_TAGGED_INT(i))) : BSQ_GET_VALUE_PTR(i, BSQBigInt)->display();
    }
};

size_t bsqKeyValueHash(KeyValue v);
bool bsqKeyValueEqual(KeyValue v1, KeyValue v2);

std::u32string diagnostic_format(Value v);

struct HashFunctor_KeyValue
{
    size_t operator()(const KeyValue& k) { return bsqKeyValueHash(k); }
};
struct EqualFunctor_KeyValue
{
    bool operator()(const KeyValue& l, const KeyValue& r) { return bsqKeyValueEqual(l, r); }
};
struct DisplayFunctor_KeyValue
{
    std::u32string operator()(const KeyValue& k) { return diagnostic_format(k); }
};

enum class BSQBufferFormat {
    Fluent,
    JSON,
    Binary
};

enum class BSQBufferEncoding {
    UTF8,
    URI,
    Base64
};

enum class BSQBufferCompression {
    None,
    RLE,
    Time,
    Space
};

class BSQBuffer : public BSQRef
{
public:
    const BSQBufferFormat format;
    const BSQBufferEncoding encoding;
    const BSQBufferCompression compression;

    const std::vector<uint8_t> sdata;
    const MIRNominalTypeEnum oftype;

    BSQBuffer(BSQBufferFormat format, BSQBufferEncoding encoding, BSQBufferCompression compression, std::vector<uint8_t>&& sdata, MIRNominalTypeEnum oftype) : BSQRef(), format(format), encoding(encoding), compression(compression), sdata(move(sdata)), oftype(oftype) { ; }
    
    virtual ~BSQBuffer() = default;
    virtual void destroy() { ; }
};

class BSQISOTime : public BSQRef
{
public:
    const uint64_t isotime;

    BSQISOTime(uint64_t isotime) : BSQRef(), isotime(isotime) { ; }
    virtual ~BSQISOTime() = default;
    virtual void destroy() { ; }
};

class BSQRegex : public BSQRef
{
public:
    const std::u32string re;

    BSQRegex(const std::u32string& re) : BSQRef(), re(re) { ; }
    virtual ~BSQRegex() = default;
};

class BSQTuple : public BSQRef
{
public:
    const std::vector<Value> entries;

    BSQTuple(std::vector<Value>&& entries) : BSQRef(), entries(move(entries)) { ; }
    virtual ~BSQTuple() = default;

    virtual void destroy()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::decrementChecked(this->entries[i]);
        }
    }

    static BSQTuple* _empty;

    Value atFixed(uint16_t idx) const
    {
        return (idx < this->entries.size()) ? this->entries[idx] : BSQ_VALUE_NONE;
    }
};

class BSQRecord : public BSQRef
{
public:
    const std::map<MIRPropertyEnum, Value> entries;

    BSQRecord(std::map<MIRPropertyEnum, Value>&& entries) : BSQRef(), entries(move(entries)) { ; }

    virtual ~BSQRecord() = default;

    virtual void destroy()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::decrementChecked(iter->second);
        }
    }

    static BSQRecord* _empty;

    bool hasProperty(MIRPropertyEnum p) const
    {
        return this->entries.find(p) != this->entries.end();
    }

    Value atFixed(MIRPropertyEnum p) const
    {
        auto iter = this->entries.find(p);
        return iter != this->entries.end() ? iter->second : BSQ_VALUE_NONE;
    }
};

class BSQObject : public BSQRef
{
public:
    MIRNominalTypeEnum ntype;

    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(), ntype(ntype) { ; }
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
