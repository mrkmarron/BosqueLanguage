//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqint.h"

#include <unordered_map>

#pragma once

////
//Value ops

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0xF) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_INT(V) (int32_t)(((int64_t)(V)) >> 0x32)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_ENCODE_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_ENCODE_VALUE_INT(I) ((void*)((((uint64_t) I) << 0x32) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE BSQ_ENCODE_VALUE_BOOL(true)
#define BSQ_VALUE_FALSE BSQ_ENCODE_VALUE_BOOL(false)

#define BSQ_VALUE_0 BSQInt(0)
#define BSQ_VALUE_POS_1 BSQInt(1)
#define BSQ_VALUE_NEG_1 BSQInt(-1)

////
//Int ops
#define BSQ_BOX_VALUE_BSQINT(E, SCOPE, SC) ((SCOPE).addAllocRefChecked<SC>(BSQBoxedInt::box(E)))
#define BSQ_GET_VALUE_BSQINT(E) (BSQBoxedInt::unbox(E))

#define HASH_COMBINE(H1, H2) (((527 + H1) * 31) + H2)

////
//Reference counting ops

#define INC_REF_DIRECT(T, V) ((T*) BSQRef::incrementDirect(V))
#define INC_REF_NONEABLE(T, V) ((T*) BSQRef::incrementNoneable(V))
#define INC_REF_CHECK(T, V) ((T*) BSQRef::incrementChecked(V))

#define ADD_ALLOC_REF(T, E, SCOPE, SC) ((T*) (SCOPE).addAllocRef<SC>(E))

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
            delete this;    
        }
    }

    inline static BSQRef* incrementDirect(BSQRef* v)
    {
        v->increment();
        return v;
    }

    inline static BSQRef* incrementNoneable(BSQRef* v)
    {
        if(BSQ_IS_VALUE_NONNONE(v))
        {
            v->increment();
        }
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

    inline static void decrementNoneable(BSQRef* v)
    {
        if(BSQ_IS_VALUE_NONNONE(v))
        {
            v->decrement();
        }
    }

    inline static void decrementChecked(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->decrement();
        }
    }

    //%%ALL_VFIELD_ACCESS_DECLS

    //%%ALL_VCALL_DECLS
};

template <uint16_t k>
class BSQRefScope
{
private:
    BSQRef* opts[k];

public:
    BSQRefScope() : opts{nullptr}
    {
        ;
    }

    ~BSQRefScope()
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            if(this->opts[i] != nullptr)
            {
                BSQRef::decrement(this->opts[i]);
            }
        }
    }

    template <uint16_t pos>
    inline BSQRef** getCallerSlot() {
        return this->opts + pos; 
    }

    template <uint16_t pos>
    inline BSQRef* addAllocRef(BSQRef* ptr)
    {
        ptr->increment();
        this->opts[pos] = ptr;

        return ptr;
    }

    template <uint16_t pos>
    inline Value addAllocRefChecked(Value v)
    {
        if (BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            ptr->increment();
            this->opts[pos] = ptr;
        }

        return ptr;
    }

    inline static void callReturnDirect(BSQRef** callerslot, BSQRef* ptr)
    {
        ptr->increment();
        *callerslot = ptr;
    }

    inline static void processReturnNoneable(BSQRef** callerslot, BSQRef* ptr)
    {
        if(BSQ_IS_VALUE_NONNONE(ptr))
        {
            ptr->increment();
            *callerslot = ptr;
        }
    }

    inline static void processReturnChecked(BSQRef** callerslot, Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQ_GET_VALUE_PTR(v, BSQRef)->increment();
            *callerslot = BSQ_GET_VALUE_PTR(v, BSQRef);
        }
    }
};

class BSQBoxedInt : public BSQRef
{
public:
    const BSQInt data;

    BSQBoxedInt(const BSQInt idata) : BSQRef(), data(idata) { ; }
    BSQBoxedInt(const BSQInt idata, int64_t excount) : BSQRef(excount), data(idata) { ; }

    virtual ~BSQBoxedInt() = default;
    virtual void destroy() { ; }
    
    static inline Value box(BSQInt v)
    {
        if(v.isInt())
        {
            return BSQ_ENCODE_VALUE_INT(v.getInt());
        }
        else
        {
            return new BSQBoxedInt(v);
        }
        
    }

    static inline BSQInt unbox(Value v)
    {
        if(BSQ_IS_VALUE_INT(v))
        {
            return BSQInt(BSQ_GET_VALUE_INT(v));
        }
        else
        {
            return BSQ_GET_VALUE_PTR(v, BSQBoxedInt)->data;
        }
    }
};

size_t bsqKeyValueHash(Value v);
bool bsqKeyValueEqual(Value v1, Value v2);

std::u32string diagnostic_format(Value v);

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

    template <uint16_t idx>
    Value atFixed() const
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

    template <MIRPropertyEnum p>
    bool hasProperty() const
    {
        return this->entries.find(p) != this->entries.end();
    }

    template <MIRPropertyEnum p>
    Value atFixed() const
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

//%%VFIELD_DECLS
//%%VMETHOD_DECLS

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

template<typename K, typename KFDecOp, typename V, typename VFDecOp>
class BSQMapEntry : public BSQRef
{
public:
    K key;
    V value;

    BSQMapEntry() : BSQRef() { ; }
    BSQMapEntry(const K& k, const V& v) : BSQRef(), key(k), value(v) { ; }

    BSQMapEntry(const BSQMapEntry& src) : BSQRef(), key(src.key), value(src.value) 
    { 
        ; 
    }

    BSQMapEntry& operator=(const BSQMapEntry& src)
    {
        this->key = src.key;
        this->value = src.value;
        return *this;
    }

    virtual ~BSQMapEntry() = default;

    virtual void destroy() 
    {
        KFDecOp(this->k);
        VFDecOp(this->v);
    }
};

template<typename T, typename FIncOp, typename FDecOp>
class BSQResult : public BSQRef
{
xxxx;
};

template<typename K, typename KFIncOp, typename KFDecOp, typename U, typename UFIncOp, typename UFDecOp>
class BSQTagged : public BSQRef
{
xxxx;
};

class BSQSet : public BSQObject {
public:
    std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
    BSQKeyList* keys;

    BSQSet(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries(), keys(nullptr) { ; }
    BSQSet(MIRNominalTypeEnum ntype, std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual>&& entries, BSQKeyList* keys) : BSQObject(ntype), entries(move(entries)), keys(keys) { ; }

    virtual ~BSQSet()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::checkedDecrement(iter->first);
            BSQRef::checkedDecrement(iter->second);
        }
        BSQRef::checkedDecrementNoneable(keys);
    }

    BSQSet* add(Value key, Value val, BSQKeyList* nkeys)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::checkedIncrementNop(iter->first);
            BSQRef::checkedIncrementNop(iter->second);
            entries.insert(*iter);
        }
        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);
        entries.insert(std::make_pair(key, val));

        BSQRef::checkedIncrementNoneable(nkeys);

        return new BSQSet(this->ntype, move(entries), nkeys);
    }

    BSQSet* destructiveAdd(Value key, Value val, BSQKeyList* nkeys)
    {
        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);
        entries.insert(std::make_pair(key, val));

        BSQRef::checkedDecrementNoneable(this->keys);
        BSQRef::checkedIncrementNoneable(nkeys);
        this->keys = nkeys;

        return this;
    }

    BSQSet* update(Value key, Value val)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(eq(key, iter->first))
            {
                BSQRef::checkedIncrementNop(key);
                BSQRef::checkedIncrementNop(val);
                entries.insert(std::make_pair(key, val));
            }
            else
            {
                BSQRef::checkedIncrementNop(iter->first);
                BSQRef::checkedIncrementNop(iter->second);
                entries.insert(*iter);
            }
        }
        BSQRef::checkedIncrementNoneable(this->keys);

        return new BSQSet(this->ntype, move(entries), this->keys);
    }

    BSQSet* destructiveUpdate(Value key, Value val)
    {
        auto iter = this->entries.find(key);
        auto oldkey = iter->first;
        auto oldval = iter->second;

        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);

        entries.erase(iter);
        entries.emplace(std::make_pair(key, val));

        BSQRef::checkedDecrement(oldkey);
        BSQRef::checkedDecrement(oldval);

        return this;
    }

    BSQSet* clearKey(Value key, BSQKeyList* nkeys)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(!eq(key, iter->first)) 
            {
                BSQRef::checkedIncrementNop(iter->first);
                BSQRef::checkedIncrementNop(iter->second);
                entries.insert(*iter);
            }
        }
        BSQRef::checkedIncrementNoneable(nkeys);

        return new BSQSet(this->ntype, move(entries), nkeys);
    }

    virtual std::u32string display() const
    {
        return std::u32string(U"[SHOULD BE SPECIAL CASED IN DISPLAY]");
    }
};

class BSQMap : public BSQObject {
public:
    std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
    BSQKeyList* keys;

    BSQMap(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries(), keys(nullptr) { ; }
    BSQMap(MIRNominalTypeEnum ntype, std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual>&& entries, BSQKeyList* keys) : BSQObject(ntype), entries(move(entries)), keys(keys) { ; }

    virtual ~BSQMap()
    {
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::checkedDecrement(iter->first);
            BSQRef::checkedDecrement(iter->second);
        }
        BSQRef::checkedDecrementNoneable(keys);
    }

    BSQMap* add(Value key, Value val, BSQKeyList* nkeys)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            BSQRef::checkedIncrementNop(iter->first);
            BSQRef::checkedIncrementNop(iter->second);
            entries.insert(*iter);
        }
        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);
        entries.insert(std::make_pair(key, val));

        BSQRef::checkedIncrementNoneable(nkeys);

        return new BSQMap(this->ntype, move(entries), nkeys);
    }

    BSQMap* destructiveAdd(Value key, Value val, BSQKeyList* nkeys)
    {
        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);
        entries.insert(std::make_pair(key, val));

        BSQRef::checkedDecrementNoneable(this->keys);
        BSQRef::checkedIncrementNoneable(nkeys);
        this->keys = nkeys;

        return this;
    }

    BSQMap* update(Value key, Value val)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(eq(key, iter->first))
            {
                BSQRef::checkedIncrementNop(key);
                BSQRef::checkedIncrementNop(val);
                entries.insert(std::make_pair(key, val));
            }
            else
            {
                BSQRef::checkedIncrementNop(iter->first);
                BSQRef::checkedIncrementNop(iter->second);
                entries.insert(*iter);
            }
        }
        BSQRef::checkedIncrementNoneable(this->keys);

        return new BSQMap(this->ntype, move(entries), this->keys);
    }

    BSQMap* destructiveUpdate(Value key, Value val)
    {
        auto iter = this->entries.find(key);
        auto oldkey = iter->first;
        auto oldval = iter->second;

        BSQRef::checkedIncrementNop(key);
        BSQRef::checkedIncrementNop(val);

        entries.erase(iter);
        entries.emplace(std::make_pair(key, val));

        BSQRef::checkedDecrement(oldkey);
        BSQRef::checkedDecrement(oldval);

        return this;
    }

    BSQMap* clearKey(Value key, BSQKeyList* nkeys)
    {
        BSQIndexableEqual eq;
        std::unordered_map<Value, Value, BSQIndexableHash, BSQIndexableEqual> entries;
        for(auto iter = this->entries.begin(); iter != this->entries.end(); ++iter)
        {
            if(!eq(key, iter->first)) 
            {
                BSQRef::checkedIncrementNop(iter->first);
                BSQRef::checkedIncrementNop(iter->second);
                entries.insert(*iter);
            }
        }
        BSQRef::checkedIncrementNoneable(nkeys);

        return new BSQMap(this->ntype, move(entries), nkeys);
    }

    virtual std::u32string display() const
    {
        return std::u32string(U"[SHOULD BE SPECIAL CASED IN DISPLAY]");
    }
};


} // namespace BSQ
