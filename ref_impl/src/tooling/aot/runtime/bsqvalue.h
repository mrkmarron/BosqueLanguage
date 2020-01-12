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

size_t bsqKeyValueHash(Value v);
bool bsqKeyValueEqual(Value v1, Value v2);

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

class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(), sdata(str) { ; }
    BSQString(const char* str, int64_t excount) : BSQRef(excount), sdata(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>().from_bytes(str)) { ; }

    virtual ~BSQString() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQString* str)
    {
        return std::hash<std::u32string>{}(str->sdata);
    }
    
    static bool keyEqual(const BSQString* l, const BSQString* r)
    {
        return l->sdata == r->sdata;
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

    static size_t hash(const BSQStringOf* str)
    {
        return HASH_COMBINE((size_t)str->oftype, std::hash<std::u32string>{}(str->sdata));
    }

    static bool keyEqual(const BSQStringOf* l, const BSQStringOf* r)
    {
        return l->oftype == r->oftype && l->sdata == r->sdata;
    }
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

class BSQGUID : public BSQRef
{
public:
    const uint8_t sdata[16];

    BSQGUID(const uint8_t sdata[16]) : BSQRef(), sdata() { memcpy_s((void*)this->sdata, 16, sdata, 16); }

    virtual ~BSQGUID() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQGUID* guid)
    {
        auto sdb = (uint64_t*)guid->sdata;
        return HASH_COMBINE(sdb[0], sdb[1]);
    }

    static bool keyEqual(const BSQGUID* l, const BSQGUID* r)
    {
        return memcmp(l->sdata, r->sdata, 16) == 0;
    }
};

class BSQDataHash : public BSQRef
{
public:
    const uint64_t hdata;

    BSQDataHash(uint64_t hdata) : BSQRef(), hdata(hdata) { ; }
    virtual ~BSQDataHash() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQDataHash* h)
    {
        return (size_t)h->hdata;
    }

    static bool keyEqual(const BSQDataHash* l, const BSQDataHash* r)
    {
        l->hdata == r->hdata;
    }
};

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t sdata[64]) : BSQRef(), hdata() { memcpy_s((void*)this->hdata, 64, hdata, 64); }
    virtual ~BSQCryptoHash() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQCryptoHash* h)
    {
        auto sdb = (uint64_t*)h->hdata;
        size_t lhh = HASH_COMBINE(HASH_COMBINE(sdb[0], sdb[1]), HASH_COMBINE(sdb[4], sdb[5]));
        size_t rhh = HASH_COMBINE(HASH_COMBINE(sdb[2], sdb[3]), HASH_COMBINE(sdb[7], sdb[8]));
        return HASH_COMBINE(lhh, rhh);
    }

    static bool keyEqual(const BSQCryptoHash* l, const BSQCryptoHash* r)
    {
        return memcmp(l->hdata, r->hdata, 64) == 0;
    }
};

class BSQEventTime : public BSQRef
{
public:
    const uint64_t timestamp;

    BSQEventTime(uint64_t timestamp) : BSQRef(), timestamp(timestamp) { ; }
    virtual ~BSQEventTime() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQEventTime* t)
    {
        return (size_t)t->timestamp;
    }

    static bool keyEqual(const BSQEventTime* l, const BSQEventTime* r)
    {
        return l->timestamp == r->timestamp;
    }
};

class BSQEnum : public BSQRef
{
public:
    const uint32_t value;
    const MIRNominalTypeEnum oftype;

    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : BSQRef(), value(value), oftype(oftype) { ; }
    virtual ~BSQEnum() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQEnum* e)
    {
        return HASH_COMBINE((size_t)e->oftype, (size_t)e->value);
    }

    static bool keyEqual(const BSQEnum* l, const BSQEnum* r)
    {
        return (l->oftype == r->oftype) & (l->value == r->value);
    }
};

class BSQIdKey : public BSQRef
{
public:
    const MIRNominalTypeEnum oftype;
    const KeyValue key;

    BSQIdKey(KeyValue key, MIRNominalTypeEnum oftype) : BSQRef(), oftype(oftype), key(key) { ; }

    virtual ~BSQIdKey() = default;

    virtual void destroy() 
    { 
        BSQRef::decrementChecked(this->key); 
    }

    static size_t hash(const BSQIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype, bsqKeyValueHash(k->key));
    }

    static bool keyEqual(const BSQIdKey* l, const BSQIdKey* r)
    {
        return l->oftype == r->oftype && bsqKeyValueEqual(l->key, r->key);
    }
};

class BSQGUIDIdKey : public BSQRef
{
public:
    const BSQGUID gdata;
    const MIRNominalTypeEnum oftype;

    BSQGUIDIdKey(const BSQGUID& gdata, MIRNominalTypeEnum oftype) : BSQRef(), gdata(gdata), oftype(oftype) { ; }

    virtual ~BSQGUIDIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQGUIDIdKey* g)
    {
        return HASH_COMBINE((size_t)g->oftype, BSQGUID::hash(&g->gdata));
    }

    static bool keyEqual(const BSQGUIDIdKey* l, const BSQGUIDIdKey* r)
    {
        return l->oftype == r->oftype && memcmp(l->gdata.sdata, r->gdata.sdata, 16) == 0;
    }
};

class BSQDataHashIdKey : public BSQRef
{
public:
    const BSQDataHash hdata;
    const MIRNominalTypeEnum oftype;

    BSQDataHashIdKey(const BSQDataHash& hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    virtual ~BSQDataHashIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQDataHashIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype, BSQDataHash::hash(&k->hdata));
    }

    static bool keyEqual(const BSQDataHashIdKey* l, const BSQDataHashIdKey* r)
    {
        return (l->oftype == r->oftype) & (l->hdata.hdata == r->hdata.hdata);
    }
};

class BSQCryptoHashIdKey : public BSQRef
{
public:
    const BSQCryptoHash hdata;
    const MIRNominalTypeEnum oftype;

    BSQCryptoHashIdKey(const BSQCryptoHash& hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    virtual ~BSQCryptoHashIdKey() = default;
    virtual void destroy() { ; }

    static size_t hash(const BSQCryptoHashIdKey* k)
    {
        return HASH_COMBINE((size_t)k->oftype, BSQCryptoHash::hash(&k->hdata));
    }

    static bool keyEqual(const BSQCryptoHashIdKey* l, const BSQCryptoHashIdKey* r)
    {
        return l->oftype == r->oftype && memcmp(l->hdata.hdata, r->hdata.hdata, 64) == 0;
    }
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

    static size_t hash(const BSQTuple* t)
    {
        size_t hash = t->entries.size();
        for(size_t i = 0; i < t->entries.size(); ++i)
        {
            hash = HASH_COMBINE(hash, bsqKeyValueHash(t->entries[i]));
        }
        return hash;
    }

    static bool keyEqual(const BSQTuple* l, const BSQTuple* r)
    {
        if(l->entries.size() != r->entries.size())
        {
            return false;
        }

        for(size_t i = 0; i < l->entries.size(); ++i)
        {
            if(!bsqKeyValueEqual(l->entries[i], r->entries[i]))
            {
                return false;
            }
        }
        return true;
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

    static size_t hash(const BSQRecord* r)
    {
        size_t hash = r->entries.size();
        for(auto iter = r->entries.begin(); iter != r->entries.end(); ++iter)
        {
            hash = HASH_COMBINE(hash, HASH_COMBINE((size_t)iter->first, bsqKeyValueHash(iter->second)));
        }
        return hash;
    }

    static bool keyEqual(const BSQRecord* l, const BSQRecord* r)
    {
        if(l->entries.size() != r->entries.size())
        {
            return false;
        }

        for(auto liter = l->entries.begin(); liter != l->entries.end(); ++liter)
        {
            auto riter = r->entries.find(liter->first);
            if(riter == r->entries.end() || !bsqKeyValueEqual(liter->second, riter->second))
            {
                return false;
            }
        }
        return true;
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

template<typename T>
class BSQList : public BSQObject {
public:
    std::vector<T> entries;

    BSQList(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQList(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    virtual ~BSQList() = default;

    virtual void destroy()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
    }

    BSQList* unsafeAdd(const T& v) const
    {
        std::vector<Value> nv(this->entries.size(), nullptr);
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            nv[i] = BSQRef::checkedIncrementOf<Value>(this->entries[i]);
        }
        nv.push_back(BSQRef::checkedIncrementOf<Value>(v));

        return new BSQList(this->ntype, move(nv));
    }

    BSQList* unsafeSet(const BSQInt& idx, const T& v) const
    {
        std::vector<Value> nv(this->entries.size(), nullptr);
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            if(i == idx)
            {
                nv[i] = BSQRef::checkedIncrementOf<Value>(v);
            }
            else
            {
                nv[i] = BSQRef::checkedIncrementOf<Value>(this->entries[i]);
            }
        }

        return new BSQList(this->ntype, move(nv));
    }

    BSQList* destructiveAdd(const T& v)
    {
        this->entries.push_back(BSQRef::checkedIncrementOf<Value>(v));
        return this;
    }

    virtual std::u32string display() const
    {
        return std::u32string(U"[SHOULD BE SPECIAL CASED IN DISPLAY]");
    }
};

class BSQKeyList : public BSQObject {
public:
    Value key;
    BSQKeyList* tail;

    BSQKeyList(MIRNominalTypeEnum ntype, Value key, BSQKeyList* tail): BSQObject(ntype), key(key), tail(tail) { ; }

    virtual ~BSQKeyList()
    {
        BSQRef::checkedDecrement(this->key);
        BSQRef::checkedDecrementNoneable(this->tail);
    }

    virtual std::u32string display() const
    {
        return std::u32string(U"[INTERNAL KEY LIST]");
    }
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
