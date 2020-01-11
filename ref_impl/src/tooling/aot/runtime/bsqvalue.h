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

////
//Reference counting ops

#define INC_REF_DIRECT(T, V) ((T) BSQRef::incrementDirect(V))
#define INC_REF_NONEABLE(T, V) ((T) BSQRef::incrementNoneable(V))
#define INC_REF_CHECK(T, V) ((T) BSQRef::incrementChecked(V))

#define ADD_ALLOC_REF(T, E, SCOPE, SC) ((T) (SCOPE).addAllocRef<SC>(E))

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

class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(), sdata(str) { ; }
    BSQString(const char* str, int64_t excount) : BSQRef(excount), sdata(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>().from_bytes(str)) { ; }

    virtual ~BSQString() = default;
    virtual void destroy() { ; }
};

class BSQStringOf : public BSQRef
{
public:
    const std::u32string sdata;
    const MIRNominalTypeEnum oftype;
  
    BSQStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }

    virtual ~BSQStringOf() = default;
    virtual void destroy() { ; }
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
};

class BSQDataHash : public BSQRef
{
public:
    const uint64_t hdata;

    BSQDataHash(uint64_t hdata) : BSQRef(), hdata(hdata) { ; }
    virtual ~BSQDataHash() = default;
    virtual void destroy() { ; }
};

class BSQCryptoHash : public BSQRef
{
public:
    const uint8_t hdata[64];

    BSQCryptoHash(const uint8_t sdata[64]) : BSQRef(), hdata() { memcpy_s((void*)this->hdata, 64, hdata, 64); }
    virtual ~BSQCryptoHash() = default;
    virtual void destroy() { ; }
};

class BSQEventTime : public BSQRef
{
public:
    const uint64_t timestamp;

    BSQEventTime(uint64_t timestamp) : BSQRef(), timestamp(timestamp) { ; }
    virtual ~BSQEventTime() = default;
    virtual void destroy() { ; }
};

class BSQEnum : public BSQRef
{
public:
    const uint32_t value;
    const MIRNominalTypeEnum oftype;

    BSQEnum(uint32_t value, MIRNominalTypeEnum oftype) : BSQRef(), value(value), oftype(oftype) { ; }
    virtual ~BSQEnum() = default;
    virtual void destroy() { ; }
};

template <typename T, typename FDecOp>
class BSQIdKey : public BSQRef
{
public:
    const T sdata;
    const MIRNominalTypeEnum oftype;

    BSQIdKey(const T& sdata, MIRNominalTypeEnum oftype) : BSQRef(), sdata(sdata), oftype(oftype) { ; }

    virtual ~BSQIdKey() = default;

    virtual void destroy() 
    { 
        FDecOp(this->sdata); 
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
};

class BSQCryptoHashIdKey : public BSQRef
{
public:
    const BSQCryptoHash hdata;
    const MIRNominalTypeEnum oftype;

    BSQCryptoHashIdKey(const BSQCryptoHash& hdata, MIRNominalTypeEnum oftype) : BSQRef(), hdata(hdata), oftype(oftype) { ; }

    virtual ~BSQCryptoHashIdKey() = default;
    virtual void destroy() { ; }
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
    const std::vector<std::pair<MIRPropertyEnum, Value>> entries;

    BSQRecord(std::vector<std::pair<MIRPropertyEnum, Value>>&& entries) : BSQRef(), entries(move(entries)) { ; }

    virtual ~BSQRecord() = default;

    virtual void destroy()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::decrementChecked(this->entries[i].second);
        }
    }

    static BSQRecord* _empty;

    template <MIRPropertyEnum p>
    bool hasProperty() const
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            if(this->entries[i].first == p)
            {
                return true;
            }
        }

        return false;
    }

    template <MIRPropertyEnum p>
    Value atFixed() const
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            if(this->entries[i].first == p)
            {
                return this->entries[i].second;
            }
        }

        return BSQ_VALUE_NONE;
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

template<typename T, typename FIncOp, typename FDecOp, typename FDisplay>
class BSQList : public BSQObject {
public:
    std::vector<T> entries;

    BSQList(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQList(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    xxxx;

    virtual ~BSQList()
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

struct BSQIndexableHash {
    size_t operator()(const Value& v) const {
        if(BSQ_IS_VALUE_NONE(v))
        {
            return 0;
        }
        else if(BSQ_IS_VALUE_INT(v))
        {
            return BSQ_GET_VALUE_INT(v);
        }
        else
        {
            auto ptr = BSQ_GET_VALUE_PTR(v, BSQRef); 
            if(dynamic_cast<BSQBoxedInt*>(ptr) != nullptr)
            {
                auto bi = dynamic_cast<BSQBoxedInt*>(ptr);
                return bi->data.isInt() ? bi->data.getInt64() : bi->data.getBigInt()->hash();
            }
            else if(dynamic_cast<BSQString*>(ptr) != nullptr)
            {
                return std::hash<std::u32string>{}(dynamic_cast<BSQString*>(ptr)->sdata);
            }
            else if(dynamic_cast<BSQStringOf*>(ptr) != nullptr)
            {
                return std::hash<std::u32string>{}(dynamic_cast<BSQStringOf*>(ptr)->sdata);
            }
            else if(dynamic_cast<BSQGUID*>(ptr) != nullptr)
            {
                //TODO: hashcode
                return 0;
            }
            else if(dynamic_cast<BSQEnum*>(ptr) != nullptr)
            {
                //TODO: hashcode
                return 0;
            }
            else if(dynamic_cast<BSQIdKey*>(ptr) != nullptr)
            {
                //TODO: hashcode
                return 0;
            }
            else if(dynamic_cast<BSQTuple*>(ptr) != nullptr)
            {
                auto t = dynamic_cast<BSQTuple*>(ptr);
                size_t h = t->entries.size();
                for(size_t i = 0; i < t->entries.size(); ++i)
                {
                    BSQIndexableHash hh;
                    h = h ^ (hh(t->entries[i]) << 1);
                }
                return h;
            }
            else 
            {
                auto r = dynamic_cast<BSQRecord*>(ptr);
                size_t h = r->entries.size();
                for(size_t i = 0; i < r->entries.size(); ++i)
                {
                    BSQIndexableHash hh;
                    h = h ^ ((size_t)r->entries[i].first << 32) ^ (hh(r->entries[i].second) << 1);
                }
                return h;
            }
        }
    }
};

struct BSQIndexableEqual {
    bool operator()(const Value& v1, const Value& v2) const {
        if(BSQ_IS_VALUE_NONE(v1) || BSQ_IS_VALUE_NONE(v2))
        {
            return BSQ_IS_VALUE_NONE(v1) && BSQ_IS_VALUE_NONE(v2);
        }
        else if(BSQ_IS_VALUE_INT(v1) || BSQ_IS_VALUE_INT(v2))
        {
            if(BSQ_IS_VALUE_INT(v1) && BSQ_IS_VALUE_INT(v2))
            {
                return BSQ_GET_VALUE_INT(v1) == BSQ_GET_VALUE_INT(v2);
            }
            else if (BSQ_IS_VALUE_INT(v1) && BSQ_IS_VALUE_PTR(v2) && dynamic_cast<BSQBoxedInt*>(BSQ_GET_VALUE_PTR(v2, BSQRef)) != nullptr)
            {
                return BSQ_GET_VALUE_BSQINT(v1) == BSQ_GET_VALUE_BSQINT(v2);
            }
            else if (BSQ_IS_VALUE_PTR(v1) && dynamic_cast<BSQBoxedInt*>(BSQ_GET_VALUE_PTR(v1, BSQRef)) != nullptr && BSQ_IS_VALUE_INT(v2))
            {
                return BSQ_GET_VALUE_BSQINT(v1) == BSQ_GET_VALUE_BSQINT(v2);
            }
            else
            {
                return false;
            }
        }
        else
        {
            auto ptr1 = BSQ_GET_VALUE_PTR(v1, BSQRef); 
            auto ptr2 = BSQ_GET_VALUE_PTR(v2, BSQRef); 
            if(dynamic_cast<BSQBoxedInt*>(ptr1) != nullptr && dynamic_cast<BSQBoxedInt*>(ptr2) != nullptr)
            {
                return dynamic_cast<BSQBoxedInt*>(ptr1)->data == dynamic_cast<BSQBoxedInt*>(ptr2)->data;
            }
            else if(dynamic_cast<BSQString*>(ptr1) != nullptr && dynamic_cast<BSQString*>(ptr2) != nullptr)
            {
                return dynamic_cast<BSQString*>(ptr1)->sdata == dynamic_cast<BSQString*>(ptr2)->sdata;
            }
            else if(dynamic_cast<BSQStringOf*>(ptr1) != nullptr && dynamic_cast<BSQStringOf*>(ptr2) != nullptr)
            {
                return dynamic_cast<BSQStringOf*>(ptr1)->sdata == dynamic_cast<BSQStringOf*>(ptr2)->sdata;
            }
            else if(dynamic_cast<BSQGUID*>(ptr1) != nullptr && dynamic_cast<BSQGUID*>(ptr2) != nullptr)
            {
                //TODO: equals
                return false;
            }
            else if(dynamic_cast<BSQEnum*>(ptr1) != nullptr && dynamic_cast<BSQEnum*>(ptr2) != nullptr)
            {
                //TODO: equals
                return false;
            }
            else if(dynamic_cast<BSQIdKey*>(ptr1) != nullptr && dynamic_cast<BSQIdKey*>(ptr2) != nullptr)
            {
                //TODO: equals
                return false;
            }
            else if(dynamic_cast<BSQTuple*>(ptr1) != nullptr && dynamic_cast<BSQTuple*>(ptr2) != nullptr)
            {
                auto t1 = dynamic_cast<BSQTuple*>(ptr1);
                auto t2 = dynamic_cast<BSQTuple*>(ptr2);
                return std::equal(t1->entries.cbegin(), t1->entries.cend(), t2->entries.cbegin(), t2->entries.cend(), [](const Value& a, const Value& b) {
                    BSQIndexableEqual eq;
                    return eq(a, b); 
                });
            }
            else if(dynamic_cast<BSQRecord*>(ptr1) != nullptr && dynamic_cast<BSQRecord*>(ptr2) != nullptr)
            {
                auto r1 = dynamic_cast<BSQRecord*>(ptr1);
                auto r2 = dynamic_cast<BSQRecord*>(ptr2);
                return std::equal(r1->entries.cbegin(), r1->entries.cend(), r2->entries.cbegin(), r2->entries.cend(), [](const std::pair<MIRPropertyEnum, Value>& a, const std::pair<MIRPropertyEnum, Value>& b) {
                    BSQIndexableEqual eq;
                    return a.first == b.first && eq(a.second, b.second); 
                });
            }
            else 
            {
                return false;
            }
        }
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
