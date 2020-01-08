//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqint.h"

#include <unordered_map>

#pragma once

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

#define BSQ_BOX_VALUE_BSQINT(E, SCOPE, SC) ((E).isInt() ? BSQ_ENCODE_VALUE_INT((E).getInt()) : (SCOPE).addAllocRef<SC, BSQBoxedInt>(new BSQBoxedInt(E)))
#define BSQ_GET_VALUE_BSQINT(E) (BSQ_IS_VALUE_INT(E) ? BSQInt(BSQ_GET_VALUE_INT(E)) : BSQ_GET_VALUE_PTR(E, BSQBoxedInt)->data)

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

    inline static void increment(BSQRef* rcb)
    {
        rcb->count++;
    }

    inline static void decrement(BSQRef* rcb)
    {
        rcb->count--;

        if(rcb->count == 0)
        {
            delete rcb;    
        }
    }

    template <typename T>
    inline static T* checkedIncrementFast(T* v)
    {
        BSQRef::increment(v);
        return v;
    }

    template <typename T>
    inline static T* checkedIncrementNoneable(T* v)
    {
        if(BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(v, BSQRef));
        }
        return v;
    }

    inline static void checkedIncrementNop(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(v, BSQRef));
        }
    }

    template <typename T>
    inline static T checkedIncrementOf(T v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(v, BSQRef));
        }

        return v;
    }

    inline static void checkedDecrementFast(Value v)
    {
        BSQRef::decrement(BSQ_GET_VALUE_PTR(v, BSQRef));
    }

    inline static void checkedDecrementNoneable(Value v)
    {
        if(BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::decrement(BSQ_GET_VALUE_PTR(v, BSQRef));
        }
    }

    inline static void checkedDecrement(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::decrement(BSQ_GET_VALUE_PTR(v, BSQRef));
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

    template <uint16_t pos, typename T>
    inline T* addAllocRef(T* ptr)
    {
        BSQRef::increment(ptr);
        this->opts[pos] = ptr;

        return ptr;
    }
};

class BSQRefScopeMgr
{
public:
    inline static void processCallReturnFast(BSQRef** callerslot, BSQRef* ptr)
    {
        BSQRef::increment(ptr);
        *callerslot = ptr;
    }

    inline static void processCallRefNoneable(BSQRef** callerslot, Value ptr)
    {
        if(BSQ_IS_VALUE_NONNONE(ptr))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(ptr, BSQRef));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, BSQRef);
        }
    }

    inline static void processCallRefAny(BSQRef** callerslot, Value ptr)
    {
        if(BSQ_IS_VALUE_PTR(ptr) & BSQ_IS_VALUE_NONNONE(ptr))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(ptr, BSQRef));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, BSQRef);
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
};

class BSQString : public BSQRef
{
public:
    const std::u32string sdata;

    BSQString(const std::u32string& str) : BSQRef(), sdata(str) { ; }
    BSQString(const char* str, int64_t excount) : BSQRef(excount), sdata(std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>().from_bytes(str)) { ; }

    virtual ~BSQString() = default;
};

class BSQStringOf : public BSQRef
{
public:
    const std::u32string sdata;
    const MIRNominalTypeEnum oftype;
  
    BSQStringOf(const std::u32string& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }
    virtual ~BSQStringOf() = default;
};

class BSQValidatedString : public BSQRef
{
public:
    const std::u32string sdata;
    const std::basic_regex<char32_t> ofpattern;

    BSQValidatedString(const std::u32string& str, std::basic_regex<char32_t> ofpattern) : BSQRef(), sdata(str), ofpattern(ofpattern) { ; }
    virtual ~BSQValidatedString() = default;
};

class BSQBuffer : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;
    const MIRNominalTypeEnum oftype;

    BSQBuffer(std::vector<uint8_t>&& sdata, MIRNominalTypeEnum oftype) : BSQRef(), sdata(move(sdata)), oftype(oftype) { ; }
    virtual ~BSQBuffer() = default;
};

class BSQGUID : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;

    BSQGUID(const std::vector<uint8_t>& sdata) : BSQRef(), sdata(sdata) { ; }
    virtual ~BSQGUID() = default;
};

class BSQEnum : public BSQRef
{
public:
    const char* ename;
    const int64_t value;
    const MIRNominalTypeEnum oftype;

    BSQEnum(const char* ename, int64_t value, MIRNominalTypeEnum oftype) : BSQRef(), ename(ename), value(value), oftype(oftype) { ; }
    virtual ~BSQEnum() = default;
};

class BSQIdKey : public BSQRef
{
public:
    const Value sdata;
    const MIRNominalTypeEnum oftype;

    BSQIdKey(Value sdata, MIRNominalTypeEnum oftype) : BSQRef(), sdata(sdata), oftype(oftype) { ; }

    virtual ~BSQIdKey()
    {
        BSQRef::checkedDecrement(this->sdata);
    }
};

class BSQTuple : public BSQRef
{
public:
    const std::vector<Value> entries;

    BSQTuple(std::vector<Value>&& entries) : BSQRef(), entries(move(entries)) { ; }

    virtual ~BSQTuple()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
    }

    static BSQTuple* _empty;

    template <uint16_t idx>
    Value atFixed() const
    {
        return (idx < this->entries.size()) ? this->entries[idx] : BSQ_VALUE_NONE;
    }

    Value atVar(uint16_t idx) const
    {
        return (idx < this->entries.size()) ? this->entries[idx] : BSQ_VALUE_NONE;
    }
};

class BSQRecord : public BSQRef
{
public:
    const std::vector<std::pair<MIRPropertyEnum, Value>> entries;

    BSQRecord(std::vector<std::pair<MIRPropertyEnum, Value>>&& entries) : BSQRef(), entries(move(entries)) { ; }

    virtual ~BSQRecord()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i].second);
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

    Value atVar(MIRPropertyEnum p) const
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

class BSQList : public BSQObject {
public:
    std::vector<Value> entries;

    BSQList(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    BSQList(MIRNominalTypeEnum ntype, std::vector<Value>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    virtual ~BSQList()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
    }

    BSQList* unsafeAdd(Value v) const
    {
        std::vector<Value> nv(this->entries.size(), nullptr);
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            nv[i] = BSQRef::checkedIncrementOf<Value>(this->entries[i]);
        }
        nv.push_back(BSQRef::checkedIncrementOf<Value>(v));

        return new BSQList(this->ntype, move(nv));
    }

    BSQList* unsafeSet(const BSQInt& idx, Value v) const
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

    BSQList* destructiveAdd(Value v)
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
