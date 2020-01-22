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

#define BSQ_NEW_ADD_SCOPE(SCOPE, T, ...) ((T*)((SCOPE).addAllocRef(new T(__VA_ARGS__))))

#define INC_REF_DIRECT(T, V) ((T*) BSQRef::incrementDirect(V))
#define INC_REF_NONEABLE(T, V) ((T*) BSQRef::incrementNoneable(V))
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

    inline BSQRef* addAllocRef(BSQRef* ptr)
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

    inline void processReturnNoneable(BSQRef* ptr)
    {
        if(BSQ_IS_VALUE_NONNONE(ptr))
        {
            ptr->increment();
            this->opts.push_back(ptr);
        }
    }

    inline void processReturnInt(IntValue i)
    {
        if(BSQ_IS_VALUE_PTR(i))
        {
            BSQRef* ptr = BSQ_GET_VALUE_PTR(i, BSQRef);
            ptr->increment();
            this->opts.push_back(ptr);
        }
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


struct ReturnOpFunctor_bool
{
    size_t operator()(bool b, BSQRefScope& scope) { ; }
};
struct ReturnOpFunctor_IntValue
{
    size_t operator()(IntValue i, BSQRefScope& scope) { scope.processReturnInt(i); }
};
struct ReturnOpFunctor_IntValueNoneable
{
    size_t operator()(IntValue i, BSQRefScope& scope) { scope.processReturnChecked(i); }
};
struct ReturnOpFunctor_Direct
{
    size_t operator()(BSQRef* ptr, BSQRefScope& scope) { scope.callReturnDirect(ptr); }
};
struct ReturnOpFunctor_Noneable
{
    size_t operator()(BSQRef* ptr, BSQRefScope& scope) { scope.processReturnNoneable(ptr); }
};
struct ReturnOpFunctor_Checked
{
    size_t operator()(Value v, BSQRefScope& scope) { scope.processReturnChecked(v); }
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

    BigInt* negate() const
    {
        return nullptr;
    }

    bool eqI64(int64_t v) const
    {
        return false;
    }

    static bool eq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

    static bool neq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

    static bool lt(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

    static bool lteq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

     static bool gt(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

    static bool gteq(const BSQBigInt& l, const BSQBigInt& r)
    {
        return false;
    }

    static BigInt* add(const BSQBigInt &l, const BSQBigInt &r)
    {
        return nullptr;
    }

    static BigInt* sub(const BSQBigInt &l, const BSQBigInt &r)
    {
        return nullptr;
    }

    static BigInt* mult(const BSQBigInt &l, const BSQBigInt &r)
    {
        return nullptr;
    }

    static BigInt* div(const BSQBigInt &l, const BSQBigInt &r)
    {
        return nullptr;
    }

    static BigInt* mod(const BSQBigInt &l, const BSQBigInt &r)
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
            return BSQBigInt::eq(*BSQ_GET_VALUE_PTR(l, BSQBigInt), *BSQ_GET_VALUE_PTR(r, BSQBigInt));
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

template<typename K, typename KFReturnOp, typename KFDecOp, typename V, typename VFReturnOp, typename VFDecOp>
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
        KFDecOp(this->key);
        VFDecOp(this->value);
    }

    void processReturn(BSQRefScope& scope)
    {
        KFReturnOp(this->key, scope);
        VFReturnOp(this->value, scope);
    }
};

template<typename T, typename TFReturnOp, typename TDecOp>
class BSQResult : public BSQRef
{
    T success;
    Value error;

    BSQResult() : BSQRef() { ; }
    BSQResult(const T& success, Value error) : BSQRef(), success(success), error(error) { ; }

    BSQResult(const BSQResult& src) : BSQRef(), success(src.success), error(src.error) 
    { 
        ; 
    }

    BSQResult& operator=(const BSQResult& src)
    {
        this->success = src.success;
        this->error = src.error;
        return *this;
    }

    virtual ~BSQResult() = default;

    virtual void destroy() 
    {
        TFDecOp(this->success);
        BSQRef::decrementChecked(this->error);
    }

    void processReturn(BSQRefScope& scope)
    {
        TFReturnOp(this->success, scope);
        scope.processReturnChecked(this->error);
    }
};

template<typename K, typename KFReturnOp, typename KFDecOp, typename U, typename UFReturnOp, typename UFDecOp>
class BSQTagged : public BSQRef
{
public:
    K key;
    U value;

    BSQTagged() : BSQRef() { ; }
    BSQTagged(const K& k, const U& u) : BSQRef(), key(k), value(u) { ; }

    BSQTagged(const BSQTagged& src) : BSQRef(), key(src.key), value(src.value) 
    { 
        ; 
    }

    BSQTagged& operator=(const BSQTagged& src)
    {
        this->key = src.key;
        this->value = src.value;
        return *this;
    }

    virtual ~BSQTagged() = default;

    virtual void destroy() 
    {
        KFDecOp(this->key);
        UFDecOp(this->value);
    }

    void processReturn(BSQRefScope& scope)
    {
        KFReturnOp(this->key, scope);
        UFReturnOp(this->value, scope);
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
