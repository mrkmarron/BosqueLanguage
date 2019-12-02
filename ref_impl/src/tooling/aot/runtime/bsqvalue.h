//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalidator.h"
#include "bigint.h"

#pragma once

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0xF) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_INT(V) (int32_t)(((int64_t)(V)) >> 0x32)
#define BSQ_GET_VALUE_PTR(V, T) (reinterpret_cast<T*>(V))

#define BSQ_BOX_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_BOX_VALUE_INT(I) ((void*)((((int64_t) I) << 0x32) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE ((void*)0x3)
#define BSQ_VALUE_FALSE ((void*)0x2)

#define BIG_INT_VALUE(X) (X.isInt() ? BigInt(X.getInt()) : *((X).getBigInt()))

#define BSQ_VALUE_0 BSQInt(0)
#define BSQ_VALUE_POS_1 BSQInt(1)
#define BSQ_VALUE_NEG_1 BSQInt(-1)

#define BSQ_BOX_VALUE_BSQINT(E, SCOPE, SC) ((E).isInt() ? BSQ_BOX_VALUE_INT((E).getInt()) : (SCOPE).addAllocRef<SC, BSQBoxedInt>(new BSQBoxedInt(E)))
#define BSQ_GET_VALUE_BSQINT(E) (BSQ_IS_VALUE_INT(E) ? BSQInt(BSQ_GET_VALUE_INT(E)) : BSQ_GET_VALUE_PTR(E, BSQBoxedInt)->data)

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE
};

//%%KNOWN_PROPERTY_LIST_DECLARE

enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE
};

//%%CONCEPT_SUBTYPE_RELATION_DECLARE

enum class MIRArrayTypeEnum
{
    Invalid = 0x0,
//%%ARRAY_TYPE_ENUM_DECLARE
};

class BSQInt
{
private:
    void* data; 

public:
    inline bool isInt() const
    {
        return (((int64_t)this->data) & 0x1) == 1;
    }

    inline int32_t getInt() const
    {
        return (int32_t)(((int64_t)this->data) >> 32);
    }

    inline BigInt* getBigInt() const
    {
        return reinterpret_cast<BigInt*>(this->data);
    }

    inline int64_t getInt64() const
    {
        return reinterpret_cast<int64_t>(this->data) >> 32;
    }

    BSQInt() : data((void*)((int64_t)0x1)) { ; }

    BSQInt(int32_t value) : data(nullptr) 
    { 
        this->data = (void*)((((int64_t)value) << 32) | 0x1);
    }

    BSQInt(BigInt* value) : data((void*)value) 
    { 
        ; 
    }

    BSQInt(const BSQInt& src)
    { 
        this->data = src.isInt() ? src.data : src.getBigInt()->copy();
    }

    BSQInt& operator=(const BSQInt& src)
    {
        if (&src != this)
        {
            if (!this->isInt())
            {
                this->getBigInt()->release();
            }
            this->data = src.isInt() ? src.data : src.getBigInt()->copy();
        }
        return *this;
    }

    BSQInt(BSQInt&& src) : data(src.data)
    { 
        src.data = (void*)((int64_t)0x1);
    }

    BSQInt& operator=(BSQInt&& src)
    {
        if (&src != this)
        {
            if (!this->isInt())
            {
                this->getBigInt()->release();
            }
            this->data = src.data;

            src.data = (void*)((int64_t)0x1);
        }
        return *this;
    }

    ~BSQInt()
    {
        if(!this->isInt())
        {
            this->getBigInt()->release();
        }
    }

    inline bool isZero() const
    {
        if(this->isInt())
        {
            return this->getInt() == 0;
        }
        else
        {
            return this->getBigInt()->isZero();
        }
    }

    inline BSQInt negate() const
    {
        if(this->isInt())
        {
            return BSQInt(-this->getInt());
        }
        else
        {
            return BSQInt(this->getBigInt()->negate());
        }
    }

    inline friend bool operator==(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() == r.getInt();
        }
        else
        {
            return BigInt::eq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }    
    }

    inline friend bool operator!=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() != r.getInt();
        }
        else
        {
            return BigInt::neq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }    
    }

    inline friend bool operator<(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() < r.getInt();
        }
        else
        {
            return BigInt::lt(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }   
    }

    inline friend bool operator<=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() <= r.getInt();
        }
        else
        {
            return BigInt::lteq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        } 
    }

    inline friend bool operator>(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() > r.getInt();
        }
        else
        {
            return BigInt::gt(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }   
    }

    inline friend bool operator>=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() >= r.getInt();
        }
        else
        {
            return BigInt::gteq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        } 
    }

    inline friend BSQInt operator+(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() + r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::add(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator-(const BSQInt& l, const BSQInt& r)
    {
       if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() - r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::sub(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator*(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() * r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::mult(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator/(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() / r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::div(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator%(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() % r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::mod(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }
};

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

    inline static Value checkedIncrement(Value v)
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
    const std::vector<uint8_t> sdata;

    BSQString(const std::vector<uint8_t>& str) : BSQRef(), sdata(str) { ; }
    BSQString(const std::string& str, int64_t excount) : BSQRef(excount), sdata(str.cbegin(), str.cend()) { ; }

    virtual ~BSQString() = default;
};

class BSQStringOf : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;
    const MIRNominalTypeEnum oftype;

    BSQStringOf(const std::vector<uint8_t>& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }
    virtual ~BSQStringOf() = default;
};

class BSQValidatedString : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;
    const BSQValidator* validator;
    const MIRNominalTypeEnum oftype;

    BSQValidatedString(const std::vector<uint8_t>& str, const BSQValidator* validator, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), validator(validator), oftype(oftype) { ; }
    virtual ~BSQValidatedString() = default;
};

class BSQPODBuffer : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;
    const MIRNominalTypeEnum oftype;

    BSQPODBuffer(std::vector<uint8_t>&& sdata, MIRNominalTypeEnum oftype) : BSQRef(), sdata(move(sdata)), oftype(oftype) { ; }
    virtual ~BSQPODBuffer() = default;
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

template <uint16_t k>
class BSQTupleFixed
{
public:
    uint16_t size;
    Value entries[std::max(k, (uint16_t)1)];

    template <uint16_t idx>
    inline Value atFixed()
    {
        return (idx < this->size) ? this->entries[idx] : BSQ_VALUE_NONE;
    }

    inline Value atVar(uint16_t idx)
    {
        return (idx < this->size) ? this->entries[idx] : BSQ_VALUE_NONE;
    }

    inline BSQTupleFixed<k> copyWithRefInc()
    {
        for(uint16_t i = 0; i < this->size; ++i)
        {
            BSQRef::checkedIncrement(this->entries[i]);
        }
        return *this;
    }

    inline void allRefDec()
    {
        for(uint16_t i = 0; i < this->size; ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
    }
};

template <uint16_t k>
class BSQTupleKnown
{
public:
    Value entries[std::max(k, (uint16_t)1)];

    template <uint16_t idx>
    inline Value atFixed()
    {
        return this->entries[idx];
    }

    inline Value atVar(uint16_t idx)
    {
        return this->entries[idx];
    }

    inline BSQTupleKnown<k> copyWithRefInc()
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            BSQRef::checkedIncrement(this->entries[i]);
        }
        return *this;
    }

    inline void allRefDec()
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
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

template <uint16_t k>
class BSQRecordFixed
{
public:
    uint16_t size;
    std::pair<MIRPropertyEnum, Value> entries[std::max(k, (uint16_t)1)];

    template <MIRPropertyEnum p>
    bool hasProperty() const
    {
        for(size_t i = 0; i < this->size; ++i)
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
        for(uint16_t i = 0; i < this->size; ++i)
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
        for(uint16_t i = 0; i < this->size; ++i)
        {
            if(this->entries[i].first == p)
            {
                return this->entries[i].second;
            }
        }

        return BSQ_VALUE_NONE;
    }

    inline BSQRecordFixed<k> copyWithRefInc()
    {
        for(uint16_t i = 0; i < this->size; ++i)
        {
            BSQRef::checkedIncrement(this->entries[i].second);
        }
        return *this;
    }

    inline void allRefDec()
    {
        for(uint16_t i = 0; i < this->size; ++i)
        {
            BSQRef::checkedDecrement(this->entries[i].second);
        }
    }
};

template <uint16_t k>
class BSQRecordKnown
{
public:
    Value entries[std::max(k, (uint16_t)1)];

    template <uint16_t pidx>
    inline Value atPropertyIndex()
    {
        return this->entries[pidx];
    }

    template <MIRPropertyEnum p>
    inline static bool hasProperty(const MIRPropertyEnum(&properties)[k])
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            if(properties[i] == p)
            {
                return true;
            }
        }

        return false;
    }

    inline BSQRecordKnown<k> copyWithRefInc()
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            BSQRef::checkedIncrement(this->entries[i]);
        }
        return *this;
    }

    inline void allRefDec()
    {
        for(uint16_t i = 0; i < k; ++i)
        {
            BSQRef::checkedDecrement(this->entries[i]);
        }
    }
};

constexpr BSQTupleFixed<0> BSQTupleFixed_empty = {0, {nullptr}};
constexpr BSQTupleKnown<0> BSQTupleKnown_empty = {nullptr};
constexpr BSQRecordFixed<0> BSQRecordFixed_empty = {0, {std::make_pair(MIRPropertyEnum::Invalid, nullptr)}};
constexpr BSQRecordKnown<0> BSQRecordKnown_empty = {nullptr};

namespace StructuralCoercionOps
{
    template<uint16_t k>
    inline BSQTuple* boxTupleFixed(const BSQTupleFixed<k>& src)
    {
        std::vector<Value> rvals(src.size, nullptr);
        for(uint16_t i = 0; i < src.size; ++i)
        {
            rvals[i] = BSQRef::checkedIncrement(src.entries[i]);
        }
        return new BSQTuple(move(rvals));
    }

    template<>
    inline BSQTuple* boxTupleFixed(const BSQTupleFixed<0>& src)
    {
        return BSQTuple::_empty;
    }

    template<uint16_t k>
    inline BSQTupleFixed<k> unboxTupleFixed(const BSQTuple* src)
    {
        BSQTupleFixed<k> res;
        res.size = src->entries.size();
        for(uint16_t i = 0; i < src->entries.size(); ++i)
        {
            res.entries[i] = src->entries[i];
        }
        return res;
    }

    template<>
    inline BSQTupleFixed<0> unboxTupleFixed(const BSQTuple* src)
    {
        return BSQTupleFixed_empty;
    }

    template <uint16_t k, uint16_t j>
    inline BSQTupleFixed<k> projectTupleDownFixed(const BSQTupleFixed<j>& src)
    {
        static_assert(k < j, "size error");

        BSQTupleFixed<k> res;
        res.size = src.size;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src.entries[i];
        }
        return res;
    }

    template <uint16_t j>
    inline BSQTupleFixed<0> projectTupleDownFixed(const BSQTupleFixed<j>& src)
    {
        return BSQTupleFixed_empty;
    }

    template <uint16_t k, uint16_t j>
    inline BSQTupleFixed<k> projectTupleUpFixed(const BSQTupleFixed<j>& src)
    {
        static_assert(k > j, "size error");

        BSQTupleFixed<k> res;
        res.size = src.size;
        for(uint16_t i = 0; i < j; ++i)
        {
            res.entries[i] = entries[i];
        }
        return res;
    }

    template<uint16_t k>
    inline BSQTuple* boxTupleKnown(const BSQTupleKnown<k>& src)
    {
        std::vector<Value> rvals(k, nullptr);
        for(uint16_t i = 0; i < k; ++i)
        {
            rvals[i] = BSQRef::checkedIncrement(src.entries[i]);
        }
        return new BSQTuple(move(rvals));
    }

    template<>
    inline BSQTuple* boxTupleKnown(const BSQTupleKnown<0>& src)
    {
        return BSQTuple::_empty;
    }

    template<uint16_t k>
    inline BSQTupleKnown<k> unboxTupleKnown(const BSQTuple* src)
    {
        BSQTupleKnown<k> res;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src->entries[i];
        }
        return res;
    }

    template<>
    inline BSQTupleKnown<0> unboxTupleKnown(const BSQTuple* src)
    {
        return BSQTupleKnown_empty;
    }

    template<uint16_t k, uint16_t j>
    inline BSQTupleFixed<k> convertTupleKnownToFixed(const BSQTupleKnown<j>& src)
    {
        static_assert(k >= j, "size error");

        BSQTupleFixed<k> res;
        res.size = j;
        for(uint16_t i = 0; i < j; ++i)
        {
            res.entries[i] = src.entries[i];
        }
        return res;
    }

    template<uint16_t j>
    inline BSQTupleFixed<0> convertTupleKnownToFixed(const BSQTupleKnown<j>& src)
    {
        return BSQTupleFixed_empty;
    }

    template<uint16_t k, uint16_t j>
    inline BSQTupleKnown<k> convertTupleFixedToKnown(const BSQTupleFixed<j> src)
    {
        static_assert(k <= j, "size error");

        BSQTupleKnown<k> res;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src.entries[i];
        }
        return res;
    }

    template<uint16_t j>
    inline BSQTupleKnown<0> convertTupleFixedToKnown(const BSQTupleFixed<j> src)
    {
       return BSQTupleKnown_empty;
    }

    template<uint16_t k>
    inline BSQRecord* boxRecordFixed(const BSQRecordFixed<k>& src)
    {
        std::vector<std::pair<MIRPropertyEnum, Value>> rvals(src.size, std::make_pair(MIRPropertyEnum::Invalid, nullptr));
        for(uint16_t i = 0; i < src.size; ++i)
        {
            rvals[i] = std::make_pair(src.entries[i].first, BSQRef::checkedIncrement(src.entries[i].second));
        }
        return new BSQRecord(move(rvals));
    }

    template<>
    inline BSQRecord* boxRecordFixed(const BSQRecordFixed<0>& src)
    {
        return BSQRecord::_empty;
    }

    template<uint16_t k>
    inline BSQRecordFixed<k> unboxRecordFixed(const BSQRecord* src)
    {
        BSQTupleFixed<k> res;
        res.size = src->entries.size();
        for(uint16_t i = 0; i < src->entires.size(); ++i)
        {
            res.entries[i] = src->entries[i];
        }
        return res;
    }

    template<>
    inline BSQRecordFixed<0> unboxRecordFixed(const BSQRecord* src)
    {
        return BSQRecordFixed_empty;
    }

    template <uint16_t k, uint16_t j>
    inline BSQRecordFixed<k> projectRecordDownFixed(const BSQTupleFixed<j>& src)
    {
        static_assert(k < j, "size error");

        BSQRecordFixed<k> res;
        res.size = src.size;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src.entries[i];
        }
        return res;
    }

    template <uint16_t j>
    inline BSQRecordFixed<0> projectRecordDownFixed(const BSQTupleFixed<j>& src)
    {
        return BSQRecordFixed_empty;
    }

    template <uint16_t k, uint16_t j>
    inline BSQRecordFixed<k> projectRecordUpFixed(const BSQTupleFixed<j>& src)
    {
        static_assert(k > j, "size error");

        BSQRecordFixed<k> res;
        res.size = src.size;
        for(uint16_t i = 0; i < j; ++i)
        {
            res.entries[i] = entries[i];
        }
        return res;
    }

    template<uint16_t k>
    inline BSQRecord* boxRecordKnown(const BSQRecordKnown<k>& src, const MIRPropertyEnum(&properties)[k])
    {
        std::vector<std::pair<MIRPropertyEnum, Value>> rvals(k, std::make_pair(MIRPropertyEnum::Invalid, nullptr));
        for(uint16_t i = 0; i < k; ++i)
        {
            rvals[i] = std::make_pair(properties[i], BSQRef::checkedIncrement(src.entries[i]));
        }
        return new BSQRecord(move(rvals));
    }

    template<uint16_t k>
    inline BSQRecordKnown<k> unboxRecordKnown(const BSQRecord* src)
    {
        BSQRecordKnown<k> res;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src->entries[i].second;
        }
        return res;
    }

    template<>
    inline BSQRecordKnown<0> unboxRecordKnown(const BSQRecord* src)
    {
        return BSQRecordKnown_empty;
    }

    template<uint16_t k, uint16_t j>
    inline BSQRecordFixed<k> convertRecordKnownToFixed(const BSQRecordKnown<j>& src, const MIRPropertyEnum(&properties)[j])
    {
        static_assert(k >= j, "size error");

        BSQRecordFixed<k> res;
        res.size = j;
        for(uint16_t i = 0; i < j; ++i)
        {
            res.entries[i] = std::make_pair(properties[i], src.entries[i]);
        }
        return res;
    }

    template<uint16_t k, uint16_t j>
    inline BSQRecordKnown<k> convertRecordFixedToKnown(const BSQRecordFixed<j> src)
    {
        static_assert(k <= j, "size error");

        BSQRecordKnown<k> res;
        for(uint16_t i = 0; i < k; ++i)
        {
            res.entries[i] = src.entries[i].second;
        }
        return res;
    }

    template<uint16_t j>
    inline BSQRecordKnown<0> convertRecordFixedToKnown(const BSQRecordFixed<j> src)
    {
       return BSQRecordKnown_empty;
    }
};

class BSQObject : public BSQRef
{
public:
    MIRNominalTypeEnum ntype;

    BSQObject(MIRNominalTypeEnum ntype) : BSQRef(), ntype(ntype) { ; }
    virtual ~BSQObject() = default;

    virtual std::string display() const = 0;

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
        return std::binary_search(&etypes[0], &etypes[k], tt) != &etypes[k]; 
    }
};
} // namespace BSQ
