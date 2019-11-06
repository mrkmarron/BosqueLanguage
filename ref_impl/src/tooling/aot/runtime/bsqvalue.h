//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalidator.h"

#pragma once

#define BSQ_IS_VALUE_NONE(V) ((V) == nullptr)
#define BSQ_IS_VALUE_NONNONE(V) ((V) != nullptr)

#define BSQ_IS_VALUE_BOOL(V) ((((uintptr_t)(V)) & 0x2) == 0x2)
#define BSQ_IS_VALUE_INT(V) ((((uintptr_t)(V)) & 0x4) == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((((uintptr_t)(V)) & 0xF) == 0)

#define BSQ_GET_VALUE_BOOL(V) (((uintptr_t)(V)) & 0x1)
#define BSQ_GET_VALUE_INT(V) ((int64_t)(((uintptr_t)(V)) >> 4))
#define BSQ_GET_VALUE_PTR(V, T) ((T*)(V))

#define BSQ_BOX_VALUE_BOOL(B) ((void*)(((uintptr_t)(B)) | 0x2))
#define BSQ_BOX_VALUE_INT(I) ((void*)((((int64_t) I) << 0x4) | 0x4))

#define BSQ_GET_VALUE_TRUTHY(V) (((uintptr_t)(V)) & 0x1)

#define BSQ_VALUE_NONE nullptr
#define BSQ_VALUE_TRUE ((void*)0x3)
#define BSQ_VALUE_FALSE ((void*)0x2)

#define BSQ_VALUE_0 BSQ_BOX_VALUE_INT(0)
#define BSQ_VALUE_POS_1 BSQ_BOX_VALUE_INT(1)
#define BSQ_VALUE_NEG_1 BSQ_BOX_VALUE_INT(-1)

#define BINT_MAX 4503599627370495
#define BINT_MIN (-4503599627370496)

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

enum class MIRArrayTypeEnum
{
    Invalid = 0x0,
//%%ARRAY_TYPE_ENUM_DECLARE
};


enum class FixedRecordPropertyListEnum
{
    Invalid = 0x0,
//%%FIXED_RECORD_PROPERTY_LIST_ENUM_DECLARE
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

    inline static void checkedIncrementFast(Value v)
    {
        BSQRef::increment(BSQ_GET_VALUE_PTR(v, BSQRef));
        return v;
    }

    inline static void checkedIncrementNoneable(Value v)
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
            BSQRef::decrement(this->opts[i]);
        }
    }

    template<uint16_t pos>
    inline BSQRef** getCallerSlot() {
        return this->opts + pos; 
    }

    template <uint16_t pos>
    inline BSQRef* addAllocRef(BSQRef* ptr)
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

class BSQString : public BSQRef
{
public:
    const std::string sdata;

    BSQString(const std::string& str) : BSQRef(), sdata(str) { ; }
    BSQString(std::string&& str, int64_t excount) : BSQRef(excount), sdata(move(str)) { ; }

    virtual ~BSQString() = default;
};

class BSQStringOf : public BSQRef
{
public:
    const std::string sdata;
    const MIRNominalTypeEnum oftype;

    BSQStringOf(const std::string& str, MIRNominalTypeEnum oftype) : BSQRef(), sdata(str), oftype(oftype) { ; }
    virtual ~BSQStringOf() = default;
};

class BSQValidatedString : public BSQRef
{
public:
    const std::string sdata;
    const BSQValidator* validator;

    BSQValidatedString(const std::string& str, const BSQValidator* validator) : BSQRef(), sdata(str), validator(validator) { ; }
    virtual ~BSQValidatedString() = default;
};

class BSQPODBuffer : public BSQRef
{
public:
    const std::vector<uint8_t> sdata;

    BSQPODBuffer(std::vector<uint8_t>&& sdata) : BSQRef(), sdata(move(sdata)) { ; }
    virtual ~BSQPODBuffer() = default;
};

class BSQGUID : public BSQRef
{
public:
    const std::string sdata;

    BSQGUID(const std::string& sdata) : BSQRef(), sdata(sdata) { ; }
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
    Value entries[k];

    template <uint16_t idx>
    inline Value atFixed()
    {
        return this->entries[idx];
    }

    inline Value atVar(uint16_t idx)
    {
        return this->entries[idx];
    }

    inline Value box()
    {
        return new BSQRecord(std::vector<Value>(this->entries, this->entries + k));
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

    template <MIRPropertyEnum p>
    Value atFixed() const
    {
        auto iter = std::find_if(this->entries.cbegin(), this->entries.cend() [](const std::pair<MIRPropertyEnum, Value>& entry) {
            return entry.first == p;
        });
        return (iter != this->entries.cend()) ? iter->second : BSQ_VALUE_NONE;
    }

    Value atVar(MIRPropertyEnum p) const
    {
        auto iter = std::find_if(this->entries.cbegin(), this->entries.cend(), [p](const std::pair<MIRPropertyEnum, Value>& entry) {
            return entry.first == p;
        });
        return (iter != this->entries.cend()) ? iter->second : BSQ_VALUE_NONE;
    }
};

template <FixedRecordPropertyListEnum rt, uint16_t k>
class BSQRecordFixed
{
public:
    Value entries[k];

    template <uint16_t pidx>
    inline Value atFixed()
    {
        return this->entries[pidx];
    }

    inline Value atVar(uint16_t pidx)
    {
        return this->entries[pidx];
    }
};

class BSQArray : public BSQRef
{
public:
    const MIRArrayTypeEnum atype;
    const std::vector<Value> contents;

    BSQArray(MIRArrayTypeEnum atype, std::vector<Value>&& contents) : BSQRef(), atype(atype), contents(move(contents)) { ; }

    virtual ~BSQArray()
    {
        for(size_t i = 0; i < this->contents.size(); ++i)
        {
            BSQRef::checkedDecrement(this->contents[i]);
        }
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
};
} // namespace BSQ
