//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

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

typedef void* Value;

class BSQRef
{
private:
    int64_t count;
    const MIRNominalTypeEnum ntype;

public:
    BSQRef(MIRNominalTypeEnum ntype) : count(0), ntype(ntype) { ; }
    BSQRef(int64_t excount, MIRNominalTypeEnum ntype) : count(excount), ntype(ntype) { ; }
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

    inline static Value checkedIncrement(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(ptr, BSQRef));
        }

        return v;
    }

    inline static void checkedDecrement(Value v)
    {
        if(BSQ_IS_VALUE_PTR(v) & BSQ_IS_VALUE_NONNONE(v))
        {
            BSQRef::decrement(BSQ_GET_VALUE_PTR(ptr, BSQRef));
        }

        return v;
    }

    constexpr static MIRNominalTypeEnum s_stringtype = /*%%NOMINAL_STRING*/MIRNominalTypeEnum::Invalid;
    constexpr static MIRNominalTypeEnum s_tupletype = /*%%NOMINAL_TUPLE*/MIRNominalTypeEnum::Invalid;
    constexpr static MIRNominalTypeEnum s_recordtype = /*%%NOMINAL_RECORD*/MIRNominalTypeEnum::Invalid;
    constexpr static MIRNominalTypeEnum s_arraytype = /*%%NOMINAL_ARRAY*/MIRNominalTypeEnum::Invalid;
    constexpr static MIRNominalTypeEnum s_objecttype = /*%%NOMINAL_OBJECT*/MIRNominalTypeEnum::Invalid;

    inline MIRNominalTypeEnum getNominalType() const
    {
        return this->ntype;
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
    RefCountScope() : opts{nullptr}
    {
        ;
    }

    ~RefCountScope()
    {
        for(size_t i = 0; i < k; ++i)
        {
            BSQRef::decrement(opts[i]);
        }
    }

    template<uint16_t pos>
    inline BSQRef** getCallerSlot() {
        return this->opts + pos; 
    }

    template <uint16_t pos>
    inline void addAllocRef(BSQRef* ptr)
    {
        BSQRef::increment(ptr);
        this->opts[pos] = ptr;
    }
};

class RefCountScopeCallMgr
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
    std::string sdata;

    BSQString(std::string& str) : BSQRef(BSQRef::s_stringtype), sdata(str) { ; }
    BSQString(std::string&& str, int64_t excount) : BSQRef(excount, BSQRef::s_stringtype), sdata(move(str)) { ; }

    virtual ~BSQString() = default;
};

class BSQTuple : public BSQRef
{
public:
    const std::vector<Value> entries;

    BSQTuple(std::vector<Value>&& entries) : BSQRef(BSQRef::s_tupletype), entries(move(entries)) { ; }

    virtual ~BSQTuple()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i])
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

typedef std::vector<Value> BSQTupleFixed;
class BSQTupleFixedOps
{
public:
    template <uint16_t idx>
    inline static Value atFixed(const BSQTupleFixed& tup)
    {
        return (idx < tup.size()) ? tup[idx] : BSQ_VALUE_NONE;
    }

    inline static Value atVar(const BSQTupleFixed& tup, uint16_t idx)
    {
        return (idx < tup.size()) ? tup[idx] : BSQ_VALUE_NONE;
    }
};

class BSQRecord : public BSQRef
{
public:
    const std::vector<std::pair<MIRPropertyEnum, Value>> entries;

    BSQRecord(std::vector<std::pair<MIRPropertyEnum, Value>>&& entries) : BSQRef(BSQRef::s_recordtype), entries(move(entries)) { ; }

    virtual ~BSQRecord()
    {
        for(size_t i = 0; i < this->entries.size(); ++i)
        {
            BSQRef::checkedDecrement(this->entries[i].second)
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
        auto iter = std::find_if(this->entries.cbegin(), this->entries.cend() [p](const std::pair<MIRPropertyEnum, Value>& entry) {
            return entry.first == p;
        });
        return (iter != this->entries.cend()) ? iter->second : BSQ_VALUE_NONE;
    }
};

typedef std::vector<std::pair<MIRPropertyEnum, Value>> BSQRecordFixed;
class BSQRecordFixedOps
{
public:
    template <uint16_t pos, MIRPropertyEnum p>
    inline static Value atKnown(const BSQRecordFixed& rec)
    {
        BSQ_ASSERT(pos >= tup.size() || rec[pos].first == p, "Bad index -- atKnown");
        return (pos < rec.size()) ? rec[pos].second : BSQ_VALUE_NONE;
    }

    template <MIRPropertyEnum p>
    inline static Value atFixed(const BSQRecordFixed& rec)
    {
        auto iter = std::find_if(rec.cbegin(), rec.cend() [](const std::pair<MIRPropertyEnum, Value>& entry) {
            return entry.first == p;
        });
        return (iter != this->entries.cend()) ? iter->second : BSQ_VALUE_NONE;
    }

    inline static Value atVar(const BSQRecordFixed& rec, MIRPropertyEnum p)
    {
        auto iter = std::find_if(rec.cbegin(), rec.cend() [p](const std::pair<MIRPropertyEnum, Value>& entry) {
            return entry.first == p;
        });
        return (iter != this->entries.cend()) ? iter->second : BSQ_VALUE_NONE;
    }
};
} // namespace BSQ
