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

enum class BSQRepr
{
    Invalid = 0x0,
    ReprNone,
    ReprBool,
    ReprInt,
    ReprString,
    ReprStringOf,
    ReprTuple,
    ReprRecord,
    ReprEnum,
    ReprIdKey,
    ReprKeyed,
    ReprTagged,
    ReprObject,
    //Extra compared to SMT since we need to use efficient encoding not slow rec version
    ReprList,
    ReprHashSet,
    ReprHashMap
};

typedef void* Value;

class BSQRef
{
private:
    int64_t count;
    const BSQRepr representation;

public:
    BSQRef(BSQRepr representation) : count(0), representation(representation) { ; }
    BSQRef(int64_t excount, BSQRepr representation) : count(excount), representation(representation) { ; }
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

    inline BSQRepr getRepr() const
    {
        return this->representation;
    }
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
            BSQRef::increment(BSQ_GET_VALUE_PTR(ptr, RefCountBase));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, RefCountBase);
        }
    }

    inline static void processCallRefAny(BSQRef** callerslot, Value ptr)
    {
        if(BSQ_IS_VALUE_PTR(ptr) & BSQ_IS_VALUE_NONNONE(ptr))
        {
            BSQRef::increment(BSQ_GET_VALUE_PTR(ptr, RefCountBase));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, RefCountBase);
        }
    }
};

class BSQString : public BSQRef
{
public:
    std::string sdata;

    BSQString(std::string& str) : BSQRef(BSQRepr::ReprString), sdata(str) { ; }
    BSQString(std::string&& str, int64_t excount) : BSQRef(excount, BSQRepr::ReprString), sdata(move(str)) { ; }

    virtual ~BSQString() = default;
};

class NSCore$cc$StringOf : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    NSCore$cc$StringOf() = default;
    virtual ~NSCore$cc$StringOf() = default;

    virtual const char* getTypeOfName() const = 0;
    virtual NSCore$cc$String* getString() const = 0;
};

class NSCore$cc$Tuple : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    const std::vector<Value> m_entries;

    NSCore$cc$Tuple(std::vector<Value>&& entries) : m_entries(move(entries)) { ; }
    virtual ~NSCore$cc$Tuple() = default;
};

class NSCore$cc$Record : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    const std::vector<std::pair<MIRPropertyEnum, Value>> m_entries;

    NSCore$cc$Record(std::vector<std::pair<MIRPropertyEnum, Value>>&& entries) : m_entries(move(entries)) { ; }
    virtual ~NSCore$cc$Record() = default;
};

class NSCore$cc$Object : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    NSCore$cc$Object() = default;
    virtual ~NSCore$cc$Object() = default;
};
} // namespace BSQ
