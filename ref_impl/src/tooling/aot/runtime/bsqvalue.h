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

typedef void* Value;

class RefCountBase
{
private:
    int64_t count;

public:
    RefCountBase() : count(0) { ; }
    RefCountBase(int64_t excount) : count(excount) { ; }
    virtual ~RefCountBase() { ; }

    inline static void increment(RefCountBase* rcb)
    {
        rcb->count++;
    }

    inline static void decrement(RefCountBase* rcb)
    {
        rcb->count--;

        if(rcb->count == 0)
        {
            delete rcb;    
        }
    }
};

template <uint16_t k>
class RefCountScope
{
private:
    RefCountBase* opts[k];

public:
    RefCountScope() : opts{nullptr}
    {
        ;
    }

    ~RefCountScope()
    {
        for(size_t i = 0; i < k; ++i)
        {
            RefCountBase::decrement(opts[i]);
        }
    }

    template<uint16_t pos>
    inline RefCountBase** getCallerSlot() {
        return this->opts + pos; 
    }

    template <uint16_t pos>
    inline void addAllocRef(RefCountBase* ptr)
    {
        RefCountBase::increment(ptr);
        this->opts[pos] = ptr;
    }
};

class RefCountScopeCallMgr
{
public:
    inline static void processCallReturnFast(RefCountBase** callerslot, RefCountBase* ptr)
    {
        RefCountBase::increment(ptr);
        *callerslot = ptr;
    }

    inline static void processCallRefNoneable(RefCountBase** callerslot, Value ptr)
    {
        if(BSQ_IS_VALUE_NONNONE(ptr))
        {
            RefCountBase::increment(BSQ_GET_VALUE_PTR(ptr, RefCountBase));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, RefCountBase);
        }
    }

    inline static void processCallRefAny(RefCountBase** callerslot, Value ptr)
    {
        if(BSQ_IS_VALUE_PTR(ptr) & BSQ_IS_VALUE_NONNONE(ptr))
        {
            RefCountBase::increment(BSQ_GET_VALUE_PTR(ptr, RefCountBase));
            *callerslot = BSQ_GET_VALUE_PTR(ptr, RefCountBase);
        }
    }
};

class NSCore$cc$Any
{
public:
    NSCore$cc$Any() = default;
    virtual ~NSCore$cc$Any() = default;
};

class NSCore$cc$Some : virtual public NSCore$cc$Any
{
public:
    NSCore$cc$Some() = default;
    virtual ~NSCore$cc$Some() = default;
};

class NSCore$cc$Truthy : virtual public NSCore$cc$Any
{
public:
    NSCore$cc$Truthy() = default;
    virtual ~NSCore$cc$Truthy() = default;
};

class NSCore$cc$None : public RefCountBase, virtual public NSCore$cc$Truthy
{
public:
    NSCore$cc$None() = default;
    virtual ~NSCore$cc$None() = default;
};

class NSCore$cc$Parsable : virtual public NSCore$cc$Some
{
public:
    NSCore$cc$Parsable() = default;
    virtual ~NSCore$cc$Parsable() = default;
};

class NSCore$cc$Bool : public RefCountBase, virtual public NSCore$cc$Parsable, virtual public NSCore$cc$Truthy
{
public:
    NSCore$cc$Bool() = default;
    virtual ~NSCore$cc$Bool() = default;
};

class NSCore$cc$Int : public RefCountBase, virtual public NSCore$cc$Parsable
{
public:
    NSCore$cc$Int() = default;
    virtual ~NSCore$cc$Int() = default;
};

class NSCore$cc$String : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    std::string sdata;

    NSCore$cc$String(std::string& str) : sdata(str) { ; }
    NSCore$cc$String(std::string&& str, int64_t excount) : RefCountBase(excount), sdata(move(str)) { ; }

    virtual ~NSCore$cc$String() = default;
};

class NSCore$cc$StringOf : public RefCountBase, virtual public NSCore$cc$Some
{
public:
    NSCore$cc$String* bstr;

    NSCore$cc$StringOf(NSCore$cc$String* str) : bstr(str) { RefCountBase::increment(str); }
    virtual ~NSCore$cc$StringOf() { RefCountBase::decrement(this->bstr); }

    virtual const char* getTypeOfName() const = 0;
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
