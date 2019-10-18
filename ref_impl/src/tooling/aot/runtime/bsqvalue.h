//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

#define BSQ_IS_VALUE_NONE(V) ((uintptr_t)((V).m_data) == 0x1)
#define BSQ_IS_VALUE_BOOL(V) ((uintptr_t)((V).m_data) & 0x2 == 0x2)
#define BSQ_IS_VALUE_INT(V) ((uintptr_t)((V).m_data) & 0x4 == 0x4)
#define BSQ_IS_VALUE_PTR(V) ((uintptr_t)((V).m_data) > 0x7)

#define BSQ_GET_VALUE_PTR(T, V) ((T)((V).m_data))
#define BSQ_GET_VALUE_BOOL(V) ((uintptr_t)((V).m_data) == 0x2)
#define BSQ_GET_VALUE_INT(V) ((int64_t)((uintptr_t)((V).m_data) >> 4))

#define BSQ_BOX_VALUE_BOOL(B) (void*)(0x2 & (uintptr_t)(!B))
#define BSQ_BOX_VALUE_INT(I) (void*)((((int64_t) I) << 0x4) & 0x4)

#define BSQ_GET_VALUE_TRUTHY(V) ((uintptr_t)((V).m_data) & 0x1 == 0x0)

#define BINT_MAX 4503599627370495
#define BINT_MIN (-4503599627370496)

namespace BSQ
{
enum class MIRPropertyEnum
{
    Invalid = 0,
//%%PROPERTY_ENUM_DECLARE
};

class RefCountBase
{
private:
    int64_t count;

public:
    RefCountBase() : count(0) { ; }
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

template <typename T>
class ValueOf
{
private:
    T* m_data;

public:
    ValueOf() : m_data(nullptr) { ; }
    ValueOf(T* v) : m_data(v) { RefCountBase::increment((RefCountBase*)v); }

    ValueOf(const ValueOf<T>& v)
    {
        RefCountBase::increment(v.m_data);
        this->m_data = v.m_data;
    }

    ValueOf<T>& operator=(const ValueOf<T>& v)
    {
        if(this == &v)
        {
            return *this;
        }

        if(v.m_data != nullptr)
        {
            RefCountBase::increment(v.m_data);
        }

        if(this->m_data != nullptr)
        {
            RefCountBase::decrement(this->m_data);
        }

        this->m_data = v.m_data;
    }
    
    ValueOf(ValueOf<T>&& v)
    {
        this->m_data = v.m_data;
        v.m_data = nullptr;
    }

    ValueOf<T>& operator=(ValueOf<T>&& v)
    {
        if(this == &v)
        {
            return *this;
        }
 
        if(this->m_data != nullptr)
        {
            RefCountBase::decrement(this->m_data);
        }

        this->m_data = v.m_data;
        v.m_data = nullptr;
    }

    ~ValueOf()
    {
        if(this->m_data != nullptr)
        {
            RefCountBase::decrement(this->m_data);
        }

        this->m_data = nullptr;
    }

    inline T* getPtr() const
    {
        return this->m_data;
    }
};

class Value
{
private:
    void* m_data;

public:
    Value() : m_data(nullptr) 
    { 
        ; 
    }

    Value(bool b) : m_data(BSQ_BOX_VALUE_BOOL(b)) { ; }
    Value(int64_t i) : m_data(BSQ_BOX_VALUE_INT(i)) { ; }
    Value(void* p) : m_data(p) { RefCountBase::increment((RefCountBase*)p); }

    template <typename T>
    Value(const ValueOf<T>& v)
    {
        if(v.getPtr() != nullptr)
        {
            RefCountBase::increment(v.getPtr());
        }

        this->m_data = v.getPtr();
    }

    Value(const Value& v)
    {
        if(BSQ_IS_VALUE_PTR(v))
        {
            RefCountBase::increment(BSQ_GET_VALUE_PTR(RefCountBase*, v));
        }

        this->m_data = v.m_data;
    }

    Value& operator=(const Value& v)
    {
        if(this == &v)
        {
            return *this;
        }

        if(BSQ_IS_VALUE_PTR(v))
        {
            RefCountBase::increment(BSQ_GET_VALUE_PTR(RefCountBase*, v));
        }

        if(BSQ_IS_VALUE_PTR(*this))
        {
            RefCountBase::decrement(BSQ_GET_VALUE_PTR(RefCountBase*, *this));
        }

        this->m_data = v.m_data;
    }
    
    Value(Value&& v)
    {
        this->m_data = v.m_data;
        v.m_data = nullptr;
    }

    Value& operator=(Value&& v)
    {
        if(this == &v)
        {
            return *this;
        }

        if(BSQ_IS_VALUE_PTR(*this))
        {
            RefCountBase::decrement(BSQ_GET_VALUE_PTR(RefCountBase*, *this));
        }

        this->m_data = v.m_data;
        v.m_data = nullptr;
    }

    ~Value()
    {
        if(BSQ_IS_VALUE_PTR(*this))
        {
            RefCountBase::decrement(BSQ_GET_VALUE_PTR(RefCountBase*, *this));
            this->m_data = nullptr;
        }
    }

    inline static Value noneValue()
    {
        return Value((void*)0x1);
    }

    inline static Value falseValue()
    {
        return Value(false);
    }

    inline static Value trueValue()
    {
        return Value(true);
    }

    inline Value zeroValue() const
    {
        return Value((int64_t)0);
    }

    inline bool isNone() const
    {
        return BSQ_IS_VALUE_NONE(*this);
    }

    inline bool isBool() const
    {
        return BSQ_IS_VALUE_BOOL(*this);
    }

    inline bool getBool() const
    {
        return BSQ_GET_VALUE_BOOL(*this);
    }

    inline bool isInt() const
    {
        return BSQ_IS_VALUE_INT(*this);
    }

    inline int64_t getInt() const
    {
        return BSQ_GET_VALUE_INT(*this);
    }

    inline bool isPtr() const
    {
        return BSQ_IS_VALUE_PTR(*this);
    }

    template <typename T>
    inline T* getPtr() const
    {
        return BSQ_GET_VALUE_PTR(T*, *this);
    }

    inline bool getTruthy() const
    {
        return BSQ_GET_VALUE_TRUTHY(*this);
    }

    static bool equality_op(Value lhs, Value rhs);
    static bool compare_op(Value lhs, Value rhs);
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
    NSCore$cc$String(std::string&& str) : sdata(move(str)) { ; }

    virtual ~NSCore$cc$String() = default;
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
