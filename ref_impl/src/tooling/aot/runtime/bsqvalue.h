//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqtype.h"

#pragma once

#define BSQ_GET_VALUE_TAG(V) (((uintptr_t)(V).m_data) & 0x7)

#define BSQ_IS_VALUE_NONE(V) ((V).m_data == nullptr)
#define BSQ_IS_VALUE_PTR(V) (BSQ_GET_VALUE_TAG(V) == 0x0)
#define BSQ_IS_VALUE_BOOL(V) (BSQ_GET_VALUE_TAG(V) == 0x2)
#define BSQ_IS_VALUE_INT(V) (BSQ_GET_VALUE_TAG(V) == 0x4)

#define BSQ_GET_VALUE_PTR(T, V) ((T)(V).m_data)
#define BSQ_GET_VALUE_BOOL(V) ((uintptr_t)(V).m_data == 0x3)
#define BSQ_GET_VALUE_INT(V) ((int32_t)(((uintptr_t)(V).m_data) >>4))

#define BSQ_BOX_VALUE_BOOL(B) (void*)(B ? 0x3 : 0x2)
#define BSQ_BOX_VALUE_INT(I) (void*)((((int64_t) I) << 0x4) & 0x4)

#define BSQ_NEEDS_REF_COUNT(V) (((V).m_data != nullptr) & BSQ_IS_VALUE_PTR(V))

namespace BSQ
{
class RefCountBase
{
private:
    int64_t count;

public:
    RefCountBase() : count(1) { ; }
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
    Value(int32_t i) : m_data(BSQ_BOX_VALUE_INT(i)) { ; }
    Value(void* p) : m_data(p) { ; }

    Value(const Value& v)
    {
        if(BSQ_NEEDS_REF_COUNT(v))
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

        if(BSQ_NEEDS_REF_COUNT(v))
        {
            RefCountBase::increment(BSQ_GET_VALUE_PTR(RefCountBase*, v));
        }

        if(BSQ_NEEDS_REF_COUNT(*this))
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

        if(BSQ_NEEDS_REF_COUNT(*this))
        {
            RefCountBase::decrement(BSQ_GET_VALUE_PTR(RefCountBase*, *this));
        }

        this->m_data = v.m_data;
    }

    ~Value()
    {
        if(BSQ_NEEDS_REF_COUNT(*this))
        {
            RefCountBase::decrement(BSQ_GET_VALUE_PTR(RefCountBase*, *this));
        }
        this->m_data = nullptr;
    }

    inline static Value noneValue()
    {
        return Value{};
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
        return Value(0);
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

    inline int32_t getInt() const
    {
        return BSQ_GET_VALUE_INT(*this);
    }

    inline bool isPtr() const
    {
        return BSQ_NEEDS_REF_COUNT(*this);
    }

    template <typename T>
    inline T* getPtr() const
    {
        return BSQ_GET_VALUE_PTR(T*, *this);
    }

    inline bool getTruthy() const
    {
        return BSQ_GET_VALUE_BOOL(*this); //works since none is all 0s
    }

    static bool equality_op(Value lhs, Value rhs);
    static bool compare_op(Value lhs, Value rhs);
};

class AnyValue : RefCountBase
{
public:
    const MIRNominalTypeEnum ntype;

    #define ROOT_VCALLABLE_DECL(NAME, RTYPE, ARGS) virtual RTYPE NAME ARGS = 0;
    #include "generated/vinvoke_decls.h"
    #undef ROOT_VCALLABLE_DECL

    #define ROOT_FIELD_DECL(NAME, FTYPE) FTYPE NAME;
    #include "generated/field_decls.h"
    #undef ROOT_FIELD_DECL

    AnyValue(MIRNominalTypeEnum nt) : ntype(ntype) { ; }
    virtual ~AnyValue() = default;
};

class String : public AnyValue
{
public:
    const std::string m_value;

    String(MIRNominalTypeEnum nt, std::string&& value) : AnyValue(nt), m_value(move(value)) { ; }
    virtual ~String() = default;
};

class StringOf : public AnyValue
{
public:
    const std::string m_value;

    StringOf(MIRNominalTypeEnum nt, std::string&& value) : AnyValue(nt), m_value(move(value)) { ; }
    virtual ~StringOf() = default;
};

class Tuple : public AnyValue
{
public:
    const std::vector<Value> m_entries;

    Tuple(MIRNominalTypeEnum nt, std::vector<Value>&& entries) : AnyValue(nt), m_entries(move(entries)) { ; }
    virtual ~Tuple() = default;
};

class Record : public AnyValue
{
public:
    const std::vector<std::pair<MIRPropertyEnum, Value>> m_entries;

    Record(MIRNominalTypeEnum nt, std::vector<std::pair<MIRPropertyEnum, Value>>&& entries) : AnyValue(nt), m_entries(move(entries)) { ; }
    virtual ~Record() = default;
};

class Entity : public AnyValue
{
public:
    Entity(MIRNominalTypeEnum nt) : AnyValue(nt) { ; }
    virtual ~Entity() = default;
};

class ListCollection : public Entity
{
public:
    const std::vector<Value> m_entries;

    ListCollection(MIRNominalTypeEnum nt, std::vector<Value>&& entries) : Entity(nt), m_entries(entries) { ; }
    virtual ~ListCollection() = default;
};

//
//TODO: HashSet and HashMap collections here
//
} // namespace BSQ
