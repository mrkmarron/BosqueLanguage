//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqtype.h"

#pragma once

namespace BSQ
{
class HeapValue
{
public:
    const MIRNominalTypeEnum ntype;

    #define ROOT_VCALLABLE_DECL(NAME, RTYPE, ARGS) virtual RTYPE NAME ARGS = 0;
    #include "generated/vinvoke_decls.h"
    #undef ROOT_VCALLABLE_DECL

    #define ROOT_FIELD_DECL(NAME, FTYPE) FTYPE NAME;
    #include "generated/field_decls.h"
    #undef ROOT_FIELD_DECL

    HeapValue(MIRNominalTypeEnum nt) : ntype(ntype) { ; }
    virtual ~HeapValue() = default;
};

class BoxedNone : public HeapValue
{
public:
    BoxedNone() : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$None) { ; }
    virtual ~BoxedNone() = default;
};

class BoxedBool : public HeapValue
{
public:
    const bool m_value;

    BoxedBool(bool value) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$Bool), m_value(value) { ; }
    virtual ~BoxedBool() = default;
};

class BoxedInt : public HeapValue
{
public:
    const int64_t m_value;

    BoxedInt(int64_t value) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$Int), m_value(value) { ; }
    virtual ~BoxedInt() = default;
};

class String : public HeapValue
{
public:
    const std::string m_value;

    String(std::string&& value) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$String), m_value(move(value)) { ; }
    virtual ~String() = default;
};

class Float : public HeapValue
{
public:
    const double m_value;

    Float(double value) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$Float), m_value(value) { ; }
    virtual ~Float() = default;
};

class StringOf : public HeapValue
{
public:
    const std::string m_value;

    StringOf(MIRNominalTypeEnum nt, std::string&& value) : HeapValue(nt), m_value(move(value)) { ; }
    virtual ~StringOf() = default;
};

class Tuple : public HeapValue
{
public:
    const std::vector<std::shared_ptr<HeapValue>> m_entries;

    Tuple(std::vector<std::shared_ptr<HeapValue>>&& entries) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$Tuple), m_entries(move(entries)) { ; }
    virtual ~Tuple() = default;
};

class Record : public HeapValue
{
public:
    const std::unordered_map<std::string, std::shared_ptr<HeapValue>> m_entries;

    Record(std::unordered_map<std::string, std::shared_ptr<HeapValue>>&& entries) : HeapValue(MIRNominalTypeEnum::BSQ_N_NSCore$cc$Record), m_entries(move(entries)) { ; }
    virtual ~Record() = default;
};

class Entity : public HeapValue
{
public:
    Entity(MIRNominalTypeEnum nt) : HeapValue(nt) { ; }
    virtual ~Entity() = default;
};

class SimpleEntity : public Entity
{
public:
    const std::unordered_map<std::string, std::shared_ptr<HeapValue>> m_fields;

    SimpleEntity(MIRNominalTypeEnum nt, std::unordered_map<std::string, std::shared_ptr<HeapValue>>&& fields) : Entity(nt), m_fields(move(fields)) { ; }
    virtual ~SimpleEntity() = default;
};

class ListCollection : public Entity
{
public:
    const std::vector<std::shared_ptr<HeapValue>> m_entries;

    ListCollection(MIRNominalTypeEnum nt, std::vector<std::shared_ptr<HeapValue>>&& entries) : Entity(nt), m_entries(entries) { ; }
    virtual ~ListCollection() = default;
};

//
//TODO: HashSet and HashMap collections here
//

typedef void* InlineNoneType;
typedef bool InlineBoolType;
typedef int64_t InlineIntType;
} // namespace BSQ
