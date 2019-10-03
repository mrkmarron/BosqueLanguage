//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

namespace BSQ
{
class HeapValue;
typedef void (*VCall)(std::shared_ptr<HeapValue> rcvr, ...);

class VTable
{
public:
    const std::string m_type;
    const std::unordered_map<std::string, VCall> m_vmap;

    VTable(std::string&& type, std::unordered_map<std::string, VCall>&& vmap) : m_type(move(type)), m_vmap(move(vmap)) { ; }
    ~VTable() = default;
};

class HeapValue
{
public:
    const VTable* m_vtable;

    HeapValue(const VTable* vtable) : m_vtable(vtable) { ; }
    virtual ~HeapValue() = default;
};

class BoxedNone : public HeapValue
{
public:
    BoxedNone(const VTable* vtable) : HeapValue(vtable) { ; }
    virtual ~BoxedNone() = default;
};

class BoxedBool : public HeapValue
{
public:
    const bool m_value;

    BoxedBool(const VTable* vtable, bool value) : HeapValue(vtable), m_value(value) { ; }
    virtual ~BoxedBool() = default;
};

class BoxedInt : public HeapValue
{
public:
    const int64_t m_value;

    BoxedInt(const VTable* vtable, int64_t value) : HeapValue(vtable), m_value(value) { ; }
    virtual ~BoxedInt() = default;
};

class String : public HeapValue
{
public:
    const std::string m_value;

    String(const VTable* vtable, std::string&& value) : HeapValue(vtable), m_value(move(value)) { ; }
    virtual ~String() = default;
};

class Float : public HeapValue
{
public:
    const double m_value;

    Float(const VTable* vtable, double value) : HeapValue(vtable), m_value(value) { ; }
    virtual ~Float() = default;
};

class StringOf : public HeapValue
{
public:
    const std::string m_value;

    StringOf(const VTable* vtable, std::string&& value) : HeapValue(vtable), m_value(move(value)) { ; }
    virtual ~StringOf() = default;
};

class Tuple : public HeapValue
{
public:
    const std::vector<std::shared_ptr<HeapValue>> m_entries;

    Tuple(const VTable* vtable, std::vector<std::shared_ptr<HeapValue>>&& entries) : HeapValue(vtable), m_entries(move(entries)) { ; }
    virtual ~Tuple() = default;
};

class Record : public HeapValue
{
public:
    const std::unordered_map<std::string, std::shared_ptr<HeapValue>> m_entries;

    Record(const VTable* vtable, std::unordered_map<std::string, std::shared_ptr<HeapValue>>&& entries) : HeapValue(vtable), m_entries(move(entries)) { ; }
    virtual ~Record() = default;
};

class Entity : public HeapValue
{
public:
    Entity(const VTable* vtable) : HeapValue(vtable) { ; }
    virtual ~Entity() = default;
};

class SimpleEntity : public Entity
{
public:
    const std::unordered_map<std::string, std::shared_ptr<HeapValue>> m_fields;

    SimpleEntity(const VTable* vtable, std::unordered_map<std::string, std::shared_ptr<HeapValue>>&& fields) : Entity(vtable), m_fields(move(fields)) { ; }
    virtual ~SimpleEntity() = default;
};

class ListCollection : public Entity
{
public:
    const std::vector<std::shared_ptr<HeapValue>> m_entries;

    ListCollection(const VTable* vtable, std::vector<std::shared_ptr<HeapValue>>&& entries) : Entity(vtable), m_entries(entries) { ; }
    virtual ~ListCollection() = default;
};

//
//TODO: HashSet and HashMap collections here
//

typedef void* InlineNoneType;
typedef bool InlineBoolType;
typedef int64_t InlineIntType;
} // namespace BSQ
