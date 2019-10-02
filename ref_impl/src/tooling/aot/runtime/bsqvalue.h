//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

namespace BSQ
{
class Value
{
protected:
    const std::string m_type;

public:
    Value(const std::string& vtype) : m_type(vtype) { ; }
    virtual ~Value() = default;

    const std::string& getType() const { return this->m_type; }
};

class Tuple : public Value
{
protected:
    const std::vector<Value> m_entries;

public:
    Tuple(const std::string& vtype, const std::vector<Value>& entries) : Value(vtype), m_entries(entries) { ; }
    virtual ~Tuple() = default;

    const std::vector<Value>& getEntries() const { return this->m_entries; }
};

class Record : public Value
{
protected:
    const std::unordered_map<std::string, Value> m_entries;

public:
    Record(const std::string& vtype, const std::unordered_map<std::string, Value>& entries) : Value(vtype), m_entries(entries) { ; }
    virtual ~Record() = default;

    const std::unordered_map<std::string, Value>& getEntries() const { return this->m_entries; }
};

class Entity : public Value
{
public:
    Entity(const std::string& vtype) : Value(vtype) { ; }
    virtual ~Entity() = default;
};

class SimpleEntity : public Entity
{
private:
    const std::unordered_map<std::string, Value> m_fields;

    SimpleEntity(const std::string& vtype, const std::unordered_map<std::string, Value>& fields) : Entity(vtype), m_fields(fields) { ; }
    virtual ~SimpleEntity() = default;

    const std::unordered_map<std::string, Value>& getFields() const { return this->m_fields; }
};

class ListCollection
{

};

class HashSetCollection
{

};

class HashMapCollection
{

};

typedef void* InlineNoneType;
typedef bool InlineBoolType;
typedef int64_t InlineIntType;

template<uint8_t k>
class InlineTuple
{
public:
    Value entries[k];
};

template<uint8_t k>
class InlineRecord
{
xxxx;
};

} // namespace BSQ
