//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

namespace BSQ
{
class MIRType;

class MIRTypeOption
{
public:
    const std::string trkey;

    MIRTypeOption(const std::string& trkey) : trkey(trkey) { ; }
    virtual ~MIRTypeOption() = default;
};

class MIRTypeEntity : public MIRTypeOption
{
public:
    const std::string entityKey;

    MIRTypeEntity(const std::string& trkey, const std::string& entityKey) : MIRTypeOption(trkey), entityKey(entityKey) { ; }
    virtual ~MIRTypeEntity() = default;
};

class MIRTypeConcept : public MIRTypeOption
{
public:
    const std::vector<std::string> conceptKeys;

    MIRTypeConcept(const std::string& trkey, const std::vector<std::string>& conceptKeys) : MIRTypeOption(trkey), conceptKeys(conceptKeys) { ; }
    virtual ~MIRTypeConcept() = default;
};

class MIRTypeTuple : public MIRTypeOption
{
public:
    const std::vector<std::pair<MIRType*, bool>> entries;
    const bool isOpen;
    
    MIRTypeTuple(const std::string& trkey, const std::vector<std::pair<MIRType*, bool>>& entries, bool isOpen) : MIRTypeOption(trkey), entries(entries), isOpen(isOpen) { ; }
    virtual ~MIRTypeTuple() = default;
};

class MIRTypeRecord : public MIRTypeOption
{
public:
    const std::map<std::string, std::pair<MIRType*, bool>> entries;
    const bool isOpen;
    
    MIRTypeRecord(const std::string& trkey, const std::map<std::string, std::pair<MIRType*, bool>>& entries, bool isOpen) : MIRTypeOption(trkey), entries(entries), isOpen(isOpen) { ; }
    virtual ~MIRTypeRecord() = default;
};

class MIRType
{
public:
    const std::string trkey;
    const std::vector<std::string> options;
};

class RuntimeType
{
public:
    RuntimeType() = default;
    virtual ~RuntimeType() = default;
};

class RuntimeEntityType : public RuntimeType
{
public:
    const MIRTypeEntity* entity;

    RuntimeEntityType(MIRTypeEntity* entity) : entity(entity) { ; }
    virtual ~RuntimeEntityType() = default;
};

class RuntimeTupleType : public RuntimeType
{
    const std::vector<RuntimeType*> entries;
    
    RuntimeTupleType(const std::vector<RuntimeType*>& entries) : entries(entries) { ; }
    virtual ~RuntimeTupleType() = default;
};

class RuntimeRecordType : public RuntimeType
{
    const std::vector<std::pair<std::string, RuntimeType*>> entries;
    
    RuntimeRecordType(const std::vector<std::pair<std::string, RuntimeType*>>& entries) : entries(entries) { ; }
    virtual ~RuntimeRecordType() = default;
};

class RuntimeTypeEnvironment
{
private:
    std::map<std::string, MIRType*> mirTypeMap;

    std::map<std::string, RuntimeEntityType*> runtimeEntityTypeMap;
    std::map<RuntimeType*, std::map<RuntimeType*, RuntimeType*>> tupleExtensionMap;
    std::map<RuntimeType*, std::map<std::pair<std::string, RuntimeType*>, RuntimeType*>> recordExtensionMap;

    RuntimeType* noneType;
    RuntimeType* boolType;
    RuntimeType* intType;
    RuntimeType* stringType;
    RuntimeType* floatType;

    RuntimeType* emptyTupleType;
    RuntimeType* emptyRecordType;

    std::vector<RuntimeType*> allRuntimeTypes;

public:
    const RuntimeType* getNoneType() const { return this->noneType; }
    const RuntimeType* getBoolType() const { return this->boolType; }
    const RuntimeType* getIntType() const { return this->intType; }
    const RuntimeType* getStringType() const { return this->stringType; }
    const RuntimeType* getFloatType() const { return this->floatType; }

    const RuntimeType* getEmptyTupleType() const { return this->emptyTupleType; }
    const RuntimeType* getEmptyRecordType() const { return this->emptyRecordType; }
};

extern RuntimeTypeEnvironment s_typeenv;
} // namespace BSQ
