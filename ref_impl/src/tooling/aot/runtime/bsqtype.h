//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

namespace BSQ
{
enum class MIRNominalTypeEnum
{
    Invalid,
#define NOMINAL_TYPE_ENUM_OP(T) BSQ_N_##T,
#include "generated/nominaltypes_enum.h"
#undef NOMINAL_TYPE_ENUM_OP
    Limit
};

enum class MIRTypeEnum
{
    Invalid,
#define MIR_TYPE_ENUM_OP(T) BSQ_T_##T,
#include "generated/types_enum.h"
#undef MIR_TYPE_ENUM_OP
    Limit
};

enum class MIRPropertyEnum
{
    Invalid,
#define MIR_PROPERTY_ENUM_OP(T) BSQ_P_##T,
#include "generated/property_enum.h"
#undef MIR_PROPERTY_ENUM_OP
    Limit
};

enum class MIRFieldEnum
{
    Invalid,
#define MIR_FIELD_ENUM_OP(T) BSQ_F_##T,
#include "generated/field_enum.h"
#undef MIR_FIELD_ENUM_OP
    Limit
};

enum class MIRInvokeEnum
{
    Invalid,
#define MIR_INVOKE_ENUM_OP(T) BSQ_I_##T,
#include "generated/invoke_enum.h"
#undef MIR_INVOKE_ENUM_OP
    Limit
};

enum class MIRVInvokeEnum
{
    Invalid,
#define MIR_VINVOKE_ENUM_OP(T) BSQ_VI_##T,
#include "generated/vinvoke_enum.h"
#undef MIR_VINVOKE_ENUM_OP
    Limit
};

class MIRType;

class MIRTypeOption
{
public:
    MIRTypeOption() { ; }
    virtual ~MIRTypeOption() = default;
};

class MIRTypeEntity : public MIRTypeOption
{
public:
    const MIRNominalTypeEnum entityKey;

    MIRTypeEntity(const MIRNominalTypeEnum entityKey) : MIRTypeOption(), entityKey(entityKey) { ; }
    virtual ~MIRTypeEntity() = default;
};

class MIRTypeConcept : public MIRTypeOption
{
public:
    const std::vector<MIRNominalTypeEnum> conceptKeys;

    MIRTypeConcept(std::vector<MIRNominalTypeEnum>&& conceptKeys) : MIRTypeOption(), conceptKeys(move(conceptKeys)) { ; }
    virtual ~MIRTypeConcept() = default;
};

class MIRTypeTuple : public MIRTypeOption
{
public:
    const std::vector<std::pair<MIRType*, bool>> entries;
    const bool isOpen;
    
    MIRTypeTuple(std::vector<std::pair<MIRType*, bool>>&& entries, bool isOpen) : MIRTypeOption(), entries(move(entries)), isOpen(isOpen) { ; }
    virtual ~MIRTypeTuple() = default;
};

class MIRTypeRecord : public MIRTypeOption
{
public:
    const std::vector<std::pair<std::string, std::pair<MIRType*, bool>>> entries;
    const bool isOpen;
    
    MIRTypeRecord(std::vector<std::pair<std::string, std::pair<MIRType*, bool>>>&& entries, bool isOpen) : MIRTypeOption(), entries(move(entries)), isOpen(isOpen) { ; }
    virtual ~MIRTypeRecord() = default;
};

class MIRType
{
public:
    const MIRTypeEnum trkey;
    const std::vector<MIRTypeOption*> options;
};
} // namespace BSQ
