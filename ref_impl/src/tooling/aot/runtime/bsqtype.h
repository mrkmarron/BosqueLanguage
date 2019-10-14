//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

namespace BSQ
{
//
//Note all of the enums need to be declared in lexographic order
//

enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
    NSCore$cc$None,
    NSCore$cc$Bool,
    NSCore$cc$Int,
    NSCore$cc$String,
    NSCore$cc$Any,
    NSCore$cc$Some,
    NSCore$cc$Truthy,
    NSCore$cc$Parsable,
    NSCore$cc$Tuple,
    NSCore$cc$Record,
    NSCore$cc$Object,
#define NOMINAL_TYPE_ENUM_OP(T) T,
#include "generated/nominaltypes_enum.h"
#undef NOMINAL_TYPE_ENUM_OP
    Limit
};

enum class MIRTypeOptionEnum
{
    Invalid = 0x0,
    NSCore$cc$None,
    NSCore$cc$Bool,
    NSCore$cc$Int,
    NSCore$cc$String,
    NSCore$cc$Any,
    NSCore$cc$Some,
    NSCore$cc$Truthy,
    NSCore$cc$Parsable,
    NSCore$cc$Tuple,
    NSCore$cc$Record,
    NSCore$cc$Object,
#define MIR_TYPE_OPTION_ENUM_OP(T) T,
#include "generated/types_option_enum.h"
#undef MIR_TYPE_OPTION_ENUM_OP
    Limit
};

enum class MIRTypeEnum
{
    Invalid = 0x0,
    NSCore$cc$None,
    NSCore$cc$Bool,
    NSCore$cc$Int,
    NSCore$cc$String,
    NSCore$cc$Any,
    NSCore$cc$Some,
    NSCore$cc$Truthy,
    NSCore$cc$Parsable,
    NSCore$cc$Tuple,
    NSCore$cc$Record,
    NSCore$cc$Object,
#define MIR_TYPE_ENUM_OP(T) T,
#include "generated/types_enum.h"
#undef MIR_TYPE_ENUM_OP
    Limit
};

enum class MIRPropertyEnum
{
    Invalid = 0x0,
#define MIR_PROPERTY_ENUM_OP(T) BSQ_P_##T,
#include "generated/property_enum.h"
#undef MIR_PROPERTY_ENUM_OP
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

    MIRTypeEntity(MIRNominalTypeEnum entityKey) : MIRTypeOption(), entityKey(entityKey) { ; }
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
    const std::vector<std::pair<MIRTypeEnum, bool>> entries;
    const bool isOpen;
    
    MIRTypeTuple(std::vector<std::pair<MIRTypeEnum, bool>>&& entries, bool isOpen) : MIRTypeOption(), entries(move(entries)), isOpen(isOpen) { ; }
    virtual ~MIRTypeTuple() = default;
};

class MIRTypeRecord : public MIRTypeOption
{
public:
    const std::vector<std::pair<MIRPropertyEnum, std::pair<MIRTypeEnum, bool>>> entries;
    const bool isOpen;
    
    MIRTypeRecord(std::vector<std::pair<MIRPropertyEnum, std::pair<MIRTypeEnum, bool>>>&& entries, bool isOpen) : MIRTypeOption(), entries(move(entries)), isOpen(isOpen) { ; }
    virtual ~MIRTypeRecord() = default;
};

class MIRType
{
public:
    const MIRTypeEnum trkey;
    const std::vector<MIRTypeOption*> options;

    MIRType(MIRTypeEnum trkey, MIRTypeOption* topt) : trkey(trkey), options({topt}) { ; }
    MIRType(MIRTypeEnum trkey, std::vector<MIRTypeOption*>&& topts) : trkey(trkey), options(move(topts)) { ; }
};

extern const std::vector<MIRTypeTuple> g_tupleTypes;
extern const std::vector<MIRTypeRecord> g_recordTypes;

extern const std::vector<MIRTypeOption*> g_types_option;
extern const std::vector<MIRType> g_types;

extern const std::set<std::pair<MIRNominalTypeEnum, MIRNominalTypeEnum>> g_nominalSubtypes;
} // namespace BSQ
