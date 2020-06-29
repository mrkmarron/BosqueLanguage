//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <cstdint>
#include <string>

//Note POD => API
typedef uint32_t DATA_KIND_FLAG;
#define DATA_KIND_CLEAR_FLAG 0x0
#define DATA_KIND_API_FLAG 0x1
#define DATA_KIND_POD_FLAG 0x3
#define DATA_KIND_PARSABLE_FLAG 0x4
#define DATA_KIND_ALL_FLAG (DATA_KIND_API_FLAG | DATA_KIND_POD_FLAG | DATA_KIND_PARSABLE_FLAG)
#define DATA_KIND_UNKNOWN_FLAG 0xFF

#define DATA_KIND_COMPUTE(KF, COMP) (((KF) == DATA_KIND_UNKNOWN_FLAG) ? (COMP) : (KF)

#define PTR_FIELD_MASK_SCALAR (char)1
#define PTR_FIELD_MASK_PTR (char)2
#define PTR_FIELD_MASK_UNION (char)4
#define PTR_FIELD_MASK_END (char)0

#define META_DATA_LOAD_DECL(X) const_cast<MetaData*>(&(X))

#define META_DATA_DECLARE_NO_PTR(NAME, TYPE, FLAG, SIZE, CUNIONFP, DISPLAY) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, 0, nullptr, Allocator::MetaData_ComputeSize_Simple, nullptr, nullptr, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, false }
#define META_DATA_DECLARE_NO_PTR_KEY(NAME, TYPE, FLAG, SIZE, LESSFP, EQFP, CUNIONFP, DISPLAY) constexpr MetaData NAME = MetaData{ TYPE, FLAG, SIZE, -1, -1, 0, nullptr, Allocator::MetaData_ComputeSize_Simple, LESSFP, EQFP, CUNIONFP, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, Allocator::MetaData_GCOperatorFP_NoRefs, DISPLAY, false }


namespace BSQ
{
enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE%%
};

class MetaData;
typedef const char* RefMask;

typedef size_t (*MemSizeFP)(const MetaData*, void*);

typedef bool (*MetaData_RelationalOpFP)(void*, void*);

typedef void* (*MetaData_UnionOperatorFP)(void*);

typedef void (*MetaData_GCDecOperatorFP)(const MetaData*, void**);
typedef void (*MetaData_GCClearMarkOperatorFP)(const MetaData*, void**);
typedef void (*MetaData_GCProcessOperatorFP)(const MetaData*, void**);

typedef std::wstring (*MetaData_DisplayFP)(void* obj);

class MetaData
{
public:
    MIRNominalTypeEnum nominaltype;
    uint32_t dataflag;

    uint32_t datasize; //size of the object in it's raw state (excluding any headers)
    int32_t sizeentry; //if this is a container then this is the size of each contained element (-1) if not a container
    int32_t sizeadvance; //if this is a container then this is the size (in void* increments) that each entry represents

    uint32_t ptrcount; //if this is a simple packed layout (or contents are simple packed layouts) then this is the number of pointers
    RefMask refmask; //if this is a mixed layout (or contents are mixed layouts) then this is the mask to use

    MemSizeFP computeMemorySize;

    //Less and Equal operations for the object when it is in boxed form (or null if they are not supported)
    MetaData_RelationalOpFP less;
    MetaData_RelationalOpFP eq;

    //inject and extract from union representations
    MetaData_UnionOperatorFP coerceUnionToBox;

    //How to do gc ops on the object
    MetaData_GCDecOperatorFP decObj;
    MetaData_GCClearMarkOperatorFP clearObj;
    MetaData_GCProcessOperatorFP processObjRoot;
    MetaData_GCProcessOperatorFP processObjHeap;

    //display function pointer
    MetaData_DisplayFP displayFP;

    //true if this may have reference fields that need to be processed
    bool hasRefs;

    template <bool isRoot>
    inline MetaData_GCProcessOperatorFP getProcessFP() const
    {
        return nullptr;
    }

    template <>
    inline MetaData_GCProcessOperatorFP getProcessFP<true>() const
    {
        return this->processObjRoot;
    }

    template <>
    inline MetaData_GCProcessOperatorFP getProcessFP<false>() const
    {
        return this->processObjHeap;
    }
};

//%%METADATA_STRUCT_DECLS%%
}

//%%SPECIAL_NAME_BLOCK_BEGIN%%
#define MIRNominalTypeEnum_None MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Bool MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Int MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_BigInt MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Float64 MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_String MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_UUID MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_LogicalTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_CryptoHash MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ByteBuffer MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_ISOTime MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Regex MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Tuple MIRNominalTypeEnum::Invalid
#define MIRNominalTypeEnum_Record MIRNominalTypeEnum::Invalid
//%%SPECIAL_NAME_BLOCK_END%%
