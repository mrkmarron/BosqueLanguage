//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <cstdint>

//Note POD => API
typedef uint32_t DATA_KIND_FLAG;
#define DATA_KIND_CLEAR_FLAG 0x0
#define DATA_KIND_API_FLAG 0x1
#define DATA_KIND_POD_FLAG 0x3
#define DATA_KIND_PARSABLE_FLAG 0x4
#define DATA_KIND_ALL_FLAG (DATA_KIND_API_FLAG | DATA_KIND_POD_FLAG | DATA_KIND_PARSABLE_FLAG)
#define DATA_KIND_UNKNOWN_FLAG 0xFF

#define DATA_KIND_COMPUTE(KF, COMP) (((KF) == DATA_KIND_UNKNOWN_FLAG) ? (COMP) : (KF)

//Category tags to embed in the type enums
#define MIRNominalTypeEnum_Category_Empty           0
#define MIRNominalTypeEnum_Category_BigInt          1
#define MIRNominalTypeEnum_Category_String          2
#define MIRNominalTypeEnum_Category_SafeString      3
#define MIRNominalTypeEnum_Category_StringOf        4
#define MIRNominalTypeEnum_Category_UUID            5
#define MIRNominalTypeEnum_Category_LogicalTime     6
#define MIRNominalTypeEnum_Category_CryptoHash      7
#define MIRNominalTypeEnum_Category_Enum            8
#define MIRNominalTypeEnum_Category_IdKeySimple     9
#define MIRNominalTypeEnum_Category_IdKeyCompound   10

#define MIRNominalTypeEnum_Category_KeyTypeLimit    MIRNominalTypeEnum_Category_IdKeyCompound

#define MIRNominalTypeEnum_Category_Float64         20
#define MIRNominalTypeEnum_Category_Buffer          21
#define MIRNominalTypeEnum_Category_BufferOf        22
#define MIRNominalTypeEnum_Category_ByteBuffer      23
#define MIRNominalTypeEnum_Category_ISOTime         24
#define MIRNominalTypeEnum_Category_Regex           25
#define MIRNominalTypeEnum_Category_Tuple           26
#define MIRNominalTypeEnum_Category_Record          27
#define MIRNominalTypeEnum_Category_Object          28

#define MIRNominalTypeEnum_Category_NormalTypeLimit MIRNominalTypeEnum_Category_Object

#define MIRNominalTypeEnum_Category_List            40
#define MIRNominalTypeEnum_Category_Stack           41
#define MIRNominalTypeEnum_Category_Queue           42
#define MIRNominalTypeEnum_Category_Set             43
#define MIRNominalTypeEnum_Category_DynamicSet      44
#define MIRNominalTypeEnum_Category_Map             45
#define MIRNominalTypeEnum_Category_DynamicMap      46

#define PTR_FIELD_MASK_SCALAR (char)1
#define PTR_FIELD_MASK_PTR (char)2
#define PTR_FIELD_MASK_UNION (char)4
#define PTR_FIELD_MASK_END (chat)0

#define META_DATA_LOAD_DECL(X) const_cast<MetaData*>(&(X))

namespace BSQ
{
enum class MIRNominalTypeEnum
{
    Invalid = 0x0,
//%%NOMINAL_TYPE_ENUM_DECLARE%%
};

enum class ObjectLayoutKind
{
    NoRef,
    Packed,
    Masked,
    CollectionNoRef,
    CollectionPacked,
    CollectionMasked
};

enum class ExtractFlag
{
    Invalid,
    Pointer,
    StructAllocNoMeta,
    StructFullSize
};

typedef const char* RefMask;
typedef const char* StackRefMask;

class MetaData
{
public:
    MIRNominalTypeEnum nominaltype;
    uint32_t typecategory;
    uint32_t dataflag;
    ExtractFlag extractop;

    size_t allocsize;

    ObjectLayoutKind mkind;
    uint32_t simpleptrcount;
    RefMask refmask;

    size_t entrysize; //if this is a container then this is the size of each contained element

    const wchar_t* displayname;

    //display function pointer
    std::wstring (*displayFP)(void*);

    //extract as a KeyValue or Value from a union
    void* (*extractGeneralRepr)(void*);
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
