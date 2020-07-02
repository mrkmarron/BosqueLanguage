//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
void* coerceUnionToBox_RefValue(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return ruv->udata;
}
void* coerceUnionToBox_BSQBool(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return BSQ_ENCODE_VALUE_BOOL(ruv->udata);
}
void* coerceUnionToBox_int64_t(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return BSQ_ENCODE_VALUE_TAGGED_INT(ruv->udata);
}
void* coerceUnionToBox_double(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return Allocator::GlobalAllocator.copyNew<double>(META_DATA_LOAD_DECL(MetaData_Float64), ruv->udata);
}
void* coerceUnionToBox_BSQISOTime(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return Allocator::GlobalAllocator.copyNew<BSQISOTime>(META_DATA_LOAD_DECL(MetaData_ISOTime), ruv->udata);
}
void* coerceUnionToBox_Regex(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    return Allocator::GlobalAllocator.copyNew<BSQRegex>(META_DATA_LOAD_DECL(MetaData_Regex), ruv->udata);
}
void* coerceUnionToBox_Tuple(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    BSQTuple* tv = (BSQTuple*)ruv->udata;

    Value* contents;
    BSQTuple* res = Allocator::GlobalAllocator.collectionNew<BSQTuple, Value>(META_DATA_LOAD_DECL(MetaData_Tuple), tv->count, &contents, tv->count, tv->flag);
    GC_MEM_COPY(GET_COLLECTION_START(res), GET_COLLECTION_START(tv), tv->count * sizeof(Value));

    return res; 
}
void* coerceUnionToBox_Record(void* uv)
{
    UnionValue* ruv = (UnionValue*)uv;
    BSQRecord* rv = (BSQRecord*)ruv->udata;

    Value* contents;
    BSQRecord* res = Allocator::GlobalAllocator.collectionNew<BSQRecord, Value>(META_DATA_LOAD_DECL(MetaData_Record), rv->count, &contents, rv->count, rv->flag);
    GC_MEM_COPY(GET_COLLECTION_START(res), GET_COLLECTION_START(rv), rv->count * sizeof(Value));

    return res; 
}

std::map<MIRRecordPropertySetsEnum, std::vector<MIRPropertyEnum>> BSQRecord::knownRecordPropertySets = {
    {MIRRecordPropertySetsEnum::ps__, {}},
    //%%KNOWN_RECORD_PROPERTY_SETS_DECLARE%%
};
    
BSQDynamicPropertySetEntry BSQRecord::emptyDynamicPropertySetEntry;

BSQDynamicPropertySetEntry* BSQRecord::getExtendedProperties(BSQDynamicPropertySetEntry* curr, MIRPropertyEnum ext)
{
    auto extrs = curr->extensions.find(ext);
    if(extrs != curr->extensions.end())
    {
        return extrs->second;
    }
    else
    {
        std::vector<MIRPropertyEnum> mps(curr->propertySet);
        mps.push_back(ext);

        auto next = new BSQDynamicPropertySetEntry(move(mps));
        curr->extensions[ext] = next;

        return next;
    }
}

MetaData* getMetaData(void* v)
{
    if (BSQ_IS_VALUE_NONE(v))
    {
        return META_DATA_LOAD_DECL(MetaData_None);
    }
    else if (BSQ_IS_VALUE_BOOL(v))
    {
        return META_DATA_LOAD_DECL(MetaData_Bool);
    }
    else if (BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return META_DATA_LOAD_DECL(MetaData_Int);
    }
    else
    {
        return GET_TYPE_META_DATA(v);
    }
}

bool bsqKeyValueEqual(KeyValue v1, KeyValue v2)
{
    if(v1 == v2) 
    {
        return true;
    }

    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) 
    {
        return false;
    }

    return kt1->eq(v1, v2);
}

bool bsqKeyValueLess(KeyValue v1, KeyValue v2)
{
    MetaData* kt1 = getMetaData(v1);
    MetaData* kt2 = getMetaData(v2);
    if(kt1 != kt2) 
    {
        return kt1->nominaltype < kt2->nominaltype;
    }

    return kt1->less(v1, v2);
}

DATA_KIND_FLAG getDataKindFlag(Value v)
{
    if(BSQ_IS_VALUE_NONE(v) | BSQ_IS_VALUE_BOOL(v) | BSQ_IS_VALUE_TAGGED_INT(v))
    {
        return DATA_KIND_ALL_FLAG;
    }
    else {
        auto rcategory = GET_TYPE_META_DATA(v)->nominaltype;
        if(rcategory == MIRNominalTypeEnum_Tuple) {
            return BSQ_GET_VALUE_PTR(v, BSQTuple)->flag;
        }
        else if(rcategory == MIRNominalTypeEnum_Record) {
            return BSQ_GET_VALUE_PTR(v, BSQRecord)->flag;
        }
        else {
            return GET_TYPE_META_DATA(v)->dataflag;
        }
    }
}

std::wstring diagnostic_format(void* v)
{
    MetaData* mdata = getMetaData(v);
    return mdata->displayFP(v);
}
}
