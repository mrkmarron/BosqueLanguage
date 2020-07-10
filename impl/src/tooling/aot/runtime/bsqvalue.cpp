//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqvalue.h"
#include "bsqkeyvalues.h"

namespace BSQ
{
None NoneStorage::nhome = BSQ_NONE;
NoneValue NoneStorage::nvhome = BSQ_NONE_VALUE;

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
