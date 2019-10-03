//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

#pragma once

namespace BSQ
{
class Runtime
{
private:
    const std::unordered_set<std::pair<std::string, std::string>> m_nominalSubtypes;

public:
    const VTable* s_noneVT;
    const VTable* s_boolVT;
    const VTable* s_intVT;
    const VTable* s_stringVT;
    const VTable* s_floatVT;
    const VTable* s_tupleVT;
    const VTable* s_recordVT;

    const std::shared_ptr<BoxedNone> s_none;
    const std::shared_ptr<BoxedBool> s_true;
    const std::shared_ptr<BoxedBool> s_false;

    Runtime(std::unordered_set<std::pair<std::string, std::string>>&& nominalSubtypes,
    const VTable* noneVT, const VTable* boolVT, const VTable* intVT, const VTable* stringVT, const VTable* floatVT, const VTable* tupleVT, const VTable* recordVT,
    std::shared_ptr<BoxedNone> snone, std::shared_ptr<BoxedBool> strue, std::shared_ptr<BoxedBool> sfalse
    )
        : m_nominalSubtypes(move(nominalSubtypes)),
        s_noneVT(noneVT), s_boolVT(boolVT), s_intVT(intVT), s_stringVT(stringVT), s_floatVT(floatVT), s_tupleVT(tupleVT), s_recordVT(recordVT),
        s_none(snone), s_true(strue), s_false(sfalse)
    {
        ;
    }

    ~Runtime() = default;

    inline std::shared_ptr<BoxedBool> boxBool(InlineBoolType bv)
    {
        return bv ? this->s_true : s_false;
    }

    inline bool subtype_NominalNominal(const std::shared_ptr<HeapValue>& v, const std::string& type)
    {
        return this->m_nominalSubtypes.find(std::make_pair(v->m_vtable->m_type, type)) != this->m_nominalSubtypes.end();
    }

    inline bool subtype_TupleTuple(const std::shared_ptr<Tuple>& v, const std::string& type)
    {
        return this->m_nominalSubtypes.find(std::make_pair(this->m_tupleTypeName, type)) != this->m_nominalSubtypes.end();
    }

    inline bool subtype_RecordRecord(const std::shared_ptr<Record>& v, const std::string& type)
    {
        return this->m_nominalSubtypes.find(std::make_pair(this->m_tupleTypeName, type)) != this->m_nominalSubtypes.end();
    }
};
} // namespace BSQ
