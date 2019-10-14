//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
bool Runtime::subtype(const Value& v, const MIRTypeOption* tt) const
{
    auto ntype = this->getValueNominalType(v);

    auto ttup = dynamic_cast<const MIRTypeTuple*>(tt);
    if (ttup != nullptr)
    {
        return (ntype == this->s_ttuple) && this->subtype_Tuple(v.getPtr<const Tuple>(), ttup);
    }

    auto trec = dynamic_cast<const MIRTypeRecord*>(tt);
    if (trec != nullptr)
    {
        return (ntype == this->s_trecord) && this->subtype_Record(v.getPtr<const Record>(), trec);
    }

    auto tentity = dynamic_cast<const MIRTypeEntity*>(tt);
    if (tentity != nullptr)
    {
        return this->subtype_Nominal(v, tentity->entityKey);
    }

    auto tconcept = dynamic_cast<const MIRTypeConcept*>(tt);
    return std::any_of(tconcept->conceptKeys.cbegin(), tconcept->conceptKeys.cend(), [&](const MIRNominalTypeEnum &te) {
        return this->subtype_Nominal(v, te);
    });
}

#define MIR_CONST_STRING_OP(N, S) Value Runtime::BSQ_STRING_##N = Value(new String(MIRNominalTypeEnum::BSQ_N_NSCore$cc$String, std::string(S)));
#include "generated/const_strings.h"
#undef MIR_CONST_STRING_OP
} // namespace BSQ
