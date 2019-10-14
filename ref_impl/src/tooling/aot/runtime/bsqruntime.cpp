//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
bool Runtime::subtype(const Value& v, const MIRTypeOption* tt)
{
    auto ntype = Runtime::getValueNominalType(v);

    auto ttup = dynamic_cast<const MIRTypeTuple*>(tt);
    if (ttup != nullptr)
    {
        return (ntype == MIRNominalTypeEnum::NSCore$cc$Tuple) && Runtime::subtype_Tuple(v.getPtr<const Tuple>(), ttup);
    }

    auto trec = dynamic_cast<const MIRTypeRecord*>(tt);
    if (trec != nullptr)
    {
        return (ntype == MIRNominalTypeEnum::NSCore$cc$Record) && Runtime::subtype_Record(v.getPtr<const Record>(), trec);
    }

    auto tentity = dynamic_cast<const MIRTypeEntity*>(tt);
    if (tentity != nullptr)
    {
        return Runtime::subtype_Nominal(v, tentity->entityKey);
    }

    auto tconcept = dynamic_cast<const MIRTypeConcept*>(tt);
    return std::any_of(tconcept->conceptKeys.cbegin(), tconcept->conceptKeys.cend(), [&](const MIRNominalTypeEnum &te) {
        return Runtime::subtype_Nominal(v, te);
    });
}

bool Runtime::subtype_Tuple(const Tuple* tval, const MIRTypeTuple* ttup)
{
    auto rp = std::mismatch(tval->m_entries.cbegin(), tval->m_entries.cend(), ttup->entries.cbegin(), ttup->entries.cend(),
                            [&](const Value& a, const std::pair<MIRTypeEnum, bool>& b) {
                                return Runtime::subtype(a, b.first);
                            });

    if (rp.first != tval->m_entries.cend() && rp.second != ttup->entries.cend())
    {
        return false;
    }
    else if (rp.first != tval->m_entries.cend())
    {
        return ttup->isOpen; //There are more values than type entries so this better be open
    }
    else if (rp.second != ttup->entries.cend())
    {
        return rp.second->second; //There are more type entries than values so they better be optional
    }
    else
    {
        return true;
    }
}

bool Runtime::subtype_Record(const Record* rval, const MIRTypeRecord* trec)
{
    auto titer = trec->entries.cbegin();
    auto viter = rval->m_entries.cbegin();

    while (titer != trec->entries.cend() && viter != rval->m_entries.cend())
    {
        if (titer->first > viter->first)
        {
            return false; //we are missing a property that the value needs
        }
        else if (titer->first < viter->first)
        {
            //we have a property in the type that is not in the value -- if it is optionl then ok & skip else false
            if (!titer->second.second)
            {
                return false;
            }

            titer++;
        }
        else
        {
            //same names so do type equality check
            if (!Runtime::subtype(viter->second, titer->second.first))
            {
                return false;
            }

            titer++;
            viter++;
        }
    }

    if (viter != rval->m_entries.cend())
    {
        //There are more values than type entries so this better be open
        return trec->isOpen;
    }
    else if (titer != trec->entries.cend())
    {
        //There are more type entries than values so they better be optional
        return std::all_of(titer, trec->entries.cend(), [&](const std::pair<MIRPropertyEnum, std::pair<MIRTypeEnum, bool>> &entry) {
            return entry.second.second;
        });
    }
    else
    {
        return true;
    }
}

#define MIR_CONST_STRING_OP(N, S) Value Runtime::BSQ_STRING_##N = Value(new String(MIRNominalTypeEnum::BSQ_N_NSCore$cc$String, std::string(S)));
#include "generated/const_strings.h"
#undef MIR_CONST_STRING_OP
} // namespace BSQ
