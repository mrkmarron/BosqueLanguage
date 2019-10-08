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
    const std::set<std::pair<MIRNominalTypeEnum, MIRNominalTypeEnum>> m_nominalSubtypes;

    const std::map<MIRTypeEnum, MIRTypeTuple*> m_declaredTupleTypes;
    const std::map<MIRTypeEnum, MIRTypeRecord*> m_declaredRecordTypes;

     const std::map<MIRTypeEnum, MIRType*> m_declaredTypes;

public:
    const MIRNominalTypeEnum s_tnone;
    const MIRNominalTypeEnum s_tbool;
    const MIRNominalTypeEnum s_tint;
    const MIRNominalTypeEnum s_tstring;
    const MIRNominalTypeEnum s_ttuple;
    const MIRNominalTypeEnum s_trecord;

    const Value s_none;
    const Value s_true;
    const Value s_false;

#define MIR_CONST_STRING_OP(N, S) static Value BSQ_STRING_##N;
#include "generated/const_strings.h"
#undef MIR_CONST_STRING_OP

    Runtime(std::set<std::pair<MIRNominalTypeEnum, MIRNominalTypeEnum>>&& nominalSubtypes,
            std::map<MIRTypeEnum, MIRTypeTuple*>&& declaredTupleTypes,
            std::map<MIRTypeEnum, MIRTypeRecord*>&& declaredRecordTypes,
            std::map<MIRTypeEnum, MIRType*>&& declaredTypes,
            MIRNominalTypeEnum tnone, MIRNominalTypeEnum tbool, MIRNominalTypeEnum tint, MIRNominalTypeEnum tstring, MIRNominalTypeEnum ttuple, MIRNominalTypeEnum trecord)
        : m_nominalSubtypes(move(nominalSubtypes)), m_declaredTupleTypes(move(declaredTupleTypes)), m_declaredRecordTypes(move(declaredRecordTypes)),
          m_declaredTypes(declaredTypes),
          s_tnone(tnone), s_tbool(tbool), s_tint(tint), s_tstring(tstring), s_ttuple(ttuple), s_trecord(trecord),
          s_none(Value::noneValue()), s_true(Value::trueValue()), s_false(Value::falseValue())
    {
        ;
    }

    inline MIRNominalTypeEnum getValueNominalType(const Value& v) const {
        if (v.isNone())
        {
            return Runtime::s_tnone;
        }
        else if (v.isBool())
        {
            return Runtime::s_tbool;
        }
        else if (v.isInt())
        {
            return Runtime::s_tint;
        }
        else
        {
            return v.getPtr<AnyValue>()->ntype;
        }
    }

    bool subtype(const Value& v, const MIRTypeOption* tt) const;

    inline bool subtype(const Value& v, const MIRType* tt) const
    {
        if(tt->options.size() == 1)
        {
            return this->subtype(v, tt->options.at(0));
        }
        else
        {
            return std::any_of(tt->options.cbegin(), tt->options.cend(), [&](const MIRTypeOption* opt) {
               return this->subtype(v, opt);
            });
        }
    }

    inline bool subtype(const Value& v, MIRTypeEnum tt) const
    {
        return this->subtype(v, this->m_declaredTypes.at(tt));
    }

    inline bool subtype_Nominal(const Value& v, MIRNominalTypeEnum type) const
    {
        return this->m_nominalSubtypes.find(std::make_pair(this->getValueNominalType(v), type)) != this->m_nominalSubtypes.end();
    }

    bool subtype_Tuple( const Tuple* tval, const MIRTypeTuple* ttup) const
    {
        auto rp = std::mismatch(tval->m_entries.cbegin(), tval->m_entries.cend(), ttup->entries.cbegin(), ttup->entries.cend(),
                                [&](const std::pair<MIRType*, bool>& a, const Value& b) {
                                    return this->subtype(b, a.first);
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

    bool subtype_Record(const Record* rval, const MIRTypeRecord* trec) const
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
                if (!this->subtype(viter->second, titer->second.first))
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
            return std::all_of(titer, trec->entries.cend(), [&](const std::pair<MIRType*, bool>& entry) {
                return entry.second;
            });
        }
        else
        {
            return true;
        }
    }
};
} // namespace BSQ
