//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

#pragma once

#define BSQ_OP_ADD(V, X, Y, F, L) int64_t V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Additon over/under flow", F, L); }
#define BSQ_OP_SUB(V, X, Y, F, L) int64_t V = X - Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Subtraction over/under flow", F, L); }
#define BSQ_OP_MULT(V, X, Y, F, L) int64_t V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Multiplication over/under flow", F, L); }
#define BSQ_OP_DIV(V, X, Y, F, L) if(Y == 0) { BSQ_ABORT("Division by 0", F, L); } int64_t V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Division over/under flow", F, L); }
#define BSQ_OP_MOD(V, X, Y, F, L) if(Y == 0) { BSQ_ABORT("Modulo by 0", F, L); } int64_t V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Modulo over/under flow", F, L); }

namespace BSQ
{   
class Runtime
{
public:
#define MIR_CONST_STRING_OP(N, S) static Value BSQ_STRING_##N;
#include "generated/const_strings.h"
#undef MIR_CONST_STRING_OP

    static inline const MIRType* getType(MIRTypeEnum tte)
    {
        return &g_types[(size_t)tte];
    }

    static inline const MIRTypeTuple* getTupleType(MIRTypeEnum tte)
    {
        return &g_tupleTypes[(size_t)tte];
    }

    static inline const MIRTypeRecord* getRecordType(MIRTypeEnum tte)
    {
        return &g_recordTypes[(size_t)tte];
    }

    static inline MIRNominalTypeEnum getValueNominalType(const Value& v)
    {
        if (v.isNone())
        {
            return MIRNominalTypeEnum::NSCore$cc$None;
        }
        else if (v.isBool())
        {
            return MIRNominalTypeEnum::NSCore$cc$Bool;
        }
        else if (v.isInt())
        {
            return MIRNominalTypeEnum::NSCore$cc$Int;
        }
        else
        {
            return v.getPtr<AnyValue>()->ntype;
        }
    }

    static bool subtype(const Value& v, const MIRTypeOption* tt);

    static bool subtype_Tuple(const Tuple* tval, const MIRTypeTuple* ttup);
    static bool subtype_Record(const Record* rval, const MIRTypeRecord* trec);

    static inline bool subtype_Nominal(const Value& v, MIRNominalTypeEnum type)
    {
        return g_nominalSubtypes.find(std::make_pair(Runtime::getValueNominalType(v), type)) != g_nominalSubtypes.end();
    }

    static inline bool subtype(const Value& v, const MIRType* tt)
    {
        if(tt->options.size() == 1)
        {
            return Runtime::subtype(v, tt->options.at(0));
        }
        else
        {
            return std::any_of(tt->options.cbegin(), tt->options.cend(), [&](const MIRTypeOption* opt) {
               return Runtime::subtype(v, opt);
            });
        }
    }

    static inline bool subtype(const Value& v, MIRTypeEnum tt)
    {
        return Runtime::subtype(v, Runtime::getType(tt));
    }
};
} // namespace BSQ
