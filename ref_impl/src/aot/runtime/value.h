//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include <cstdlib>
#include <cstdint>

#define NOT_IMPLEMENTED(OP) (BSQ::fail(OP, __FILE__, __LINE__))

#define RUNTIME_ERROR(MSG) (BSQ::fail(OP, __FILE__, __LINE__))
#define BSQ_ABORT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))

namespace BSQ
{
    void fail(const char* msg, const char* file, int64_t line, ...)
    {
        exit(1);
    }

    typedef void* Value;

    constexpr int32_t  VarTag_Shift       = 48;
    constexpr int32_t  VarTagInline_Shift = 46;

    constexpr uint64_t FloatTag_Value = (((uint64_t)0xFFFCull) << VarTag_Shift);
    constexpr uint64_t AtomTag_Value  = (((uint64_t)0x1i64) << VarTag_Shift);
    
    constexpr uint64_t TrueTagInline_Value  = (((uint64_t)0x1i64) << VarTagInline_Shift);
    constexpr uint64_t FalseTagInline_Value = (((uint64_t)0x2i64) << VarTagInline_Shift);

    constexpr uint64_t ReferenceTag_Mask = (FloatTag_Value | AtomTag_Value);
    constexpr uint64_t TagInline_Mask    = (((uint64_t)0x3i64) << VarTagInline_Shift);

    constexpr Value NoneInline_Value  = (Value)((uint64_t)0x0);
    constexpr Value TrueInline_Value  = (Value)(AtomTag_Value | TrueTagInline_Value);
    constexpr Value FalseInline_Value = (Value)(AtomTag_Value | FalseTagInline_Value);

    constexpr uint64_t k_Nan = 0xFFF8000000000000ull;

    inline uint64_t doubleConvert(double value)
    {
        return  *((uint64_t*)(&value));
    }

    inline bool IsNan(double value)
    {
        uint64_t nCompare = doubleConvert(value);
        return ((~nCompare & 0x7FF0000000000000ull) == 0) & ((nCompare & 0x000FFFFFFFFFFFFFull) != 0);
    }

    inline bool isNone(Value v)
    {
        return v == NoneInline_Value;
    }

    inline bool isTrue(Value v)
    {
        return v == TrueInline_Value;
    }

    inline bool isFalse(Value v)
    {
        return v == FalseInline_Value;
    }

    inline bool isInlineAtom(Value v)
    {
        return (((uint64_t)v) & AtomTag_Value) != 0;
    }

    inline bool isInlineFloat(Value v)
    {
        return (((uint64_t)v) & FloatTag_Value) != 0;
    }

    inline bool isReference(Value v)
    {
        return (v != NoneInline_Value) & (((uint64_t)v & ReferenceTag_Mask) == 0);
    }

    inline bool isBool(Value v)
    {
        return isInlineAtom(v) & ((((uint64_t)v) & TagInline_Mask) != 0);
    }

    inline bool isInt(Value v)
    {
        return isInlineAtom(v) & (((uint64_t)v) & TagInline_Mask) == 0;
    }

    inline Value boolToVar(bool value)
    {
        return value ? TrueInline_Value : FalseInline_Value;
    }

    inline Value smallintToVar(int32_t value)
    {
        return (Value*)(((uintptr_t)(uint32_t)value) | AtomTag_Value);
    }

    inline Value intToVar(int64_t value)
    {
        if((value < INT32_MIN) || (value > INT32_MAX))
        {
            return (Value*)(((uintptr_t)(uint32_t)value) | AtomTag_Value);
        }

        NOT_IMPLEMENTED("intToVar -- BigInt");
    }

    inline Value floatToVar(double value)
    {
         if (IsNan(value))
        {
            value = *((double*)(&k_Nan));
        }

        uint64_t val = doubleConvert(value);
        return (Value)(val ^ FloatTag_Value);
    }

} // namespace BSQ
