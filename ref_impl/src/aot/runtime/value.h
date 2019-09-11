//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include <cstdint>

namespace BSQ
{
enum class Tag
{
    //none is the special nullptr value
    ref_tag = 0x0, 
    true_tag = 0x1,
    false_tag = 0x2,
    inlineint_tag = 0x4
};

typedef int32_t inline_int;
typedef void* Value;

constexpr Value bnone = (Value)0x0;
constexpr Value btrue = (Value)0x1;
constexpr Value bfalse = (Value)0x2;

inline bool JavascriptNumber::Is_NoTaggedIntCheck(Var aValue)
{
    return ((uint64)aValue >> 50) != 0;
}

inline double JavascriptNumber::GetValue(Var aValue)
{
    AssertMsg(Is(aValue), "Ensure var is actually a 'JavascriptNumber'");
    double result;
    (*(uint64 *)(&result)) = (((uint64)aValue) ^ FloatTag_Value);
    return result;
}

inline Tag getTagFrom(Value v)
{
    return (Tag)(((uint64_t)v) & 0xF);
}

inline inline_int unboxInlineInt(Value v)
{
    return (inline_int)(((int64_t)v) >> 4);
}
inline Value boxInlineInt(inline_int i)
{
    return (Value)(((uint64_t)(i << 4)) & ((uint64_t)Tag::inlineint_tag));
}



} // namespace BSQ
