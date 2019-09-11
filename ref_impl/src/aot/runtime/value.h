//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include <cstdint>

namespace BSQ
{
enum class Tag
{
    ref_tag = 0x0,
    none_tag = 0x1,
    false_tag = 0x2,
    true_tag = 0x4,
    inlineint_tag = 0x8
};

typedef int32_t inline_int;
typedef void *Value;

constexpr Value vnone = (Value)0x1;
constexpr Value vfalse = (Value)0x2;
constexpr Value vtrue = (Value)0x4;

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
