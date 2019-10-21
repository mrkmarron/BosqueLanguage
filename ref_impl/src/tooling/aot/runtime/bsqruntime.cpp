//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{
//%%STATIC_STRING_CREATE%%

bool Runtime::equality_op(Value lhs, Value rhs)
{
    BSQ_ASSERT(false, "NOT IMPLEMENTED");
    return false;
}

bool Runtime::compare_op(Value lhs, Value rhs) 
{
    BSQ_ASSERT(false, "NOT IMPLEMENTED");
    return false;
}

std::string Runtime::diagnostic_format(Value v)
{
    BSQ_ASSERT(false, "NOT IMPLEMENTED");
    return std::string("");
}
} // namespace BSQ
