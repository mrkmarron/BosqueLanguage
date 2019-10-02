//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "common.h"

namespace BSQ
{
void fail(const char* msg, const char* file, int64_t line, ...) 
{
    exit(1);
}
} // namespace BSQ