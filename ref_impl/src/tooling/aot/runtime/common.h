//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <cstdlib>
#include <cstdint>

#include <string>
#include <vector>
#include <set>
#include <map>

#include <algorithm>

#ifdef _DEBUG
#define NOT_IMPLEMENTED(OP) (BSQ::fail(OP, __FILE__, __LINE__))
#define BSQ_ASSERT(C, MSG) (BSQ::assert(OP, __FILE__, __LINE__))
#endif

#define BSQ_ABORT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))

namespace BSQ
{
void assert(bool cond, const char* msg, const char* file, int64_t line, ...);
void fail(const char* msg, const char* file, int64_t line, ...);
} // namespace BSQ
