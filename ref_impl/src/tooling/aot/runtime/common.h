//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <cstdlib>
#include <cstdint>

#include <string>
#include <vector>
#include <unordered_set>
#include <unordered_map>

#include <memory>

#ifndef RELEASE
#define NOT_IMPLEMENTED(OP) (BSQ::fail(OP, __FILE__, __LINE__))
#define ASSERT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))
#endif

#define BSQ_ABORT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))

namespace BSQ
{
void fail(const char* msg, const char* file, int64_t line, ...);
} // namespace BSQ
