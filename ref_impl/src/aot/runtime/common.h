//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <memory>

#include <string>
#include <regex>

#include <map>

#define NOT_IMPLEMENTED(OP) (BSQ::fail(OP, __FILE__, __LINE__))

#define RUNTIME_ERROR(MSG) (BSQ::fail(OP, __FILE__, __LINE__))
#define BSQ_ABORT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))

namespace BSQ
{
void fail(const char* msg, const char* file, int64_t line, ...);
} // namespace BSQ
