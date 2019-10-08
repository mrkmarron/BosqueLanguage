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
#define BSQ_ASSERT(C, MSG) (BSQ::assert(C, MSG, __FILE__, __LINE__))
#endif

#ifdef _DEBUG
#define BSQ_ABORT(MSG, F, L) (throw BSQAbort(MSG, F, L, __FILE__, __LINE__))
#else
#define BSQ_ABORT(MSG, F, L) (throw BSQAbort())
#endif

namespace BSQ
{
void assert(bool cond, const char* msg, const char* file, int64_t line);

class BSQAbort
{
#ifdef _DEBUG
public:
const char* msg;
const char* bfile;
int64_t bline;
const char* cfile;
int64_t cline;

BSQAbort(const char* msg, const char* bfile, int64_t bline, const char* cfile, int64_t cline) : msg(msg), bfile(bfile), bline(bline), cfile(cfile), cline(cline) { ; }
#else
public:
BSQAbort() { ; }
#endif
};
} // namespace BSQ
