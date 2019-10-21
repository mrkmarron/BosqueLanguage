//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"

#pragma once

#define BSQ_OP_ADD(V, X, Y, F, L) V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Additon over/under flow", F, L); }
#define BSQ_OP_SUB(V, X, Y, F, L) V = X - Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Subtraction over/under flow", F, L); }
#define BSQ_OP_MULT(V, X, Y, F, L) V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Multiplication over/under flow", F, L); }
#define BSQ_OP_DIV(V, X, Y, F, L) if(Y == 0) { BSQ_ABORT("Division by 0", F, L); } V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Division over/under flow", F, L); }
#define BSQ_OP_MOD(V, X, Y, F, L) if(Y == 0) { BSQ_ABORT("Modulo by 0", F, L); } V = X + Y; if((V < BINT_MIN) | (BINT_MAX < V)) { BSQ_ABORT("Modulo over/under flow", F, L); }

namespace BSQ
{   
class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

static const char* propertyNames[];

static bool equality_op(Value lhs, Value rhs);
static bool compare_op(Value lhs, Value rhs);

static std::string diagnostic_format(Value v);
};
} // namespace BSQ
