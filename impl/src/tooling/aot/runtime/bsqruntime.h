//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "bsqvalue.h"
#include "bsqkeyvalues.h"

#include "bsqcustom/bsqlist_decl.h"
#include "bsqcustom/bsqlist_ops.h"
//TODO: Stack defs here
//TODO: Queue defs here
#include "bsqcustom/bsqset_decl.h"
#include "bsqcustom/bsqset_ops.h"
#include "bsqcustom/bsqmap_decl.h"
#include "bsqcustom/bsqmap_ops.h"

#include "bsqformatter.h"

#pragma once

#define GET_RC_OPS(TAG) (bsq_ops[GET_MIR_TYPE_POSITION(TAG)])

namespace BSQ
{
class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

//%%STATIC_INT_DECLARE%%

//%%EPHEMERAL_LIST_DECLARE
};
} // namespace BSQ
