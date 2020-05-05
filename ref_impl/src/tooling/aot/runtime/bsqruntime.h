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

#pragma once

#define GET_RC_OPS(TAG) (bsq_ops[GET_MIR_TYPE_POSITION(TAG)])

namespace BSQ
{   
class StaticOps
{
public:
static BSQValueOps bsqops_empty;
static BSQValueOps bsqops_direct;
static BSQValueOps bsqops_checked;

//%%STATIC_OPS_DECLARE
};

constexpr BSQValueOps* bsq_ops[] = {
//%%NOMINAL_TYPE_TO_OPS
nullptr
};

template <size_t k>
struct RCIncFunctor_BSQUnionValue
{
    inline BSQUnionValue<k> operator()(BSQUnionValue<k> u) const 
    { 
        GET_RC_OPS(u.nominalType)->RCIncFunctorFP(u.udata)); 
        return u;
    }
};
template <size_t k>
struct RCDecFunctor_BSQUnionValue
{
    inline void operator()(BSQUnionValue<k> u) const 
    { 
        GET_RC_OPS(u.nominalType)->RCDecFunctorFP(u.udata));  
    }
};
template <size_t k>
struct RCReturnFunctor_BSQUnionValue
{
    inline void operator()(BSQUnionValue<k>& u, BSQRefScope& scope) const 
    { 
        GET_RC_OPS(u.nominalType)->RCReturnFunctorFP(u.udata, scope));
    }
};
template <size_t k>
struct EqualFunctor_BSQUnionValue
{
    inline bool operator()(BSQUnionValue<k>& l, BSQUnionValue<k>& r) const 
    { 
        return GET_RC_OPS(u.nominalType)->EqualFunctorFP(l.udata, r.udata));
    }
};
template <size_t k>
struct LessFunctor_BSQUnionValue
{
    inline bool operator()(BSQUnionValue<k>& l, BSQUnionValue<k>& r) const
    { 
        return GET_RC_OPS(u.nominalType)->LessFunctorFP(l.udata, r.udata));
    }
};
template <size_t k>
struct DisplayFunctor_BSQUnionValue
{
    std::u32string operator()(BSQUnionValue<k>& u) const
    {
        return GET_RC_OPS(u.nominalType)->DisplayFunctorFP(u.udata));
    }
};

class Runtime
{
public:
//%%STATIC_STRING_DECLARE%%

//%%STATIC_INT_DECLARE%%

//%%EPHEMERAL_LIST_DECLARE
};
} // namespace BSQ
