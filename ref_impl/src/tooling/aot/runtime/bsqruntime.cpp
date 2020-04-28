//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqruntime.h"

namespace BSQ
{    
inline bool INVALID_EqualFunctorFP(void* data1, void* data2) { assert(false); return false; }
inline bool INVALID_LessFunctorFP(void* data1, void* data2) { assert(false); return false; }
inline std::u32string INVALID_DisplayFunctorFP(void* data) { assert(false); return U"[INVALID]"; }

inline void* EMPTY_RCIncFunctorFP(void* arg) { return arg; }
inline void EMPTY_RCDecFunctorFP(void* arg) { ; }
inline void EMPTY_RCReturnFunctorFP(void* arg, BSQRefScope& scope) { ; }

inline void* DIRECT_RCIncFunctorFP(void* arg) { return BSQRef::incrementDirect(arg); }
inline void DIRECT_RCDecFunctorFP(void* arg) { BSQRef::decrementDirect(arg); }
inline void DIRECT_RCReturnFunctorFP(void* arg, BSQRefScope& scope) { scope.callReturnDirect(BSQ_GET_VALUE_PTR(arg, BSQRef)); }

inline void* CHECKED_RCIncFunctorFP(void* arg) { return BSQRef::incrementChecked(arg); }
inline void CHECKED_RCDecFunctorFP(void* arg) { BSQRef::decrementChecked(arg); }
inline void CHECKED_RCReturnFunctorFP(void* arg, BSQRefScope& scope) { scope.processReturnChecked(arg); }

static BSQValueOps bsqops_empty = {
    &EMPTY_RCIncFunctorFP,
    &EMPTY_RCDecFunctorFP,
    &EMPTY_RCReturnFunctorFP,
    &INVALID_EqualFunctorFP,
    &INVALID_LessFunctorFP,
    &INVALID_DisplayFunctorFP
};

static BSQValueOps bsqops_direct = {
    &DIRECT_RCIncFunctorFP,
    &DIRECT_RCDecFunctorFP,
    &DIRECT_RCReturnFunctorFP,
    &INVALID_EqualFunctorFP,
    &INVALID_LessFunctorFP,
    &INVALID_DisplayFunctorFP
};

static BSQValueOps bsqops_checked = {
    &CHECKED_RCIncFunctorFP,
    &CHECKED_RCDecFunctorFP,
    &CHECKED_RCReturnFunctorFP,
    &INVALID_EqualFunctorFP,
    &INVALID_LessFunctorFP,
    &INVALID_DisplayFunctorFP
};

//%%STATIC_OPS_CREATE

//%%STATIC_STRING_CREATE%%

//%%STATIC_INT_CREATE%%
} // namespace BSQ
