//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

#pragma once

class BSQValidator
{
public:
    const char* strrep;

    BSQValidator(const char* strrep): strrep(strrep) { ; }
    virtual ~BSQValidator() = default;
};

//
//TODO: fill in validator stuff here 
//