//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "mirtype.h"

namespace BSQ
{
    class TypedStringValue
    {
        const MIRType* strtype;
        const std::string contents;
    };

    class GUIDValue
    {
        const std::shared_ptr<std::string> host;
        const uint64_t idv;
    };
} 
