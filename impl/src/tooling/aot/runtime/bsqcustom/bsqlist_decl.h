//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include "../bsqvalue.h"

namespace BSQ
{
template <typename T>
struct BSQList
{
    size_t count;

    template <typename DisplayF>
    std::wstring display() const
    {
        T* vals = GET_COLLECTION_START_FIXED(this, sizeof(BSQList<T>));
        std::wstring ls(L"{");
        for (size_t i = 0; i < this->count; ++i)
        {
            if (i != 0)
            {
                ls += L", ";
            }
            ls += DisplayF{}(vals[i]);
        }
        ls += L"}";

        return ls;
    }
};
}
