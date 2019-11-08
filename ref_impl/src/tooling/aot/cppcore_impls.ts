//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

const CoreImplBodyText = new Map<string, (params: string[]) => string>()
.set("int_tryparse", (params: string[]) => `return std::stol((${params[0]})->sdata);`)
;

export {
    CoreImplBodyText
};
