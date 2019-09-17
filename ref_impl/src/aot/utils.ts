//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

function NOT_IMPLEMENTED<T>(action: string): T {
    throw new Error(`Not Implemented: ${action}`);
}

function sanitizeForCpp(name: string): string {
    return name;
}

export {
    NOT_IMPLEMENTED,
    sanitizeForCpp
};
