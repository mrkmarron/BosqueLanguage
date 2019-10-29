//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function sanitizeStringForCpp(name: string): string {
    return name
    .replace(/#/g, "$h$")
    .replace(/::/g, "$cc$")
    .replace(/=/g, "$eq$")
    .replace(/\[/g, "$lb$")
    .replace(/\]/g, "$rb$")
    .replace(/{/g, "$lc$")
    .replace(/}/g, "$rc$")
    .replace(/</g, "$la$")
    .replace(/>/g, "$ra$")
    .replace(/\|/g, "$v$")
    .replace(/--/g, "$dd$")
    .replace(/, /g, "$csp$")
    .replace(/[.]/g, "$dot$")
    .replace(/:/g, "$c$")
    .replace(/[\\]/g, "$bs$")
    .replace(/[/]/g, "$fs$")
    .replace(/%/g, "$pct$");
}

function filenameClean(fname: string): string {
    return fname.replace(/\\/g, "\\\\");
}

export {
    NOT_IMPLEMENTED,
    sanitizeStringForCpp,
    filenameClean
};
