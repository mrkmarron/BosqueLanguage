//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRType, MIRTypeOption, MIREntityType } from "../../compiler/mir_assembly";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function isInlinableType(t: MIRType | MIRTypeOption): boolean {
    if (t instanceof MIRType && t.options.length !== 1) {
        return false;
    }

    const ut = (t instanceof MIRType) ? t.options[0] : t;
    return (ut.trkey === "NSCore::Bool" || ut.trkey === "NSCore::Int");
}

function getInlinableType(t: MIRType | MIRTypeOption): MIRTypeOption {
    return (t instanceof MIRType) ? t.options[0] : t;
}

function isUniqueEntityType(t: MIRType | MIRTypeOption): boolean {
    if (t instanceof MIRType && t.options.length !== 1) {
        return false;
    }

    const ut = (t instanceof MIRType) ? t.options[0] : t;
    return ut instanceof MIREntityType;
}

function getUniqueEntityType(t: MIRType | MIRTypeOption): MIREntityType {
    return ((t instanceof MIRType) ? t.options[0] : t) as MIREntityType;
}

function sanitizeForCpp(name: string): string {
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

export {
    NOT_IMPLEMENTED,
    isInlinableType,
    getInlinableType,
    isUniqueEntityType,
    getUniqueEntityType,
    sanitizeForCpp
};
