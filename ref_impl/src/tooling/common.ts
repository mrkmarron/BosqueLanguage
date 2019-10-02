//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRType, MIRTypeOption } from "../compiler/mir_assembly";

function NOT_IMPLEMENTED<T>(msg: string): T {
    throw new Error(`Not Implemented: ${msg}`);
}

function isInlineType(t: MIRType | MIRTypeOption): boolean {
    if (t instanceof MIRType && t.options.length !== 1) {
        return false;
    }

    const ut = (t instanceof MIRType) ? t.options[0] : t;
    return (ut.trkey === "NSCore::Bool" || ut.trkey === "NSCore::Int");
}

export {
    NOT_IMPLEMENTED,
    isInlineType
};
