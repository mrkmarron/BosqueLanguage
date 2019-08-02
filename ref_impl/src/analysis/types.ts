//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRType, MIRAssembly } from "../compiler/mir_assembly";

class TypeConstraint {
    readonly assembly: MIRAssembly;
    readonly subtypeUpper: MIRType[]; //Type is in intersection of all these types
    readonly subtypeLower: MIRType[]; //Type is not in union of these types

    private constructor(assembly: MIRAssembly, subtypeUpper: MIRType[], subtypeLower: MIRType[]) {
        this.assembly = assembly;
        this.subtypeLower = subtypeLower;
        this.subtypeUpper = subtypeUpper;
    }

    isInfeasible(): boolean {
        xxxx;
    }

    isTypeConsistent(t: MIRType): boolean {
        xxxx;
    }
}
