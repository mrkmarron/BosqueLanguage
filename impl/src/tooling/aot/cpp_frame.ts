//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeRepr } from "./type_repr";

import * as assert from "assert";

abstract class FrameLocation {
    readonly name: string;
    readonly trepr: TypeRepr;
}

class NamedLocation extends FrameLocation {
}

class StackLocation extends FrameLocation {
    readonly alignedStart: number;
}

class CPPFrame {
    private frameMask: number[] = [];

    private namedVars: Map<string, NamedLocation> = new Map<string, NamedLocation>();
    private frameVars: Map<string, FrameLocation> = new Map<string, FrameLocation>();

    private addStackLocation(name: string, trepr: TypeRepr) {

    }

    public ensureLocationForVariable(name: string, trepr: TypeRepr) {

    }

    public generateReadFromLocation(name: string): string {

    }

    public generateWriteToLocation(name: string, trepr: TypeRepr, src: string): string {
        this.ensureLocationForVariable(name, trepr);

        if(!trepr.hasPointers) {
            return `${name} = ${src};`;
        }
        else {
            const sl = this.frameVars.get(name) as StackLocation;

            return `*((${sl.trepr.base}*)($sp$ + ${sl.alignedStart})) = *${src};`;
        }
    }
}

export {
    CPPFrame
};