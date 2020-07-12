//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { TypeRepr, ReprStorageKind } from "./type_repr";

const pointerframe = "$pframe$";
const valuestructframe = "$vsframe$";
const generalstructframe = "$gframe$";

abstract class FrameLocation {
    readonly name: string;
    readonly access: string;
    readonly trepr: TypeRepr;

    constructor(name: string, access: string, trepr: TypeRepr) {
        this.name = name;
        this.access = access;
        this.trepr = trepr;
    }
}

class ArgLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, name, trepr);
    }
}

class PrimitiveLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, name, trepr);
    }
}

class PointerLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, `${pointerframe}.${name}`, trepr);
    }
}

class ValueStructLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, `${valuestructframe}.${name}`, trepr);
    }
}

class GeneralStructLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, `${generalstructframe}.${name}`, trepr);
    }
}

class CPPFrame {
    private registeredNames: Map<string, FrameLocation> = new Map<string, FrameLocation>();

    private tempnamectr = 0;
    
    generateFreshName(bn?: string): string {
        return `$$_${bn || "fresh"}_${this.tempnamectr++}_$$`;
    }

    addArgumentVariable(name: string, trepr: TypeRepr) {
        this.registeredNames.set(name, new ArgLocation(name, trepr));
    }

    ensureLocationForVariable(name: string, trepr: TypeRepr) {
        if(!this.registeredNames.has(name)) {
            if(trepr.storage === ReprStorageKind.Primitive) {
                this.registeredNames.set(name, new PrimitiveLocation(name, trepr));
            }
            else if(trepr.storage === ReprStorageKind.Pointer) {
                this.registeredNames.set(name, new PointerLocation(name, trepr));
            }
            else if(trepr.storage === ReprStorageKind.ValueStruct) {
                this.registeredNames.set(name, new ValueStructLocation(name, trepr));
            }
            else {
                this.registeredNames.set(name, new GeneralStructLocation(name, trepr));
            }
        }
    }

    getTypeReprForName(name: string): TypeRepr {
        return (this.registeredNames.get(name) as FrameLocation).trepr;
    }

    getExpressionForName(name: string): string {
        return (this.registeredNames.get(name) as FrameLocation).access;
    }

    generateMoveFromSrcIntoFrame(name: string, nrepr: TypeRepr, src: string, srepr: TypeRepr): string {
        this.ensureLocationForVariable(name, nrepr);

        return moveCPPValue(this.getExpressionForName(name), src, srepr, nrepr);
    }

    generateMoveIntoDstFromFrame(name: string, dst: string, drepr: TypeRepr): string {
        const acc = this.getExpressionForName(name);
        const acctr = this.getTypeReprForName(name);

        return moveCPPValue(dst, acc, acctr, drepr);
    }

    generateMoveOperation(dst: string, drepr: TypeRepr, src: string, srepr: TypeRepr): string {
        return moveCPPValue(dst, src, srepr, drepr);
    }

    generateAllocation(name: string, trepr: TypeRepr, allocsrc: string): string {
        this.ensureLocationForVariable(name, trepr);

        const sl = this.frameVars.get(name) as StackLocation;
        return `*((${sl.trepr.base}**)($sp$ + ${sl.alignedStart})) = ${allocsrc};`;
    }
}

export {
    CPPFrame
};
