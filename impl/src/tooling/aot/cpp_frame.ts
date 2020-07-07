//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { TypeRepr, StructRepr, RefRepr, KeyValueRepr, UnionRepr, ValueRepr, LayoutMaskEnum, MemoryByteAlignment, TRRepr } from "./type_repr";
import { moveCPPValue } from "./cpp_loadstore";

abstract class FrameLocation {
    readonly name: string;
    readonly trepr: TypeRepr;

    constructor(name: string, trepr: TypeRepr) {
        this.name = name;
        this.trepr = trepr;
    }
}

class NamedLocation extends FrameLocation {
    constructor(name: string, trepr: TypeRepr) {
        super(name, trepr);
    }
}

class StackLocation extends FrameLocation {
    readonly alignedStart: number;

    constructor(name: string, trepr: TypeRepr, alignedStart: number) {
        super(name, trepr);

        this.alignedStart = alignedStart;
    }
}

class CPPFrame {
    private currentHead = 0;
    private frameMask: LayoutMaskEnum[] = [];

    private namedArgs: Map<string, NamedLocation> = new Map<string, NamedLocation>();
    private frameArgs: Map<string, FrameLocation> = new Map<string, NamedLocation>();

    private namedVars: Map<string, NamedLocation> = new Map<string, NamedLocation>();
    private frameVars: Map<string, FrameLocation> = new Map<string, FrameLocation>();

    private tempnamectr = 0;
    
    generateFreshName(bn?: string): string {
        return `$$_${bn || "fresh"}_${this.tempnamectr++}_$$`;
    }

    ensureLocationForVariable(name: string, trepr: TypeRepr) {
        if(!trepr.isStack) {
            if(!this.namedArgs.has(name) && !this.namedVars.has(name)) {
                this.namedVars.set(name, new NamedLocation(name, trepr));
            }
        }
        else {
            if(!this.frameArgs.has(name) && !this.frameVars.has(name)) {
                this.frameVars.set(name, new StackLocation(name, trepr, this.currentHead));

                if(trepr instanceof StructRepr) {
                    this.frameMask = [...this.frameMask, ...trepr.layoutmask];
                    this.currentHead += trepr.alignedSize;
                }
                else if(trepr instanceof TRRepr) {
                    this.frameMask = [...this.frameMask, ...trepr.layoutmask];
                    this.currentHead += trepr.alignedSize;
                }
                else if(trepr instanceof RefRepr) {
                    this.frameMask.push(LayoutMaskEnum.Ptr);
                    this.currentHead += MemoryByteAlignment;
                }
                else if(trepr instanceof UnionRepr) {
                    this.frameMask.push(LayoutMaskEnum.Union);
                    
                    //the above will mark everything this scans past the size of the enum
                    for(let i = 0; i < trepr.alignedSize / MemoryByteAlignment; ++i) {
                        this.frameMask.push(LayoutMaskEnum.Scalar);
                    }

                    this.currentHead += trepr.alignedSize;
                }
                else if(trepr instanceof KeyValueRepr) {
                    this.frameMask.push(LayoutMaskEnum.Ptr);
                    this.currentHead += MemoryByteAlignment;
                }
                else if(trepr instanceof ValueRepr) {
                    this.frameMask.push(LayoutMaskEnum.Ptr);
                    this.currentHead += MemoryByteAlignment;
                }
                else {
                    assert(false);
                }
            }
        }
    }

    getTypeReprForName(name: string): TypeRepr {
        return ((this.namedArgs.get(name) || this.frameArgs.get(name) || this.namedVars.get(name) || this.frameVars.get(name)) as FrameLocation).trepr;
    }

    getExpressionForName(name: string): string {
        if (this.namedArgs.has(name) || this.namedVars.has(name)) {
            return name;
        }
        else if (this.frameArgs.has(name)) {
            return name;
        }
        else {
            const sl = this.frameVars.get(name) as StackLocation;
            return `((${sl.trepr.storage}*)($sp$ + ${sl.alignedStart}))`;
        }
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

    addArgumentVariable(name: string, trepr: TypeRepr) {
        if(!trepr.isStack) {
            this.namedArgs.set(name, new NamedLocation(name, trepr));
        }
        else {
            this.frameArgs.set(name, new NamedLocation(name, trepr));
        }
    }
}

export {
    CPPFrame
};
