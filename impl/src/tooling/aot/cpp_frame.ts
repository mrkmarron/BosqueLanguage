//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { TypeRepr, StructRepr, RefRepr, KeyValueRepr, UnionRepr, ValueRepr, LayoutMaskEnum, MemoryByteAlignment, TRRepr, NoneRepr } from "./type_repr";
import { MIRType } from "../../compiler/mir_assembly";

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

    private namedVars: Map<string, NamedLocation> = new Map<string, NamedLocation>();
    private frameVars: Map<string, FrameLocation> = new Map<string, FrameLocation>();

    private tempnamectr = 0;
    
    generateFreshName(bn?: string): string {
        return `$$_${bn || "fresh"}_${this.tempnamectr++}_$$`;
    }

    ensureLocationForVariable(name: string, trepr: TypeRepr) {
        if(!trepr.hasPointers && !(trepr instanceof TRRepr) && !(trepr instanceof UnionRepr)) {
            if(!this.namedVars.has(name)) {
                this.namedVars.set(name, new NamedLocation(name, trepr));
            }
        }
        else {
            if(!this.frameVars.has(name)) {
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

    generateStore(name: string, trepr: TypeRepr, src: string): string {
        this.ensureLocationForVariable(name, trepr);

        if(!trepr.isStack) {
            return `${name} = ${src};`;
        }
        else {
            const sl = this.frameVars.get(name) as StackLocation;
            if(trepr.isSimplePtr) {
                return `*((void**)($sp$ + ${sl.alignedStart})) = *${src};`;
            }
            else {
                return `GC_MEM_COPY(($sp$ + ${sl.alignedStart}), ${src}, ${trepr.alignedSize});`;
            }
        }
    }

    generateLoad(name: string): string {
        if(this.namedVars.has(name)) {
            return name;
        }
        else {
            const sl = this.frameVars.get(name) as StackLocation;
            return `(${sl.trepr.std}*)($sp$ + ${sl.alignedStart})`;
        }
    }

    generateMoveFromSrcIntoFrame(name: string, nrepr: TypeRepr, src: string, srepr: TypeRepr): string {

    }

    generateMoveIntoDstFromFrame(name: string, dst: string, drepr: TypeRepr): string {

    }

    generateAllocation(name: string, trepr: TypeRepr, allocsrc: string): string {
        this.ensureLocationForVariable(name, trepr);

        const sl = this.frameVars.get(name) as StackLocation;
        return `*((${sl.trepr.std}**)($sp$ + ${sl.alignedStart})) = ${allocsrc};`;
    }

    intitializeUnion(name: string, trepr: UnionRepr, src: string, srepr: TypeRepr): string {
        this.ensureLocationForVariable(name, trepr);

        const sl = this.frameVars.get(name) as StackLocation;
        if(!srepr.isStack) {
            return `*((MetaData**)($sp$ + ${sl.alignedStart}) = META_DATA_LOAD_DECL(${srepr.metadataName}); *((${srepr.std}*)($sp$ + ${sl.alignedStart} + sizeof(MetaData*)) = ${src};`;
        }
        else {
            if(trepr.isSimplePtr) {
                return `*((MetaData**)($sp$ + ${sl.alignedStart}) = META_DATA_LOAD_DECL(${srepr.metadataName}); *((void**)($sp$ + ${sl.alignedStart} + sizeof(MetaData*)) = *${src};`;
            }
            else {
                return `*((MetaData**)($sp$ + ${sl.alignedStart}) = META_DATA_LOAD_DECL(${srepr.metadataName}); GC_MEM_COPY(($sp$ + ${sl.alignedStart} + sizeof(MetaData*)), ${src}, ${srepr.alignedSize});`;
            }
        }
    }

    extractFromUnion(name: string, srepr: TypeRepr, uname: string): string {
        this.ensureLocationForVariable(name, srepr);

        const sl = this.frameVars.get(uname) as StackLocation;
        if(!srepr.isStack) {
            return `${name} = *((${srepr.std}*)(((UnionValue*)($sp$ + ${sl.alignedStart}))->udata);`;
        }
        else {
            const tl = this.frameVars.get(name) as StackLocation;
            if(srepr.isSimplePtr) {
                return `*((void**)($sp$ + ${tl.alignedStart})) = *((void**)(((UnionValue*)($sp$ + ${sl.alignedStart}))->udata));`;
            }
            else {
                return `GC_MEM_COPY($sp$ + ${tl.alignedStart}, ((UnionValue*)($sp$ + ${sl.alignedStart}))->udata, ${srepr.alignedSize});`;
            }
        }
    }

    coercePrimitive(xxxx, frame: CPPFrame, exp: string, from: MIRType, trfrom: TypeRepr, into: MIRType, trinto: TypeRepr): {exp: string, op: string | undefined} {

        if (trfrom instanceof NoneRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

            if (trinto instanceof UnionRepr) {
                const usname = this.generateFreshName("unionnone");
                const op = frame.intitializeUnion(usname, trinto, "BSQ_VALUE_NONE", trfrom);
                return {exp: usname, op: op};
            }
            else if (trinto instanceof KeyValueRepr) {
                return {exp: "((KeyValue)BSQ_VALUE_NONE)", op: undefined};
            }
            else {
                return {exp: "((Value)BSQ_VALUE_NONE)", op: undefined};
            }
        }
        else if (trfrom instanceof StructRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");
   
            if (trinto instanceof UnionRepr) {
                const usname = this.generateFreshName("unionstruct");
                const op = frame.intitializeUnion(usname, trinto, exp, trfrom);
                return {exp: usname, op: op};
            }
            else {
                let cc = "[INVALID]";
                let op: string | undefined = undefined;

                if (trfrom.base === "BSQBool") {
                    cc = `BSQ_ENCODE_VALUE_BOOL(${exp})`;
                }
                else if (trfrom.base === "int64_t") {
                    cc = `BSQ_ENCODE_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if(trfrom.isStack) {
                        cc = this.generateFreshName("boxarg");
                        op = frame.generateStoreAllocation(cc, trinto, `Allocator::GlobalAllocator.copyInto<${trfrom.std}*>(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp})`);
                    }
                    else {
                        cc = this.generateFreshName("boxarg");
                        op = frame.generateStoreAllocation(cc, trinto, `Allocator::GlobalAllocator.copyInto<${trfrom.std}*>(META_DATA_LOAD_DECL(${trfrom.metadataName}), &${exp})`);
                    }
                }

                if (trinto instanceof KeyValueRepr) {
                    return {exp: `((KeyValue)${cc})`, op: op};
                }
                else {
                    return {exp: `((Value)${cc})`, op: op};
                }
            }
        }
        else if (trfrom instanceof TRRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");
            
            if (trinto instanceof UnionRepr) {
                const usname = this.generateFreshName("uniontr");
                const op = frame.intitializeUnion(usname, trinto, exp, trfrom);
                return { exp: usname, op: op };
            }
            else if(trinto instanceof TRRepr) {
                assert(trfrom.isTuple === trinto.isTuple);

                const csname = this.generateFreshName("convtr");
                const op = frame.generateWriteToLocation(csname, trinto, exp);
                return { exp: csname, op: op };
            }
            else {
                const cc = this.generateFreshName("boxtr");
                const op = frame.generateStoreAllocation(cc, trinto, `Allocator::GlobalAllocator.allocateTPlus<${trfrom.std}*>(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp})`);

                if (trinto instanceof KeyValueRepr) {
                    return {exp: `((KeyValue)${cc})`, op: op};
                }
                else {
                    return {exp: `((Value)${cc})`, op: op};
                }
            }
        }
        else if (trfrom instanceof RefRepr) {
            assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

            if (trinto instanceof UnionRepr) {
                const usname = this.generateFreshName("unionref");
                const op = frame.intitializeUnion(usname, trinto, exp, trfrom);
                return { exp: usname, op: op };
            }
            else if (trinto instanceof KeyValueRepr) {
                return {exp: `((KeyValue)${exp})`, op: undefined};
            }
            else {
                return {exp: `((Value)${exp})`, op: undefined};
            }
        }
        else if(trfrom instanceof UnionRepr) {
            if(trinto instanceof NoneRepr) {
                return {exp: "BSQ_VALUE_NONE", op: undefined};
            }
            else if(trinto instanceof StructRepr) {
                const usname = this.generateFreshName("unionse");
                const op = frame.extractFromUnion(usname, trinto, exp);
                return { exp: usname, op: op };
            }
            else if(trinto instanceof TRRepr) {
                const usname = this.generateFreshName("uniontr");
                const op = frame.generateWriteToLocation(usname, trinto, exp);
                return { exp: usname, op: op };
            }
            else if(trinto instanceof RefRepr) {
                const usname = this.generateFreshName("unionre");
                const op = frame.extractFromUnion(usname, trinto, exp);
                return { exp: usname, op: op };
            }
            else {
                const ename = this.generateFreshName("unioneg");
                frame.ensureLocationForVariable(ename, trinto);
                const ecall = `(BSQUnion*)`
                xxxx;
            }
        }
        else if (trfrom instanceof KeyValueRepr) {
            if (trinto instanceof NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof StructRepr) {
                if (trinto.base === "BSQBool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if(trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*(BSQ_GET_VALUE_PTR(${exp}, ${trinto.base}))`;
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((Value)${exp})`;
            }
        }
        else {
            if (trinto instanceof NoneRepr) {
                return `BSQ_VALUE_NONE`;
            }
            else if (trinto instanceof StructRepr) {
                if (trinto.base === "BSQBool") {
                    return `BSQ_GET_VALUE_BOOL(${exp})`;
                }
                else if (trinto.base === "int64_t") {
                    return `BSQ_GET_VALUE_TAGGED_INT(${exp})`;
                }
                else {
                    if(trinto.base === "BSQTuple" || trinto.base === "BSQRecord") {
                        return `*(BSQ_GET_VALUE_PTR(${exp}, ${trinto.base}))`;
                    }
                    else {
                        return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.boxed})->bval`;
                    }
                }
            }
            else if (trinto instanceof RefRepr) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${trinto.base})`;
            }
            else {
                return `((KeyValue)${exp})`;
            } 
        }
    }
}

export {
    CPPFrame
};
