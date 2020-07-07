//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeRepr, NoneRepr, StructRepr, TRRepr, RefRepr, UnionRepr, KeyValueRepr, EphemeralListRepr } from "./type_repr";

import * as assert from "assert";

function coercePrimitive(trgt: string, exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    if (trfrom instanceof NoneRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return `${trgt}->umeta = META_DATA_LOAD_DECL(MetaData_None);`;
        }
        else if (trinto instanceof KeyValueRepr) {
            return `*${trgt} = ((KeyValue)BSQ_VALUE_NONE);`;
        }
        else {
            return `*${trgt} = ((Value)BSQ_VALUE_NONE);`;
        }
    }
    else if (trfrom instanceof StructRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            if(!trfrom.isStack) {
                if(trfrom.isSimpleAssignable) {
                    return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); ${trgt}->udata = reinterpret_cast<void*>(${exp});`;
                }
                else {
                    return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); GC_MEM_COPY(${trgt}->udata, &${exp}, ${trfrom.alignedSize});`;
                }
            }
            else {
                if(trfrom.isSimpleAssignable) {
                    return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); ${trgt}->udata = *((void**)${exp});`;
                }
                else {
                    return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); GC_MEM_COPY(${trgt}->udata, ${exp}, ${trfrom.alignedSize});`;
                }
            }
        }
        else {
            if (trfrom.base === "BSQBool") {
                return `*${trgt} = BSQ_ENCODE_VALUE_BOOL(${exp});`;
            }
            else if (trfrom.base === "int64_t") {
                return `*${trgt} = BSQ_ENCODE_VALUE_TAGGED_INT(${exp});`;
            }
            else {
                if(!trfrom.isStack) {
                    return `*${trgt} = Allocator::GlobalAllocator.allocateT<${trfrom.base}>(META_DATA_LOAD_DECL(${trfrom.metadataName})); *${trgt} = ${exp};`;
                }
                else {
                    if(trfrom.isSimpleAssignable) {
                        return `*${trgt} = Allocator::GlobalAllocator.allocateT<${trfrom.base}>(META_DATA_LOAD_DECL(${trfrom.metadataName})); *${trgt} = *${exp};`;
                    }
                    else {
                        return `*${trgt} = Allocator::GlobalAllocator.allocateT<${trfrom.base}>(META_DATA_LOAD_DECL(${trfrom.metadataName})); GC_MEM_COPY(*${trgt}, ${exp}, ${trfrom.alignedSize});`;
                    }
                }
            }
        }
    }
    else if (trfrom instanceof TRRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof RefRepr), "Should not be possible");
        
        if (trinto instanceof UnionRepr) {
            return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); GC_MEM_COPY(${trgt}->udata, ${exp}, ${Math.min(trfrom.alignedSize, trinto.datasize)});`;
        }
        else if(trinto instanceof TRRepr) {
            return `GC_MEM_COPY(*${trgt}, ${exp}, ${Math.min(trfrom.alignedSize, trinto.alignedSize)});`;
        }
        else {
            const trsizeexp = `Allocator::MetaData_ComputeSize_SimpleCollection(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${exp})`;
            return `*${trgt} = Allocator::GlobalAllocator.allocateDynamic<${trfrom.base}>(META_DATA_LOAD_DECL(${trfrom.metadataName}), ${trsizeexp}); GC_MEM_COPY(*${trgt}, ${exp}, ${trsizeexp});`;
        }
    }
    else if (trfrom instanceof RefRepr) {
        assert(!(trinto instanceof NoneRepr) && !(trinto instanceof StructRepr) && !(trinto instanceof TRRepr) && !(trinto instanceof RefRepr), "Should not be possible");

        if (trinto instanceof UnionRepr) {
            return `${trgt}->umeta = META_DATA_LOAD_DECL(${trfrom.metadataName}); ${trgt}->udata = *${exp};`;
        }
        else {
            return `*${trgt} = *${exp};`;
        }
    }
    else if(trfrom instanceof UnionRepr) {
        if(trinto instanceof NoneRepr) {
            return ";";
        }
        else if(trinto instanceof StructRepr) {
            if(!trinto.isStack) {
                if(trinto.isSimpleAssignable) {
                    return `${trgt} = reinterpret_cast<${trinto.base}>(${exp}->udata);`;
                }
                else {
                    return `GC_MEM_COPY(&${trgt}, ${exp}->udata, ${trinto.alignedSize});`;
                }
            }
            else {
                if(trinto.isSimpleAssignable) {
                    return `*${trgt} = *((${trinto.base}*)${exp});`;
                }
                else {
                    return `GC_MEM_COPY(${trgt}, ${exp}->udata, , ${trinto.alignedSize});`;
                }
            }
        }
        else if(trinto instanceof TRRepr) {
            return `GC_MEM_COPY(${trgt}, ${exp}->udata, ${Math.min(trinto.alignedSize, trfrom.datasize)});`;
        }
        else if(trinto instanceof RefRepr) {
            return `*${trgt} = ${exp}->udata;`;
        }
        else {
            return `${exp}->umeta->coerceUnionToBox(${exp}, ${trgt});`;
        }
    }
    else if (trfrom instanceof KeyValueRepr) {
        if (trinto instanceof NoneRepr) {
            return `;`;
        }
        else if (trinto instanceof StructRepr) {
            if (trinto.base === "BSQBool") {
                return `${trgt} = BSQ_GET_VALUE_BOOL(*${exp})`;
            }
            else if (trinto.base === "int64_t") {
                return `${trgt} = BSQ_GET_VALUE_TAGGED_INT(*${exp})`;
            }
            else {
                if(!trfrom.isStack) {
                    return `${trgt} = *((${trinto.base}*)${exp});`;
                }
                else {
                    if(trfrom.isSimpleAssignable) {
                        return `*${trgt} = *((${trinto.base}*)${exp});`;
                    }
                    else {
                        return `GC_MEM_COPY(*${trgt}, *${exp}, ${trinto.alignedSize});`;
                    }
                }
            }
        }
        else if(trinto instanceof TRRepr) {
            const trsizeexp = `Allocator::MetaData_ComputeSize_SimpleCollection(META_DATA_LOAD_DECL(${trinto.metadataName}), ${exp})`;
            return `GC_MEM_COPY(${trgt}, *${exp}, ${trsizeexp});`;
        }
        else if (trinto instanceof UnionRepr) {
            return `GET_TYPE_META_DATA(*${exp})->coerceBoxToUnion(${exp}, ${trgt});`;
        }
        else if (trinto instanceof RefRepr) {
            return `*${trgt} = BSQ_GET_VALUE_PTR(*${exp}, ${trinto.base})`;
        }
        else {
            return `*${trgt} = *((Value*)${exp})`;
        }
    }
    else {
        if (trinto instanceof NoneRepr) {
            return `;`;
        }
        else if (trinto instanceof StructRepr) {
            if (trinto.base === "BSQBool") {
                return `${trgt} = BSQ_GET_VALUE_BOOL(*${exp})`;
            }
            else if (trinto.base === "int64_t") {
                return `${trgt} = BSQ_GET_VALUE_TAGGED_INT(*${exp})`;
            }
            else {
                if(!trfrom.isStack) {
                    return `${trgt} = *((${trinto.base}*)${exp});`;
                }
                else {
                    if(trfrom.isSimpleAssignable) {
                        return `*${trgt} = *((${trinto.base}*)${exp});`;
                    }
                    else {
                        return `GC_MEM_COPY(*${trgt}, *${exp}, ${trinto.alignedSize});`;
                    }
                }
            }
        }
        else if(trinto instanceof TRRepr) {
            const trsizeexp = `Allocator::MetaData_ComputeSize_SimpleCollection(META_DATA_LOAD_DECL(${trinto.metadataName}), ${exp})`;
            return `GC_MEM_COPY(${trgt}, *${exp}, ${trsizeexp});`;
        }
        else if (trinto instanceof UnionRepr) {
            return `GET_TYPE_META_DATA(*${exp})->coerceBoxToUnion(${exp}, ${trgt});`;
        }
        else if (trinto instanceof RefRepr) {
            return `*${trgt} = BSQ_GET_VALUE_PTR(*${exp}, ${trinto.base})`;
        }
        else {
            return `*${trgt} = *((KeyValue*)${exp})`;
        } 
    }
}

function generateEphemeralListConvert(trgt: string, exp: string, elfrom: EphemeralListRepr, elinto: EphemeralListRepr): string {
    const ops: string[] = [];
   
    for(let i = 0; i < elinto.elist.length; ++i) {
        ops.push(moveCPPValue(`&(${trgt}->entry_${i})`, `&(${exp}->entry_${i})`, elfrom.elist[i], elinto.elist[i]));
    }

    return `{ ${ops.join("")} }`;
}

function coerceCPPValue(trgt: string, exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    assert(trfrom.base !== trinto.base);

    if(trfrom instanceof EphemeralListRepr && trinto instanceof EphemeralListRepr) {
        return generateEphemeralListConvert(trgt, exp, trfrom, trinto);
    }

    return coercePrimitive(trgt, exp, trfrom, trinto);
}

function moveCPPValue(trgt: string, exp: string, trfrom: TypeRepr, trinto: TypeRepr): string {
    if(trfrom.base !== trinto.base) {
        return coerceCPPValue(trgt, exp, trfrom, trinto);
    }
    else {
        if(!trinto.isStack) {
            return `${trgt} = ${exp};`;
        }
        else {
            if(trinto.isSimpleAssignable) {
                return `*${trgt} = *${exp};`;
            }
            else {
                return `GC_MEM_COPY(${trgt}, ${exp}, ${trinto.alignedSize});`;
            }
        }
    }
}

export {
    moveCPPValue  
};
