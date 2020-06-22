//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmemory.h"

namespace BSQ
{
    GCStackEntry GCStack::frames[8192];
    uint32_t GCStack::stackp = 0;

    void GCOperator::collect()
    {
        this->alloc->collect();
    }

    Allocator Allocator::GlobalAllocator;

    template<bool isRoot>
    void* Allocator::moveObjectToRCSpace(void* obj)
    {
        const MetaData* ometa = GET_TYPE_META_DATA(obj);
        const layout = ometa->mkind;

        void* nobj = nullptr;
        if((layout == ObjectLayoutKind::NoRef) | (layout == ObjectLayoutKind::Packed) | (layout == ObjectLayoutKind::Masked))
        {
            void* nobj = this->ralloc.allocateSize(ometa->allocsize);
            MEM_STATS_OP(this->promotedbytes += ometa->allocsize);

            GC_MEM_COPY(nobj, obj, ometa->allocsize);
            if(layout != ObjectLayoutKind::NoRef)
            {
                this->worklist.push(nobj);
            }
        }
        else 
        {
            size_t elemcount = *((size_t*)GC_GET_FIRST_DATA_LOC(obj));
            size_t totalsize = ometa->allocsize + BSQ_WORD_ALIGN_ALLOC_SIZE((elemcount * ometa->entrysize));
            void* nobj = this->ralloc.allocateSize(totalsize);
            MEM_STATS_OP(this->promotedbytes += totalsize);

            GC_MEM_COPY(nobj, obj, totalsize);
            if(layout != ObjectLayoutKind::CollectionNoRef)
            {
                this->worklist.push(nobj);
            }
        }

        if constexpr (isRoot)
        {
            MARK_RC_HEADER(nobj, this->mark);
            this->maybeZeroCounts.push_back(nobj);
        }
        else
        {
            INC_RC_HEADER(nobj);
        }

        SET_TYPE_META_DATA_FORWARD_SENTINAL(obj);
        SET_FORWARD_PTR(obj, nobj);

        return nobj;
    }

    void Allocator::collect()
    {
        if(this->mark == GC_MARK_BLACK_X)
        {
            this->collectMark<GC_MARK_BLACK_X>();
        }
        else
        {
            this->collectMark<GC_MARK_BLACK_Y>();
        }
    }
}
