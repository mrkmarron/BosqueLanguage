//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include <vector>
#include <stack>
#include <queue>

#include "bsqmetadata.h"

////////
//GCStack

#define GC_STACK_LOAD(T, BASE, IDX) (*((T*)(BASE + IDX)))
#define GC_STACK_STORE(T, BASE, IDX, V) (*((T*)(BASE + IDX))) = (V))

////////
//Memory allocator

#define MEM_STATS
#if defined(BDEBUG) || defined(MEM_STATS)
#define ENABLE_MEM_STATS
#define MEM_STATS_OP(X) X
#define MEM_STATS_ARG(X) X
#else
#define MEM_STATS_OP(X)
#define MEM_STATS_ARG(X)
#endif

#define BSQ_NURSERY_SIZE 2097152
#define BSQ_ALLOC_COUNT_THRESHOLD 33554432
#define BSQ_ALLOC_LARGE_BLOCK_SIZE 4096

#define BSQ_MEM_ALIGNMENT 8
#define BSQ_WORD_ALIGN_ALLOC_SIZE(ASIZE) (((ASIZE) + 0x7) & 0xFFFFFFFFFFFFFFFC)

#define BSQ_ALLIGNED_MALLOC(SIZE) _aligned_malloc(SIZE, BSQ_MEM_ALIGNMENT)

#define GC_MARK_BLACK_X ((uint64_t)(1 << 60))
#define GC_MARK_BLACK_Y ((uint64_t)(2 << 60))

#define GC_RC_CLEAR ((uint64_t)0)
#define GC_COUNT_GET_MASK 0xFFFFFFFFFFFF
#define GC_MARK_GET_MASK 0xFFFF000000000000

#define GET_RC_HEADER(M) ((RCMeta*)((uint8_t*)M) - sizeof(RCMeta))
#define GET_RC_VALUE(M) (*GET_RC_HEADER(M))
#define GET_RC_COUNT(M) (GET_RC_VALUE(M) & GC_COUNT_GET_MASK)
#define GET_RC_MARK(M) (GET_RC_VALUE(M) & GC_MARK_GET_MASK)

#define INC_RC_HEADER(M) (GET_RC_VALUE(M)++)
#define DEC_RC_HEADER(M) (GET_RC_VALUE(M)--)
#define MARK_RC_HEADER(M, XY) (GET_RC_VALUE(M) = (GET_RC_COUNT(M) | XY))

#define IS_ZERO_COUNT(M) (GET_RC_COUNT(M) == 0)
#define IS_UNREACHABLE(M, XY) (IS_ZERO_COUNT(M) & (GET_RC_MARK(M) != XY))

#define TYPE_INFO_FORWARD_SENTINAL nullptr
#define GET_TYPE_META_DATA(M) ((MetaData*)M)
#define SET_TYPE_META_DATA_FORWARD_SENTINAL(M) ((MetaData*)M) = nullptr

#define GET_FORWARD_PTR(M) *((void**)(((uint8_t*)M) + sizeof(MetaData*)))
#define SET_FORWARD_PTR(M, P) *((void**)(((uint8_t*)M) + sizeof(MetaData*))) = (void*)P

#define GC_CHECK_IS_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)
#define IS_RC_ALLOCATION(M, BSTART, BEND) (((uintptr_t)M < BSTART) | (BEND <= (uintptr_t)M))

#define GC_MEM_COPY(DST, SRC, BYTES) memcpy_s(DST, SRC, BYTES)
#define GC_GET_FIRST_DATA_LOC(M) (((uint8_t*)M) + sizeof(MetaData*))
#define GC_GET_FIRST_COLLECTION_LOC(M) (((uint8_t*)M) + sizeof(MetaData*) + sizeof(size_t))

namespace BSQ
{
    class Allocator;

    //Bits include stack mark data and ref count
    typedef uint64_t RCMeta;
    
    struct GCStackEntry
    {
        void** refframep;
        uint32_t refslots;

        void** mixedframep;
        StackRefMask mask;
    };

    class GCStack
    {
    public:
        static GCStackEntry frames[8192];
        static uint32_t stackp;

        inline static void pushFrame(void** reffp, uint32_t refslots, void** structfp=nullptr, StackRefMask mask=nullptr)
        {
            if(GCStack::stackp >= 8192)
            {
                printf("Out-Of-Stack\n");
                exit(1);
            }

            GCStack::frames[GCStack::stackp++] = {reffp, refslots, structfp, mask};
        }

        inline static void popFrame()
        {
            GCStack::stackp--;
        }
    };

    class GCOperator
    {
    private:
        Allocator* alloc;
        
    public:
        GCOperator(Allocator* alloc) : alloc(alloc) { ; }

        void collect();
    };

    //A class that implements our bump pointer nursery space
    class BumpAllocator
    {
    private:
        //We inline the fields for the current/end of the block that we are allocating from
        uint8_t* m_currPos;
        uint8_t* m_endPos;

        uint8_t* m_block;
        GCOperator gc;

#ifdef ENABLE_MEM_STATS
        size_t totalalloc;
#endif
    public:
        BumpAllocator(Allocator* alloc) : m_currPos(nullptr), m_endPos(nullptr), m_block(nullptr), gc(alloc)
        { 
            MEM_STATS_OP(this->totalalloc = 0);
            this->m_block = (uint8_t*)BSQ_ALLIGNED_MALLOC(BSQ_NURSERY_SIZE);
            this->m_currPos = this->m_block;
            this->m_endPos = this->m_block + BSQ_NURSERY_SIZE;

            MEM_STATS_OP(this->totalalloc = 0);
        }

        ~BumpAllocator()
        {
            free(this->m_block);
        }

        inline uintptr_t getBumpStartAddr() const { return (uintptr_t)this->m_block; }
        inline uintptr_t getBumpEndAddr() const { return (uintptr_t)this->m_currPos; }

        //Allocate a byte* of the the template size (word aligned)
        template <typename T>
        inline T* allocateTypeRawSize()
        {
            MEM_STATS_OP(this->totalalloc += sizeof(T));

            if (this->m_currPos + sizeof(T) > this->m_endPos)
            {
                this->gc.collect();
            }

            T* res = (T*)this->m_currPos;
            this->m_currPos += sizeof(T);

            return res;
        }

        //Allocate a byte* of the the template size (word aligned) plus an extra block
        template <typename T, typename U>
        inline T* allocateTypeRawSizePlus(size_t csize, U** contents)
        {
            MEM_STATS_OP(this->totalalloc += sizeof(T) + csize);

            if (this->m_currPos + sizeof(T) + csize > this->m_endPos)
            {
                this->gc.collect();
            }

            T* res = (T*)this->m_currPos;
            *contents = (U*)(this->m_currPos + sizeof(T));
            this->m_currPos += sizeof(T) + csize;
        }
    };

    //A class that implements our free list large and/or old reference counting space
    class RefAllocator
    {
    private:
#ifdef ENABLE_MEM_STATS
        size_t totalalloc;
        size_t livealloc;
#endif

    public:
        RefAllocator()
        {
            MEM_STATS_OP(this->totalalloc = 0);
            MEM_STATS_OP(this->livealloc = 0);
        }

        ~RefAllocator()
        {
            ;
        }

        inline uint8_t* allocateSize(size_t size)
        {
            size_t tsize = sizeof(RCMeta) + size;
            MEM_STATS_OP(this->totalalloc += tsize);

            uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(tsize);
            *((RCMeta*)rr) = GC_RC_CLEAR;

#if defined(_WIN32)
            MEM_STATS_OP(this->livealloc += _msize(rr));
#endif

            return (rr + sizeof(RCMeta));
        }

        //Allocate a byte* of the the template size (word aligned)
        template <typename T>
        T* allocateTypeRawSize()
        {
            constexpr size_t tsize = sizeof(RCMeta) + sizeof(T);
            MEM_STATS_OP(this->livealloc += tsize);
            MEM_STATS_OP(this->totalalloc += tsize);

            uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(tsize);
            ((RCMeta*)rr)->rcount = 0;

            return (T*)(rr + sizeof(RCMeta));
        }

        //Allocate a byte* of the the template size (word aligned) plus an extra block
        template <typename T, typename U>
        T* allocateTypeRawSizePlus(size_t csize, U** contents)
        {
            constexpr size_t tsize = sizeof(RCMeta) + sizeof(T);
            MEM_STATS_OP(this->livealloc += tsize + csize);
            MEM_STATS_OP(this->totalalloc += tsize + csize);

            uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(tsize + csize);
            ((RCMeta*)rr)->rcount = 0;

            *contents = (U*)(rr + sizeof(RCMeta) + sizeof(T));
            return (T*)(rr + sizeof(RCMeta));
        }

        
        inline void release(uint8_t* m)
        {
#if defined(_WIN32)
            MEM_STATS_OP(this->livealloc -= _msize(m - sizeof(RCMeta)));
#endif

            free(m - sizeof(RCMeta));
        }
    };
    
    class Allocator
    {
    private:
        BumpAllocator balloc;
        RefAllocator ralloc;

        std::vector<void*> maybeZeroCounts;

        RCMeta mark;
        uintptr_t bstart;
        uintptr_t bend;
        std::queue<void*> worklist;

        std::queue<void*> releaselist;

#ifdef ENABLE_MEM_STATS
        size_t gccount;
        size_t promoted;

        size_t max;
#endif

        template <uint64_t mark>
        inline void rcDecRef(void* obj)
        {
            if(GC_CHECK_IS_PTR(obj) | (obj != nullptr))
            {
                assert(GET_RC_COUNT(obj) > 0); //otherwise we lost a count somewhere

                DEC_RC_HEADER(obj);
                if(IS_UNREACHABLE(obj, mark))
                {
                    this->releaselist.push(*iter);
                }
            }
        }

        template <uint64_t mark>
        void rcDecMixed(void** slots, const char* mask)
        {  
            void** cslot = slots;
            const char* cmaskop = mask;

            while (*cmaskop)
            {
                char op = *cmaskop++;
                if(op == PTR_FIELD_MASK_SCALAR) 
                {
                    cslot++;
                }    
                else if(op == PTR_FIELD_MASK_PTR)
                {
                    this->rcDecRef<mark>(cslot++);
                }
                else
                {
                    assert(false, "NOT IMPLEMENTED");
                }
            }
        }

        template <uint64_t mark>
        void rcDecObjectMixed(void* obj, MetaData* meta, ObjectLayoutKind layout)
        {
            if(layout == ObjectLayoutKind::Masked)
            {
                void** slots = (void**)GC_GET_FIRST_DATA_LOC(obj);
                this->rcDecMixed<mark>(slots, meta->refmask);
            }
            else
            {
                size_t count = *((size_t*)GC_GET_FIRST_DATA_LOC(obj));
                void** elemscurr = (void**)GC_GET_FIRST_COLLECTION_LOC(obj);
                for(size_t i = 0; i < count; ++i)
                {
                    this->rcDecMixed<mark>(elemscurr, meta->refmask);
                    elemscurr = (void**)(((uint8_t*)elemscurr) + meta->entrysize);
                }
            }
        }

        template <uint64_t mark>
        inline void rcDecObject(void* obj)
        {
            MetaData* meta = GET_TYPE_META_DATA(obj);
            ObjectLayoutKind layout = meta->mkind;

            if(layout == ObjectLayoutKind::Packed)
            {
                void** slotcurr = (void**)GC_GET_FIRST_DATA_LOC(obj);
                void** slotend = slotcurr + meta->simpleptrcount;
                while(slotcurr != slotend)
                {
                    this->rcDecObject<mark>(*slotcurr++);
                }
            }
            else if(layout == ObjectLayoutKind::CollectionPacked)
            {
                size_t count = *((size_t*)GC_GET_FIRST_DATA_LOC(obj));
                void** elemscurr = (void**)GC_GET_FIRST_COLLECTION_LOC(obj);
                void** elemsend = elemscurr + count;
                while(elemscurr != elemsend)
                {
                    this->rcDecObject<mark>(*elemscurr++);
                }
            }
            else
            {
                this->rcDecObjectMixed(obj, meta, layout);
            }
        }

        //If we visit an object in the bump space that has not been seen before then we need to copy it to the RC space and set the forwarding info
        template<bool isRoot>
        void* moveObjectToRCSpace(void* obj);

        //Process the reference in the given slot (updating the slot contents if needed)
        template<bool isRoot, uint64_t mark>
        inline void processRefSlot(void** slot)
        {
            void* v = *slot;
            if(GC_CHECK_IS_PTR(v) | (v != nullptr))
            {
                if(IS_RC_ALLOCATION(v, this->bstart, this->bend))
                {
                    if constexpr (isRoot)
                    {
                        MARK_RC_HEADER(v, mark);
                    }
                    else
                    {
                        INC_RC_HEADER(v);
                    }
                }
                else
                {
                    *slot = this->moveObjectToRCSpace(v);
                }
            }
        }

        template <bool isRoot, uint64_t mark>
        inline void processMixed(void** slots, const char* mask)
        {
            void** cslot = slots;
            const char* cmaskop = mask;

            while (*cmaskop)
            {
                char op = *cmaskop++;
                if(op == PTR_FIELD_MASK_SCALAR) 
                {
                    cslot++;
                }    
                else if(op == PTR_FIELD_MASK_PTR)
                {
                    this->processRefSlot<isRoot, mark>(cslot++);
                }
                else
                {
                    assert(false, "NOT IMPLEMENTED");
                }
            }
        }

        template <uint64_t mark>
        void processFrameMixedRoots(void** slots, StackRefMask mask)
        {
            this->processMixed<true, mark>(slots, mask);
        }

        void processObjectMixed(void* obj, MetaData* meta, ObjectLayoutKind layout)
        {
            if(layout == ObjectLayoutKind::Masked)
            {
                void** slots = (void**)GC_GET_FIRST_DATA_LOC(obj);
                this->processMixed<false, GC_RC_CLEAR>(slots, meta->refmask);
            }
            else
            {
                size_t count = *((size_t*)GC_GET_FIRST_DATA_LOC(obj));
                void** elemscurr = (void**)GC_GET_FIRST_COLLECTION_LOC(obj);
                for(size_t i = 0; i < count; ++i)
                {
                    this->processMixed<false, GC_RC_CLEAR>(elemscurr, meta->refmask);
                    elemscurr = (void**)(((uint8_t*)elemscurr) + meta->entrysize);
                }
            }
        }

        template <uint64_t mark>
        void processRoots()
        {
            for(size_t i = 0; i < GCStack::stackp; ++i)
            {
                void** slots = GCStack::frames[i].refframep;
                uint32_t slotct = GCStack::frames[i].refslots;
                for(size_t j = 0; j < slotct; ++j)
                {
                    this->processRefSlot<true>(slots + j);
                }

                if(GCStack::frames[i].mixedframep != nullptr)
                {
                    this->processFrameMixedRoots<mark>(GCStack::frames[i].mixedframep, GCStack::frames[i].mask);
                }
            }
        }

        inline void processObject(void* obj)
        {
            MetaData* meta = GET_TYPE_META_DATA(obj);
            ObjectLayoutKind layout = meta->mkind;

            if(layout == ObjectLayoutKind::Packed)
            {
                void** slotcurr = (void**)GC_GET_FIRST_DATA_LOC(obj);
                void** slotend = slotcurr + meta->simpleptrcount;
                while(slotcurr != slotend)
                {
                    this->processRefSlot<false, GC_RC_CLEAR>(slotcurr++);
                }
            }
            else if(layout == ObjectLayoutKind::CollectionPacked)
            {
                size_t count = *((size_t*)GC_GET_FIRST_DATA_LOC(obj));
                void** elemscurr = (void**)GC_GET_FIRST_COLLECTION_LOC(obj);
                void** elemsend = elemscurr + count;
                while(elemscurr != elemsend)
                {
                    this->processRefSlot<false, GC_RC_CLEAR>(elemscurr++);
                }
            }
            else
            {
                this->processObjectMixed(obj, meta, layout);
            }
        }

        void processHeap()
        {
            while(!this->worklist.empty())
            {
                this->processObject(this->worklist.front());
                this->worklist.pop();
            }
        }

        template <uint64_t mark>
        void checkZeroCountList()
        {
            auto biter = this->maybeZeroCounts.begin();
            auto eiter = this->maybeZeroCounts.end();
            for(auto iter = biter; iter < eiter; iter++)
            {
                if(IS_UNREACHABLE(*iter, mark))
                {
                    this->releaselist.push(*iter);
                    *iter = nullptr;
                }
            }

            if(!this->releaselist.empty())
            {
                this->maybeZeroCounts.erase(biter, std::remove(biter, eiter, nullptr));
            }
        }

        template <uint64_t mark>
        void processRelease()
        {
            while(!this->releaselist.empty())
            {
                void* obj = this->releaselist.front();
                this->releaselist.pop();

                this->rcDecObject<mark>(obj);
            }
        }

    public:
        Allocator() : balloc(this), ralloc(), maybeZeroCounts(), mark(GC_MARK_BLACK_X), bstart(0), bend(0), worklist(), releaselist()
        {
            maybeZeroCounts.reserve(256);
        }

        ~Allocator()
        {
            ;
        }

        //Allocate with "new" from the slab allocator
        template<typename T, typename... Args>
        inline T* ObjectNew(Args... args)
        {
            static_assert(BSQ_WORD_ALIGN_ALLOC_SIZE(sizeof(T)) == sizeof(T));

            if constexpr (sizeof(T) <= BSQ_ALLOC_LARGE_BLOCK_SIZE)
            {
                return new (this->balloc.allocateTypeRawSize<T>()){args...};
            }
            else
            {
                return new (this->ralloc.allocateTypeRawSize<T>()){args...};
            }
        }

        //Allocate T* of the size needed to hold count elements of the given type
        template <typename T, typename U, typename... Args>
        T* CollectionNew(size_t count, U** contents, Args... args)
        {
            static_assert(BSQ_WORD_ALIGN_ALLOC_SIZE(sizeof(T)) == sizeof(T));

            size_t csize = BSQ_WORD_ALIGN_ALLOC_SIZE(count * sizeof(U));
    
            if (sizeof(T) + csize <= BSQ_ALLOC_LARGE_BLOCK_SIZE)
            {
                return new (this->balloc.allocateTypeRawSizePlus<T, U>(csize, contents)){*contents, args...};
            }
            else
            {
                return new (this->ralloc.allocateTypeRawSizePlus<T, U>(csize, contents)){*contents, args...};
            }
        }

        void collect();
    };
}