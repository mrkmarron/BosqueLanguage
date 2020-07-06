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
#include <map>

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

#define BSQ_MIN_NURSERY_SIZE 1048576
#define BSQ_MAX_NURSERY_SIZE 16777216
#define BSQ_ALLOC_LARGE_BLOCK_SIZE 8192

#define BSQ_MEM_ALIGNMENT 8
#define BSQ_ALIGN_ALLOC_SIZE(ASIZE) (((ASIZE) + 0x7) & 0xFFFFFFFFFFFFFFFC)

#define BSQ_ALLIGNED_MALLOC(SIZE) _aligned_malloc(SIZE, BSQ_MEM_ALIGNMENT)

#define TYPE_INFO_FORWARD_SENTINAL nullptr
#define GET_TYPE_META_DATA(M) ((MetaData*)((uint8_t*)M - sizeof(MetaData)))
#define SET_TYPE_META_DATA_FORWARD_SENTINAL(M) *((void**)((uint8_t*)M - sizeof(MetaData))) = TYPE_INFO_FORWARD_SENTINAL

#define GET_FORWARD_PTR(M) *((void**)M)
#define SET_FORWARD_PTR(M, P) *((void**)M) = (void*)P

#define GET_COLLECTION_START_FIXED(M, X) (((uint8_t*)M) + BSQ_ALIGN_ALLOC_SIZE(X))
#define GET_COLLECTION_START_META(M, META) (((uint8_t*)M) + BSQ_ALIGN_ALLOC_SIZE((META)->datasize))

#define GC_RC_CLEAR ((uint64_t)0)
#define GC_RC_MARK_FROM_ROOT ((uint64_t)(1 << 60))
#define GC_RC_BIG_ALLOC ((uint64_t)(1 << 61))

#define GC_COUNT_GET_MASK 0xFFFFFFFFFFFF
#define GC_MARK_GET_MASK 0xFFFF000000000000

#define GET_RC_HEADER(M) ((RCMeta*)((uint8_t*)M) - (sizeof(RCMeta) + sizeof(MetaData)))
#define GET_RC_VALUE(M) (*GET_RC_HEADER(M))
#define GET_RC_COUNT(M) (GET_RC_VALUE(M) & GC_COUNT_GET_MASK)
#define GET_RC_MARK(M) (GET_RC_VALUE(M) & GC_MARK_GET_MASK)

#define INC_RC_HEADER(M) (GET_RC_VALUE(M)++)
#define DEC_RC_HEADER(M) (GET_RC_VALUE(M)--)
#define MARK_HEADER_SET(M) (GET_RC_VALUE(M) = (GET_RC_COUNT(M) | GC_RC_MARK_FROM_ROOT))
#define MARK_HEADER_CLEAR(M) (GET_RC_VALUE(M) = GET_RC_COUNT(M))

#define IS_UNREACHABLE(M) (GET_RC_VALUE(M) == GC_RC_CLEAR)

#define GC_CHECK_IS_PTR(V) ((((uintptr_t)(V)) & 0x7) == 0)
#define IS_BUMP_ALLOCATION(M, BSTART, BEND) ((BSTART <= (uintptr_t)M) & ((uintptr_t)M < BEND))
#define IS_LARGE_ALLOCATION(M) (GET_RC_VALUE(M) == GC_RC_BIG_ALLOC)

#define GET_SLAB_BASE(M) ((void*)((uint8_t*)M - sizeof(MetaData)))
#define GET_FREE_LIST_BASE(M) ((void*)((uint8_t*)M - (sizeof(RCMeta) + sizeof(MetaData))))
#define GC_MEM_COPY(DST, SRC, BYTES) memcpy_s(DST, BYTES, SRC, BYTES)

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
        RefMask mask;
    };

    class GCStack
    {
    public:
        static GCStackEntry frames[8192];
        static uint32_t stackp;

        inline static void pushFrame(void** reffp, uint32_t refslots, void** structfp=nullptr, RefMask mask=nullptr)
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

    //A class that implements our bump pointer + large free-list nursery space
    class NewSpaceAllocator
    {
    private:
        //We inline the fields for the current/end of the block that we are allocating from
        uint8_t* m_currPos;
        uint8_t* m_endPos;

        size_t m_allocsize;
        uint8_t* m_block;

        //
        //We may want to tie into a nicer free list impl here (and in the old space)
        //
        std::map<void*, size_t> m_largeallocs;

        GCOperator gc;

#ifdef ENABLE_MEM_STATS
        size_t totalalloc;
#endif

        void setAllocBlock(size_t asize)
        {
            this->m_allocsize = asize;
            this->m_block = (uint8_t*)BSQ_ALLIGNED_MALLOC(asize);

            this->m_currPos = this->m_block;
            this->m_endPos = this->m_block + asize;
        }

        void resizeAllocatorAsNeeded(size_t rcalloc)
        {
            bool shouldgrow = this->m_allocsize < BSQ_MAX_NURSERY_SIZE && this->m_allocsize < rcalloc * 0.5;
            bool shouldshrink = BSQ_MIN_NURSERY_SIZE < this->m_allocsize && rcalloc < this->m_allocsize;

            if(shouldgrow || shouldshrink)
            {
                free(this->m_block);
                if(shouldgrow)
                {
                    this->setAllocBlock(2 * this->m_allocsize);
                }
                else
                {
                    this->setAllocBlock(this->m_allocsize / 2);
                }
            }
        }

    public:
        NewSpaceAllocator(Allocator* alloc) : m_block(nullptr), m_largeallocs(), gc(alloc)
        { 
            MEM_STATS_OP(this->totalalloc = 0);

            this->setAllocBlock(BSQ_MIN_NURSERY_SIZE);
        }

        ~NewSpaceAllocator()
        {
            free(this->m_block);

            std::for_each(this->m_largeallocs.begin(), this->m_largeallocs.end(), [](void* alloc) {
                free(alloc);
            });
            this->m_largeallocs.clear();
        }

        inline uintptr_t getBumpStartAddr() const { return (uintptr_t)this->m_block; }
        inline uintptr_t getBumpEndAddr() const { return (uintptr_t)this->m_currPos; }

        inline size_t clearLargeAlloc(void* v)
        {
            auto iter = this->m_largeallocs.find(v);
            size_t asize = iter->second;

            this->m_largeallocs.erase(iter);
            
            return asize;
        }

        void postGCProcess(size_t rcmem)
        {
            std::for_each(this->m_largeallocs.begin(), this->m_largeallocs.end(), [](void* alloc) {
                free(GET_FREE_LIST_BASE(alloc));
            });
            this->m_largeallocs.clear();

            this->resizeAllocatorAsNeeded(rcmem);

            this->m_currPos = this->m_block;
            this->m_endPos = this->m_block + this->m_allocsize;
        }

        size_t currentAllocatedBytes() const
        {
            size_t balloc = this->m_currPos - this->m_block;
            std::for_each(this->m_largeallocs.begin(), this->m_largeallocs.end(), [&balloc](const std::pair<void*, size_t>& ainfo) {
                balloc += ainfo.second + sizeof(RCMeta) + sizeof(MetaData);
            });

            return balloc;
        }

        //Return uint8_t* of given asize + sizeof(MetaData)
        //If it is a large alloc then the RCMeta is just before the return pointer 
        template <size_t asize>
        inline uint8_t* allocateSize()
        {
            constexpr size_t rsize = asize + sizeof(MetaData);

            if constexpr (rsize <= BSQ_ALLOC_LARGE_BLOCK_SIZE)
            {
                MEM_STATS_OP(this->totalalloc += rsize);

                if (this->m_currPos + rsize > this->m_endPos)
                {
                    this->gc.collect();
                }

                uint8_t* res = this->m_currPos;
                this->m_currPos += rsize;

                return res;
            }
            else
            {
                constexpr size_t tsize = sizeof(RCMeta) + rsize;
                MEM_STATS_OP(this->totalalloc += tsize);

                uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(tsize);

                *((RCMeta*)rr) = GC_RC_BIG_ALLOC;
                this->m_largeallocs[rr] = asize;

                return (rr + sizeof(RCMeta));
            }
        }

        //Return uint8_t* of given asize + sizeof(MetaData)
        //If it is a large alloc then the RCMeta is just before the return pointer 
        template <size_t asize>
        inline uint8_t* allocateSizePlus(size_t csize, uint8_t** contents)
        {
            constexpr size_t rsize = asize + sizeof(MetaData);

            if(rsize + csize < BSQ_ALLOC_LARGE_BLOCK_SIZE)
            {
                size_t fsize = rsize + csize;
                MEM_STATS_OP(this->totalalloc += fsize);

                if (this->m_currPos + fsize > this->m_endPos)
                {
                    this->gc.collect();
                }

                uint8_t* res = this->m_currPos;
                *contents = this->m_currPos + rsize;
                this->m_currPos += fsize;

                return res;
            }
            else
            {
                constexpr size_t tsize = sizeof(RCMeta) + rsize;
                size_t fsize = tsize + csize;
                MEM_STATS_OP(this->totalalloc += fsize);

                uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(fsize);
                *((RCMeta*)rr) = GC_RC_BIG_ALLOC;
                this->m_largeallocs[rr] = asize + csize;

                *contents = (rr + tsize);
                return (rr + sizeof(RCMeta));
            }
        }
    };

    //A class that implements our free list large and/or old reference counting space
    class OldSpaceAllocator
    {
    private:
        //
        //We may want to tie into a nicer free list impl here (and in the new space)
        //

        size_t livealloc;

#ifdef ENABLE_MEM_STATS
        size_t totalalloc;
#endif

    public:
        OldSpaceAllocator() : livealloc(0)
        {
            MEM_STATS_OP(this->totalalloc = 0);
        }

        ~OldSpaceAllocator()
        {
            ;
        }

        inline size_t currentAllocatedBytes() const
        {
            return this->livealloc;
        }

        inline uint8_t* allocateSize(size_t size)
        {
            size_t tsize = sizeof(RCMeta) + sizeof(MetaData) + size;
            MEM_STATS_OP(this->totalalloc += tsize);

            uint8_t* rr = (uint8_t*)BSQ_ALLIGNED_MALLOC(tsize);
            *((RCMeta*)rr) = GC_RC_CLEAR;

            this->livealloc += tsize;

            return (rr + sizeof(RCMeta));
        }
        
        inline void release(void* m, size_t size)
        {
            this->livealloc -= sizeof(RCMeta) + sizeof(MetaData) + size;
            free(GET_FREE_LIST_BASE(m));
        }
    };

    class Allocator
    {
    public:
        static Allocator GlobalAllocator;

    private:
        NewSpaceAllocator nsalloc;
        OldSpaceAllocator osalloc;

        std::vector<void*> maybeZeroCounts;

        uintptr_t bstart;
        uintptr_t bend;
        std::queue<void*> worklist;

        std::queue<void*> releaselist;
        
#ifdef ENABLE_MEM_STATS
        size_t gccount;
        size_t promotedbytes;
        size_t maxheap;
#endif

        ////////
        //Operations GC mark and move
        template<bool isRoot>
        void* moveBumpObjectToRCSpace(void* obj)
        {
            const MetaData* ometa = GET_TYPE_META_DATA(obj);
            size_t osize = ometa->datasize;
            if(ometa->sizeentry != 0)
            {   
                size_t elemcount = *((size_t*)obj);
                osize += BSQ_ALIGN_ALLOC_SIZE(elemcount * ometa->sizeentry);
            }
            MEM_STATS_OP(this->promotedbytes += ometa->datasize + sizeof(MetaData));

            void* nobj = this->osalloc.allocateSize(osize + sizeof(MetaData) + sizeof(RCMeta));
            GC_MEM_COPY(nobj, GET_TYPE_META_DATA(obj), osize + sizeof(MetaData));
            if(ometa->hasRefs)
            {
                this->worklist.push(nobj);
            }

            void* robj = (void*)((uint8_t*)nobj + sizeof(MetaData));
            if constexpr (isRoot)
            {
                MARK_HEADER_SET(robj);
                this->maybeZeroCounts.push_back(robj);
            }
            else
            {
                INC_RC_HEADER(robj);
            }

            SET_TYPE_META_DATA_FORWARD_SENTINAL(obj);
            SET_FORWARD_PTR(obj, robj);

            return robj;
        }

        template<bool isRoot>
        void* moveLargeObjectToRCSpace(void* obj)
        {
            const MetaData* ometa = GET_TYPE_META_DATA(obj);
            size_t lasize = this->nsalloc.clearLargeAlloc(obj);
            MEM_STATS_OP(this->promotedbytes += lasize + sizeof(MetaData));

            if(ometa->hasRefs)
            {
                this->worklist.push(obj);
            }

            if constexpr (isRoot)
            {
                MARK_HEADER_SET(obj);
                this->maybeZeroCounts.push_back(obj);
            }
            else
            {
                INC_RC_HEADER(obj);
            }

            return nobj;
        }

        template<bool isRoot>
        inline static void gcProcessSlot(void** slot)
        {
            void* v = *slot;
            if(GC_CHECK_IS_PTR(v) & (v != nullptr))
            {
                if(IS_BUMP_ALLOCATION(v,  Allocator::GlobalAllocator.bstart, Allocator::GlobalAllocator.bend))
                {
                    *slot = Allocator::GlobalAllocator.moveBumpObjectToRCSpace<isRoot>(v);
                }
                else if(IS_LARGE_ALLOCATION(v))
                {
                    *slot = Allocator::GlobalAllocator.moveLargeObjectToRCSpace<isRoot>(v);
                }
                else 
                {
                    if constexpr (isRoot)
                    {
                        MARK_HEADER_SET(v);
                    }
                    else
                    {
                        INC_RC_HEADER(v);
                    }
                }
            }
        }

        template<bool isRoot>
        inline static void gcProcessSlots(void** slots, size_t limit)
        {  
            void** cslot = slots;
            void* end = slots + limit;
            
            while (cslot != end)
            {
                Allocator::gcProcessSlot<isRoot>(cslot++);
            }
        }

        template<bool isRoot>
        inline static void gcProcessSlotsWithUnion(void** slots)
        {  
            const MetaData* umeta = ((const MetaData*)(*slots++));
            umeta->getProcessFP<isRoot>()(umeta, slots);
        }

        template <bool isRoot>
        inline static void gcProcessSlotsWithMask(void** slots, const char* mask)
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
                    Allocator::gcProcessSlot<isRoot>(cslot++);
                }
                else
                {
                    Allocator::gcProcessSlotsWithUnion<isRoot>(cslot++);
                }
            }
        }

        ////////
        //Operations GC decrement
        inline static void gcDecrement(void* obj)
        {
            if(GC_CHECK_IS_PTR(obj) & (obj != nullptr))
            {
                DEC_RC_HEADER(obj);
                if(IS_UNREACHABLE(obj))
                {
                    Allocator::GlobalAllocator.releaselist.push(obj);
                }
            }
        }

        inline static void gcDecrementSlots(void** slots, size_t limit)
        {  
            void** cslot = slots;
            void* end = slots + limit;
            
            while (cslot != end)
            {
                Allocator::gcDecrement(*cslot++);
            }
        }

        inline static void gcDecrementSlotsWithUnion(void** slots)
        {  
            const MetaData* umeta = ((const MetaData*)(*slots++));
            umeta->decObj(umeta, slots);
        }

        inline static void gcDecSlotsWithMask(void** slots, const char* mask)
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
                    Allocator::gcDecrement(*cslot++);
                }
                else
                {
                    Allocator::gcDecrementSlotsWithUnion(cslot++);
                }
            }
        }

        ////////
        //Operations GC mark clear
        inline static void gcClearMark(void* obj)
        {
            if(GC_CHECK_IS_PTR(obj) & (obj != nullptr))
            {
                MARK_HEADER_CLEAR(obj);
            }
        }

        inline static void gcClearMarkSlots(void** slots, size_t limit)
        {  
            void** cslot = slots;
            void* end = slots + limit;
            
            while (cslot != end)
            {
                Allocator::gcClearMark(*cslot++);
            }
        }

        inline static void gcClearMarkSlotsWithUnion(void** slots)
        {  
            const MetaData* umeta = ((const MetaData*)(*slots++));
            umeta->clearObj(umeta, slots);
        }

        inline static void gcClearMarkSlotsWithMask(void** slots, const char* mask)
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
                    Allocator::gcClearMark(*cslot++);
                }
                else
                {
                    Allocator::gcClearMarkSlotsWithUnion(cslot++);
                }
            }
        }

        ////////
        //GC algorithm
        static void processRoots()
        {
            for(size_t i = 0; i < GCStack::stackp; ++i)
            {
                void** slots = GCStack::frames[i].refframep;
                uint32_t slotct = GCStack::frames[i].refslots;
                for(size_t j = 0; j < slotct; ++j)
                {
                    Allocator::gcProcessSlot<true>(slots + j);
                }

                if(GCStack::frames[i].mixedframep != nullptr)
                {
                    Allocator::gcProcessSlotsWithMask<true>(GCStack::frames[i].mixedframep, GCStack::frames[i].mask);
                }
            }
        }

        void processHeap()
        {
            while(!this->worklist.empty())
            {
                void* obj = this->worklist.front();
                
                const MetaData* umeta = GET_TYPE_META_DATA(obj);
                umeta->getProcessFP<false>()(umeta, (void**)obj);

                this->worklist.pop();
            }
        }

        void checkMaybeZeroCountList()
        {
            auto biter = this->maybeZeroCounts.begin();
            auto eiter = this->maybeZeroCounts.end();
            for(auto iter = biter; iter < eiter; iter++)
            {
                if(IS_UNREACHABLE(*iter))
                {
                    this->releaselist.push(*iter);
                    *iter = nullptr;
                }
                else
                {
                    if(GET_RC_COUNT(*iter) != 0)
                    {
                        *iter = nullptr;
                    }
                }
            }

            if(!this->releaselist.empty())
            {
                this->maybeZeroCounts.erase(biter, std::remove(biter, eiter, nullptr));
            }
        }

        void processRelease()
        {
            while(!this->releaselist.empty())
            {
                void* obj = this->releaselist.front();
                
                const MetaData* umeta = GET_TYPE_META_DATA(obj);
                if(umeta->hasRefs)
                {
                    umeta->decObj(umeta, (void**)obj);
                }

                size_t asize = umeta->computeMemorySize(umeta, obj);
                this->osalloc.release(obj, asize);

                this->releaselist.pop();
            }
        }

        void clearAllMarkRoots()
        {
            for(size_t i = 0; i < GCStack::stackp; ++i)
            {
                void** slots = GCStack::frames[i].refframep;
                uint32_t slotct = GCStack::frames[i].refslots;
                for(size_t j = 0; j < slotct; ++j)
                {
                    Allocator::gcClearMark(slots + j);
                }

                if(GCStack::frames[i].mixedframep != nullptr)
                {
                    Allocator::gcClearMarkSlotsWithMask(GCStack::frames[i].mixedframep, GCStack::frames[i].mask);
                }
            }
        }

    public:
        Allocator() : nsalloc(this), osalloc(), maybeZeroCounts(), bstart(0), bend(0), worklist(), releaselist()
        {
            this->maybeZeroCounts.reserve(256);

            MEM_STATS_OP(this->gccount = 0);
            MEM_STATS_OP(this->promotedbytes = 0);
            MEM_STATS_OP(this->maxheap = 0);
        }

        ~Allocator()
        {
            ;
        }

        template<typename T>
        inline T* allocateT(MetaData* mdata) 
        {
            constexpr size_t asize = BSQ_ALIGN_ALLOC_SIZE(sizeof(T));
            uint8_t* alloc = this->nsalloc.allocateSize<asize>();

            *((MetaData*)alloc) = mdata;
            T* res = (T*)(alloc + sizeof(MetaData));
            
            return alloc;
        }

        template <typename T, typename U>
        inline T* allocateTPlus(MetaData* mdata, size_t count, U** contents) 
        {
            size_t csize = BSQ_ALIGN_ALLOC_SIZE(count * sizeof(U));
            constexpr size_t asize = BSQ_ALIGN_ALLOC_SIZE(sizeof(T));
    
            uint8_t* alloc = this->nsalloc.allocateSizePlus<asize>(csize, (uint8_t**)contents);

            *((MetaData*)alloc) = mdata;
            T* res = (T*)(alloc + sizeof(MetaData));
            
            return alloc;
        }

        template<typename T>
        inline T* copyInto(MetaData* mdata, T* src)
        {
            T* res = this->allocateT<T>(mdata);
            GC_MEM_COPY(res, src, mdata->datasize);

            return res;
        }

        template<typename T, size_t size>
        inline T* copyIntoFixedPlus(MetaData* mdata, T* src)
        {
            T* res = this->allocateT<T>(mdata);
            GC_MEM_COPY(res, src, size);

            return res;
        }

        void collect()
        {
            MEM_STATS_OP(this->gccount++);
            MEM_STATS_OP(this->maxheap = std::max(this->maxheap, this->nsalloc.currentAllocatedBytes() + this->osalloc.currentAllocatedBytes()));

            //mark and move all live objects out of new space
            this->processRoots();
            this->processHeap();

            //Look at all the possible unreachable roots in the old space and collect (recursively) them as needed
            this->checkMaybeZeroCountList();
            this->processRelease();

            //Reset the mark colors on the roots
            this->clearAllMarkRoots();

            //Adjust the new space size if needed and reset/free the newspace allocators
            this->nsalloc.postGCProcess(this->osalloc.currentAllocatedBytes());
        }

        struct GCOperator_ProcessRoot { void operator()(void** slot) { Allocator::gcProcessSlot<true>(slot); } };
        struct GCOperator_ProcessHeap { void operator()(void** slot) { Allocator::gcProcessSlot<false>(slot); } };
        struct GCOperator_Dec { void operator()(void** slot) { Allocator::gcDecrement(*slot); } };
        struct GCOperator_Clear { void operator()(void** slot) { Allocator::gcClearMark(*slot); } };

        struct GCOperator_ProcessRoot_Union { void operator()(void** slot) { Allocator::gcProcessSlotsWithUnion<true>(slot); } };
        struct GCOperator_ProcessHeap_Union { void operator()(void** slot) { Allocator::gcProcessSlotsWithUnion<false>(slot); } };
        struct GCOperator_Dec_Union { void operator()(void** slot) { Allocator::gcDecrementSlotsWithUnion(slot); } };
        struct GCOperator_Clear_Union { void operator()(void** slot) { Allocator::gcClearMarkSlotsWithUnion(slot); } };

        inline static void MetaData_GCOperatorFP_NoRefs(const MetaData* meta, void** data)
        {
            ;
        }

        template <typename OP>
        inline static void MetaData_GCOperatorFP_Packed(const MetaData* meta, void** data)
        {
            void** slotcurr = data;
            void** slotend = slotcurr + meta->ptrcount;
            while(slotcurr != slotend)
            {
                OP{}(slotcurr++);
            }
        }

        template <typename OP>
        inline static void MetaData_GCOperatorFP_PackedEntries_Direct(const MetaData* meta, void** data)
        {
            size_t count = *((size_t*)data);

            void** slotcurr = (void**)GET_COLLECTION_START_META(data, meta);
            for(size_t i = 0; i < count; ++i)
            {
               OP{}(slotcurr++);
            }
        }

        template <typename OP>
        inline static void MetaData_GCOperatorFP_PackedEntries(const MetaData* meta, void** data)
        {
            size_t count = *((size_t*)data);
            uint32_t advancesize = meta->sizeadvance;

            void** slotcurr = (void**)GET_COLLECTION_START_META(data, meta);
            for(size_t i = 0; i < count; ++i)
            {
                void** slotend = slotcurr + meta->ptrcount;
                while(slotcurr != slotend)
                {
                    OP{}(slotcurr++);
                }
                slotcurr += advancesize;
            }
        }

        template <typename OP>
        inline static void MetaData_GCOperatorFP_Masked_Simple(const MetaData* meta, void** data)
        {
            void** cslot = data;
            const char* cmaskop = meta->refmask;
            
            while (*cmaskop)
            {
                char op = *cmaskop++;
                if(op == PTR_FIELD_MASK_SCALAR) 
                {
                    cslot++;
                }    
                else
                {
                    OP{}(*cslot++);
                }
            }
        }

        template <typename OP>
        inline static void MetaData_GCOperatorFP_MaskedEntries_Simple(const MetaData* meta, void** data)
        {
            size_t count = *((size_t*)data);
            uint32_t advancesize = meta->sizeadvance;

            void** slotcurr = (void**)GET_COLLECTION_START_META(data, meta);
            for(size_t i = 0; i < count; ++i)
            {
                void** cslot = slotcurr;
                const char* cmaskop = meta->refmask;

                while (*cmaskop)
                {
                    char op = *cmaskop++;
                    if(op == PTR_FIELD_MASK_SCALAR) 
                    {
                        cslot++;
                    }    
                    else
                    {
                        OP{}(*cslot++);
                    }
                }

                slotcurr += advancesize;
            }
        }

        template <typename OP, typename UOP>
        inline static void MetaData_GCOperatorFP_Masked_WithUnion(const MetaData* meta, void** data)
        {
            void** cslot = data;
            const char* cmaskop = meta->refmask;
            
            while (*cmaskop)
            {
                char op = *cmaskop++;
                if(op == PTR_FIELD_MASK_SCALAR) 
                {
                    cslot++;
                }    
                else if(op == PTR_FIELD_MASK_PTR)
                {
                    OP{}(*cslot++);
                }
                else
                {
                    UOP{}(cslot++);
                }
            }
        }

        template <typename OP, typename UOP>
        inline static void MetaData_GCOperatorFP_MaskedEntries_WithUnion(const MetaData* meta, void** data)
        {
            size_t count = *((size_t*)data);
            uint32_t advancesize = meta->sizeadvance;

            void** slotcurr = (void**)GET_COLLECTION_START_META(data, meta);
            for(size_t i = 0; i < count; ++i)
            {
                void** cslot = slotcurr;
                const char* cmaskop = meta->refmask;

                while (*cmaskop)
                {
                    char op = *cmaskop++;
                    if(op == PTR_FIELD_MASK_SCALAR) 
                    {
                        cslot++;
                    }    
                    else if(op == PTR_FIELD_MASK_PTR)
                    {
                        OP{}(*cslot++);
                    }
                    else
                    {
                        UOP{}(cslot++);
                    }
                }

                slotcurr += advancesize;
            }
        }

        inline static size_t MetaData_ComputeSize_Simple(const MetaData* meta, void* data)
        {
            return sizeof(MetaData) + meta->datasize;
        }

        inline static size_t MetaData_ComputeSize_SimpleCollection(const MetaData* meta, void* data)
        {
            size_t count = *((size_t*)data);
            return sizeof(MetaData) + meta->datasize + BSQ_ALIGN_ALLOC_SIZE(count * meta->sizeentry);
        }
    };
}
