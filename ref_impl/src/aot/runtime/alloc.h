//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include <cstdint>
#include <cstring>

#define GET_ALLOCATION_HEADER(M) ((AllocatorHeader*) (((uint8_t*)M) - sizeof(AllocatorHeader)))

namespace Memory
{    
typedef uint32_t ALLOC_SIZE_TYPE;
typedef uint32_t REF_COUNT_TYPE;
typedef uint32_t MIR_TYPE_KEY;

struct AllocatorHeader
{
    REF_COUNT_TYPE ref_count;
    ALLOC_SIZE_TYPE alloc_size;
    void* mir_type;
};

constexpr ALLOC_SIZE_TYPE power2(ALLOC_SIZE_TYPE v)
{
    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;
    return v;
}

constexpr ALLOC_SIZE_TYPE allocation_size(uint32_t slots) 
{
    return (ALLOC_SIZE_TYPE)(power2((slots == 0 ? 1 : slots) + sizeof(AllocatorHeader)));
}

inline void incRef(void* mem)
{
    (GET_ALLOCATION_HEADER(mem))->ref_count++;
}
inline void* decRef(void* mem)
{
    AllocatorHeader* h = GET_ALLOCATION_HEADER(mem);
    if(h->ref_count == 1)
    {
        return mem;
    }
    else 
    {
        h->ref_count--;
        return nullptr;
    }
}

inline void prepHeader(AllocatorHeader* header, ALLOC_SIZE_TYPE size, void* mirtype)
{
    header->ref_count = 1;
    header->alloc_size = size;
    header->mir_type = mirtype;
}

struct AllocaterTypeBucket
{
    size_t free_count;
    void* entries;
};

class Allocator
{
private:
void** mir_types;
AllocaterTypeBucket* type_segregated_allocs;

public:
template <typename T, MIR_TYPE_KEY tkey, ALLOC_SIZE_TYPE size>
inline T* allocate()
{
    AllocaterTypeBucket& bucket = this->type_segregated_allocs[tkey];
    void* v = bucket.entries;
    if(v != nullptr)
    {
        bucket.entries = *((void**)v);
        bucket.free_count--;
        return (T*)v;
    }
    else
    {
        return this->allocate_slow<T, tkey, size>();
    }
} 

template <typename T, MIR_TYPE_KEY tkey, ALLOC_SIZE_TYPE size>
T* allocate_slow()
{
    void* nv = malloc(size);
    memset(nv, 0, size);
    prepHeader(nv, size, mir_types[tkey]);

    return (T*)(nv + sizeof(AllocatorHeader));
}

inline void release(void* mem, MIR_TYPE_KEY tkey)
{
    AllocaterTypeBucket& bucket = this->type_segregated_allocs[tkey];
    *((void**)mem) = bucket.entries;
    bucket.entries = mem;
    bucket.free_count++;
}
};
}
