//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating List values
//

#ifndef Ty
#define Ty TName
#define T int
#define DEC_RC_T(X)
#endif

class Ty : public BSQObject {
public:
    int64_t size;
    T* entries;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), size(0), entries(nullptr) { ; }
    Ty(MIRNominalTypeEnum ntype, int64_t size, T* vals) : BSQObject(ntype), size(size), entries(vals) { ; }

    virtual ~Ty()
    {
        free(this->entries);
    }

    virtual void destroy()
    {
        for(size_t i = 0; i < this->size; ++i)
        {
            DEC_RC_T(this->entries[i]);
        }
    }
};

#undef Ty
#undef T
#undef DEC_RC_T
