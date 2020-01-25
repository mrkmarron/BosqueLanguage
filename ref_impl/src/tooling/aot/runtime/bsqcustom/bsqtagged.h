//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating the various MapEntry types
//

#ifndef Ty
#define Ty TName
#define K int
#define K_NAME key
#define V int
#define V_NAME value
#define INC_RC_K(X)
#define DEC_RC_K(X)
#define CALL_RET_K(X, S)
#define INC_RC_V(X)
#define DEC_RC_V(X)
#define CALL_RET_V(X, S)
#endif

class Ty : public BSQRef
{
public:
    K K_NAME;
    V V_NAME;

    Ty() : BSQRef() { ; }
    Ty(K& k, V& u) : BSQRef(), K_NAME(k), V_NAME(u) { ; }

    Ty(const Ty& src) : BSQRef(), K_NAME(src.K_NAME), V_NAME(src.V_NAME) 
    { 
        ; 
    }

    Ty& operator=(const Ty& src)
    {
        this->K_NAME = src.K_NAME;
        this->V_NAME = src.V_NAME;
        return *this;
    }

    virtual ~Ty() = default;

    virtual void destroy() 
    {
        DEC_RC_K(this->K_NAME);
        DEC_RC_V(this->V_NAME);
    }

    Ty* processBox(BSQRefScope& scope) 
    {
        INC_RC_K(this->K_NAME);
        INC_RC_V(this->V_NAME);

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->K_NAME, this->V_NAME);
    }

    void processCallReturn(BSQRefScope& scaller) 
    {
        CALL_RET_K(this->K_NAME, scaller);
        CALL_RET_V(this->V_NAME, scaller);
    }
};

#undef Ty
#undef K
#undef K_NAME
#undef V
#undef V_NAME
#undef INC_RC_K
#undef DEC_RC_K
#undef CALL_RET_K
#undef INC_RC_V
#undef DEC_RC_V
#undef CALL_RET_V
