//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating the various Result types
//

#ifndef Ty
#define Ty TName
#define T int
#define T_NAME result
#define E int
#define E_NAME error
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define CALL_RET_T(X, S)
#define INC_RC_E(X)
#define DEC_RC_E(X)
#define CALL_RET_E(X, S)
#endif

class Ty : public BSQRef
{
    bool success;
    T T_NAME;
    E E_NAME;

    Ty() : BSQRef() { ; }
    Ty(bool success, T& result, E error) : BSQRef(), success(success), T_NAME(result), E_NAME(error) { ; }

    Ty(const Ty& src) : BSQRef(), success(src.success), T_NAME(src.T_NAME), E_NAME(src.E_NAME) 
    { 
        ; 
    }

    Ty& operator=(const Ty& src)
    {
        this->success = src.success;
        this->T_NAME = src.T_NAME;
        this->E_NAME = src.E_NAME;
        return *this;
    }

    virtual ~Ty() = default;

    virtual void destroy() 
    {
        DEC_RC_T(this->T_NAME);
        DEC_RC_E(this->E_NAME);
    }

    Ty* processBox(BSQRefScope& scope) 
    {
        INC_RC_T(this->T_NAME);
        INC_RC_E(this->E_NAME);

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->success, this->T_NAME, this->E_NAME);
    }

    void processCallReturn(BSQRefScope& scaller) 
    {
        CALL_RET_T(this->T_NAME, scaller);
        CALL_RET_E(this->E_NAME, scaller);
    }
};

#undef Ty 
#undef T
#undef T_NAME
#undef E
#undef E_NAME
#undef INC_RC_T
#undef DEC_RC_T
#undef CALL_RET_T
#undef INC_RC_E
#undef DEC_RC_E
#undef CALL_RET_E
