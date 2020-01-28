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
#define E_NAME error
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define CALL_RET_T(X, S)
#endif

class Ty : public BSQRef
{
    bool success;
    T T_NAME;
    Value E_NAME;

    Ty() : BSQRef() { ; }
    Ty(bool success, T& result, Value error) : BSQRef(), success(success), T_NAME(result), E_NAME(error) { ; }

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
        BSQRef::decrementChecked(this->E_NAME);
    }

    Ty* processBox(BSQRefScope& scope) 
    {
        INC_RC_T(this->T_NAME);
        BSQRef::incrementChecked(this->E_NAME);

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->success, this->T_NAME, this->E_NAME);
    }

    void processCallReturn(BSQRefScope& scaller) 
    {
        CALL_RET_T(this->T_NAME, scaller);
        scaller.processReturnChecked(this->E_NAME);
    }
};

#undef Ty 
#undef T
#undef T_NAME
#undef E_NAME
#undef INC_RC_T
#undef DEC_RC_T
#undef CALL_RET_T
