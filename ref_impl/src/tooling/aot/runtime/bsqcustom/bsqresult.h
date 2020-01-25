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
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define CALL_RET_T(X, S)
#endif

class Ty : public BSQRef
{
    bool success;
    T result;
    Value error;

    Ty() : BSQRef() { ; }
    Ty(bool success, T& result, Value error) : BSQRef(), success(success), result(result), error(error) { ; }

    Ty(const Ty& src) : BSQRef(), success(src.success), result(src.result), error(src.error) 
    { 
        ; 
    }

    Ty& operator=(const Ty& src)
    {
        this->success = src.success;
        this->result = src.result;
        this->error = src.error;
        return *this;
    }

    virtual ~Ty() = default;

    virtual void destroy() 
    {
        DEC_RC_T(this->result);
        BSQRef::decrementChecked(this->error);
    }

    Ty* processBox(BSQRefScope& scope) 
    {
        INC_RC_T(this->result);
        BSQRef::incrementChecked(this->error);

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->success, this->result, this->error);
    }

    void processCallReturn(BSQRefScope& scaller) 
    {
        CALL_RET_T(this->success, scaller);
        scaller.processReturnChecked(this->error);
    }
};

#undef Ty
#undef T
#undef INC_RC_K
#undef DEC_RC_K
#undef CALL_RET_K
#undef INC_RC_ERR
#undef DEC_RC_ERR
#undef CALL_RET_ERR
