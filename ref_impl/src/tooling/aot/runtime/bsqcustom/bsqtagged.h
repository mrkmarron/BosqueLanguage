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
#define V int
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
    K key;
    V value;

    Ty() : BSQRef() { ; }
    Ty(K& k, V& u) : BSQRef(), key(k), value(u) { ; }

    Ty(const Ty& src) : BSQRef(), key(src.key), value(src.value) 
    { 
        ; 
    }

    Ty& operator=(const Ty& src)
    {
        this->key = src.key;
        this->value = src.value;
        return *this;
    }

    virtual ~Ty() = default;

    virtual void destroy() 
    {
        DEC_RC_K(this->key);
        DEC_RC_V(this->value);
    }

    Ty* processBox(BSQRefScope& scope) 
    {
        INC_RC_K(this->key);
        INC_RC_V(this->value);

        return BSQ_NEW_ADD_SCOPE(scope, Ty, this->key, this->value);
    }

    void processCallReturn(BSQRefScope& scaller) 
    {
        CALL_RET_K(this->key, scaller);
        CALL_RET_V(this->value, scaller);
    }
};

#undef Ty
#undef K
#undef V
#undef INC_RC_K
#undef DEC_RC_K
#undef CALL_RET_K
#undef INC_RC_V
#undef DEC_RC_V
#undef CALL_RET_V
