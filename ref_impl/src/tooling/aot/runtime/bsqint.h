//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#pragma once

#include <cstdint>

#define BIG_INT_VALUE(X) (X.isInt() ? BigInt(X.getInt()) : *((X).getBigInt()))

//A big integer class for supporting Bosque -- right now it does not do much
class BigInt
{
    //TODO: want to refcount this 

public:
    BigInt() { ; }
    BigInt(int64_t value) { ; }
    BigInt(const char* bigstr) { ; }

    ~BigInt()
    {
        this->release();
    }

    size_t hash() const
    {
        return 0;
    }

    BigInt* copy() const
    {
        return nullptr;
    }

    void release()
    {
        ;
    }

    bool isZero() const
    {
        return false;
    }

    BigInt* negate() const
    {
        return nullptr;
    }

    static bool eq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool neq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool lt(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool lteq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

     static bool gt(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static bool gteq(const BigInt& l, const BigInt& r)
    {
        return false;
    }

    static BigInt* add(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* sub(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* mult(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* div(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }

    static BigInt* mod(const BigInt &l, const BigInt &r)
    {
        return nullptr;
    }
};

class BSQInt
{
private:
    void* data; 

public:
    inline bool isInt() const
    {
        return (((int64_t)this->data) & 0x1) == 1;
    }

    inline int32_t getInt() const
    {
        return (int32_t)(((int64_t)this->data) >> 32);
    }

    inline BigInt* getBigInt() const
    {
        return reinterpret_cast<BigInt*>(this->data);
    }

    inline int64_t getInt64() const
    {
        return reinterpret_cast<int64_t>(this->data) >> 32;
    }

    BSQInt() : data((void*)((int64_t)0x1)) { ; }

    BSQInt(int32_t value) : data(nullptr) 
    { 
        this->data = (void*)((((uint64_t)value) << 32) | 0x1);
    }

    BSQInt(BigInt* value) : data((void*)value) 
    { 
        ; 
    }

    BSQInt(const BSQInt& src)
    { 
        this->data = src.isInt() ? src.data : src.getBigInt()->copy();
    }

    BSQInt& operator=(const BSQInt& src)
    {
        if (&src != this)
        {
            if (!this->isInt())
            {
                this->getBigInt()->release();
            }
            this->data = src.isInt() ? src.data : src.getBigInt()->copy();
        }
        return *this;
    }

    BSQInt(BSQInt&& src) : data(src.data)
    { 
        src.data = (void*)((int64_t)0x1);
    }

    BSQInt& operator=(BSQInt&& src)
    {
        if (&src != this)
        {
            if (!this->isInt())
            {
                this->getBigInt()->release();
            }
            this->data = src.data;

            src.data = (void*)((int64_t)0x1);
        }
        return *this;
    }

    ~BSQInt()
    {
        if(!this->isInt())
        {
            this->getBigInt()->release();
        }
    }

    inline bool isZero() const
    {
        if(this->isInt())
        {
            return this->getInt() == 0;
        }
        else
        {
            return this->getBigInt()->isZero();
        }
    }

    inline BSQInt negate() const
    {
        if(this->isInt())
        {
            return BSQInt(-this->getInt());
        }
        else
        {
            return BSQInt(this->getBigInt()->negate());
        }
    }

    inline friend bool operator==(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() == r.getInt();
        }
        else
        {
            return BigInt::eq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }    
    }

    inline friend bool operator!=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() != r.getInt();
        }
        else
        {
            return BigInt::neq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }    
    }

    inline friend bool operator<(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() < r.getInt();
        }
        else
        {
            return BigInt::lt(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }   
    }

    inline friend bool operator<=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() <= r.getInt();
        }
        else
        {
            return BigInt::lteq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        } 
    }

    inline friend bool operator>(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() > r.getInt();
        }
        else
        {
            return BigInt::gt(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        }   
    }

    inline friend bool operator>=(const BSQInt& l, const BSQInt& r)
    {
        if(l.isInt() && r.isInt())
        {
            return l.getInt() >= r.getInt();
        }
        else
        {
            return BigInt::gteq(BIG_INT_VALUE(l), BIG_INT_VALUE(r));
        } 
    }

    inline friend BSQInt operator+(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() + r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::add(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator-(const BSQInt& l, const BSQInt& r)
    {
       if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() - r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::sub(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator*(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() * r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::mult(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator/(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() / r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::div(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }

    inline friend BSQInt operator%(const BSQInt& l, const BSQInt& r)
    {
        if (l.isInt() && r.isInt())
        {
            int64_t res = l.getInt64() % r.getInt64();
            return (INT32_MIN <= res && res < INT32_MAX) ? BSQInt(res) : BSQInt(new BigInt(res));
        }
        else
        {
            return BSQInt(BigInt::mod(BIG_INT_VALUE(l), BIG_INT_VALUE(r)));
        }
    }
};
