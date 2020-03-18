//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

//
//This file is a template for instatiating the various MapEntry types
//

#ifndef Ty
#define Ty TName
#define T int
#define TOps TName_Ops
#define INC_RC_T(X)
#define DEC_RC_T(X)
#define FDisplay(X)
#define BSCOPE
#endif

class TOps
{
public:
    template <uint16_t n>
    static Ty* createFromSingle(BSQRefScope& scope, MIRNominalTypeEnum ntype, const T(&values)[n])
    {
        T* entries = malloc(sizeof(T) * n);

        for (int i = 0; i < n; i++)
        {
            entries[i] = INC_RC_T(values[i]));
        }

        return BSQ_NEW_ADD_SCOPE(scope, Ty, ntype, n, entries);
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

        std::u32string ls(U"{");
        for (size_t i = 0; i < this->size; ++i)
        {
            if (i != 0)
            {
                ls += U", ";
            }

            BSQRefScope BSCOPE;
            ls += FDisplay(this->entries[i]);
        }
        ls += U"}";

        return ls;
    }

    template <typename LambdaP>
    static bool list_all(Ty* l, LambdaP p)
    {
        for(int64_t i = 0; i < l->size; ++i)
        {
            if(!p(l->entries[i]))
            {
                return false;
            }
        }
        return true;
    }

    template <typename LambdaP>
    static int64_t list_count(Ty* l, LambdaP p)
    {
        int64_t count = 0;
        for(int64_t i = 0; i < l->size; ++i)
        {
            if(p(l->entries[i]))
            {
                count++;
            }
        }
        return count;
    }

    template <typename LambdaP>
    inline static int64_t list_indexof(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        for(int64_t i = s; i < e; ++i)
        {
            if(p(l->entries[i]))
            {
                i;
            }
        }
        return l->size;
    }

    template <typename LambdaP>
    inline static int64_t list_indexoflast(Ty* l, int64_t s, int64_t e, LambdaP p)
    {
        for(int64_t i = e; i >= s; --i)
        {
            if(p(l->entries[i]))
            {
                i;
            }
        }
        return s - 1;
    }
};

#undef Ty
#undef T
#undef INC_RC_T
#undef DEC_RC_T
#undef BSCOPE
#undef FDisplay
