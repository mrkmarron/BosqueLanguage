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
#define FDisplay(X)
#define BSCOPE
#endif

class Ty : public BSQObject {
public:
    std::vector<T> entries;

    Ty(MIRNominalTypeEnum ntype) : BSQObject(ntype), entries() { ; }
    Ty(MIRNominalTypeEnum ntype, std::vector<T>&& vals) : BSQObject(ntype), entries(move(vals)) { ; }

    virtual ~Ty()
    {
        ;
    }

    virtual void destroy()
    {
        std::for_each(this->entries.begin(), this->entries.end(), [](T& v) -> void {
            DEC_RC_T(v);
        });
    }

    virtual std::u32string display() const
    {
        std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;

        std::u32string ls(U"{");
        BSQRefScope BSCOPE;
        for (size_t i = 0; i < this->entries.size(); ++i)
        {
            if (i != 0)
            {
                ls += U", ";
            }
            ls += FDisplay(this->entries[i]);
        }
        ls += U"}";

        return ls;
    }
};

#undef Ty
#undef T
#undef DEC_RC_T
#undef FDisplay
#undef BSCOPE
