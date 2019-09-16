//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"
#include "mirtype.h"

namespace BSQ
{
    typedef std::pair<std::shared_ptr<std::string>, uint64_t> GUID;

    class Value
    {
    public:
        const RuntimeType* vtype;

        Value(): vtype(nullptr) { ; }
        Value(const RuntimeType* vtype) : vtype(vtype) { ; }

        Value(const Value&) = default;
        Value& operator=(const Value&) = default;

        Value(Value&&) = default;
        Value& operator=(Value&&) = default;

        virtual ~Value() { ; }
    };

    class BoxedBool : public Value
    {
    public:
        bool bval;

        BoxedBool() : Value(), bval(false) { ; }
        BoxedBool(const RuntimeType* vtype, bool val) : Value(vtype), bval(val) { ; }

        BoxedBool(const BoxedBool&) = default;
        BoxedBool& operator=(const BoxedBool&) = default;

        BoxedBool(BoxedBool&&) = default;
        BoxedBool& operator=(BoxedBool&&) = default;

        virtual ~BoxedBool() { ; }

        inline std::shared_ptr<BoxedBool> box(bool bv) { return std::make_shared<BoxedBool>(s_typeenv.getBoolType(), bv); }
        inline bool unbox(std::shared_ptr<BoxedBool> bv) { return bv->bval; }
    };

    class BoxedInt : public Value
    {
    public:
        int64_t ival;

        BoxedInt() : Value(), ival(false) { ; }
        BoxedInt(const RuntimeType* vtype, int64_t val) : Value(vtype), ival(val) { ; }

        BoxedInt(const BoxedInt&) = default;
        BoxedInt& operator=(const BoxedInt&) = default;

        BoxedInt(BoxedInt&&) = default;
        BoxedInt& operator=(BoxedInt&&) = default;

        virtual ~BoxedInt() { ; }

        inline std::shared_ptr<BoxedInt> box(int64_t iv) { return std::make_shared<BoxedInt>(s_typeenv.getIntType(), iv); }
        inline bool unbox(std::shared_ptr<BoxedInt> iv) { return iv->ival; }
    };

    class BoxedString : public Value
    {
    public:
        std::shared_ptr<std::string> sval;

        BoxedString() : Value(), sval(nullptr) { ; }
        BoxedString(const RuntimeType* vtype, std::shared_ptr<std::string> val) : Value(vtype), sval(val) { ; }

        BoxedString(const BoxedString&) = default;
        BoxedString& operator=(const BoxedString&) = default;

        BoxedString(BoxedString&&) = default;
        BoxedString& operator=(BoxedString&&) = default;

        virtual ~BoxedString() { ; }

        inline std::shared_ptr<BoxedString> box(std::shared_ptr<std::string> sv) { return std::make_shared<BoxedString>(s_typeenv.getStringType(), sv); }
        inline std::shared_ptr<std::string> unbox(std::shared_ptr<BoxedString> sv) { return sv->sval; }
    };

    class BoxedFloat : public Value
    {
    public:
        double fval;

        BoxedFloat() : Value(), fval() { ; }
        BoxedFloat(const RuntimeType* vtype, double val) : Value(vtype), fval(val) { ; }

        BoxedFloat(const BoxedFloat&) = default;
        BoxedFloat& operator=(const BoxedFloat&) = default;

        BoxedFloat(BoxedFloat&&) = default;
        BoxedFloat& operator=(BoxedFloat&&) = default;

        virtual ~BoxedFloat() { ; }

        inline std::shared_ptr<BoxedFloat> box(double fv) { return std::make_shared<BoxedFloat>(s_typeenv.getFloatType(), fv); }
        inline double unbox(std::shared_ptr<BoxedFloat> fv) { return fv->fval; }
    };
} 
