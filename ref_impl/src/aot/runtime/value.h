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

        virtual ~Value() { ; }
    };

    class BoxedBool : public Value
    {
    public:
        const bool bval;

        BoxedBool() : Value(), bval(false) { ; }
        BoxedBool(const RuntimeType* vtype, bool val) : Value(vtype), bval(val) { ; }

        BoxedBool(const BoxedBool&) = default;
        BoxedBool& operator=(const BoxedBool&) = default;

        virtual ~BoxedBool() { ; }

        inline static std::shared_ptr<BoxedBool> box(bool bv) { return std::make_shared<BoxedBool>(s_typeenv.getBoolType(), bv); }
        inline bool unbox() const { return this->bval; }
    };

    class BoxedInt : public Value
    {
    public:
        const int64_t ival;

        BoxedInt() : Value(), ival(false) { ; }
        BoxedInt(const RuntimeType* vtype, int64_t val) : Value(vtype), ival(val) { ; }

        BoxedInt(const BoxedInt&) = default;
        BoxedInt& operator=(const BoxedInt&) = default;

        virtual ~BoxedInt() { ; }

        inline static std::shared_ptr<BoxedInt> box(int64_t iv) { return std::make_shared<BoxedInt>(s_typeenv.getIntType(), iv); }
        inline bool unbox() const { return this->ival; }
    };

    class BoxedString : public Value
    {
    public:
        const std::shared_ptr<std::string> sval;

        BoxedString() : Value(), sval(nullptr) { ; }
        BoxedString(const RuntimeType* vtype, std::shared_ptr<std::string> val) : Value(vtype), sval(val) { ; }

        BoxedString(const BoxedString&) = default;
        BoxedString& operator=(const BoxedString&) = default;

        virtual ~BoxedString() { ; }

        inline static std::shared_ptr<BoxedString> box(std::shared_ptr<std::string> sv) { return std::make_shared<BoxedString>(s_typeenv.getStringType(), sv); }
        inline std::shared_ptr<std::string> unbox() const { return this->sval; }
    };

    class BoxedFloat : public Value
    {
    public:
        const double fval;

        BoxedFloat() : Value(), fval() { ; }
        BoxedFloat(const RuntimeType* vtype, double val) : Value(vtype), fval(val) { ; }

        BoxedFloat(const BoxedFloat&) = default;
        BoxedFloat& operator=(const BoxedFloat&) = default;

        virtual ~BoxedFloat() { ; }

        inline static std::shared_ptr<BoxedFloat> box(double fv) { return std::make_shared<BoxedFloat>(s_typeenv.getFloatType(), fv); }
        inline double unbox() const { return this->fval; }
    };
} 
