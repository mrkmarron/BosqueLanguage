//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include <cstdlib>
#include <cstdint>
#include <string>

#define NOT_IMPLEMENTED(OP) (BSQ::fail(OP, __FILE__, __LINE__))

#define RUNTIME_ERROR(MSG) (BSQ::fail(OP, __FILE__, __LINE__))
#define BSQ_ABORT(MSG) (BSQ::fail(OP, __FILE__, __LINE__))

namespace BSQ
{
    class MIRType
    {
        xxxx;
    };

    void fail(const char* msg, const char* file, int64_t line, ...)
    {
        exit(1);
    }

    constexpr int32_t  VarTag_Shift       = 48;
    constexpr int32_t  VarTagInline_Shift = 46;

    constexpr uint64_t FloatTag_Value = (((uint64_t)0xFFFCull) << VarTag_Shift);
    constexpr uint64_t AtomTag_Value  = (((uint64_t)0x1i64) << VarTag_Shift);
    
    constexpr uint64_t TrueTagInline_Value  = (((uint64_t)0x1i64) << VarTagInline_Shift);
    constexpr uint64_t FalseTagInline_Value = (((uint64_t)0x2i64) << VarTagInline_Shift);

    constexpr uint64_t ReferenceTag_Mask = (FloatTag_Value | AtomTag_Value);

    constexpr uint64_t TagInline_Mask    = (((uint64_t)0x3i64) << VarTagInline_Shift);
    constexpr uint64_t IntTagInline_Mask  = TagInline_Mask; //becuase the tag part is 0
    constexpr uint64_t BoolTagInline_Mask = (AtomTag_Value | TrueTagInline_Value | FalseTagInline_Value);
    
    constexpr uint64_t k_Nan = 0xFFF8000000000000ull;

    class Value
    {
    private:
        uintptr_t data;

    public:
        Value(uintptr_t cdata) : data(cdata) { ; }

        xxxx;

        inline Value getNoneValue()
        {
            return Value((uintptr_t)0x0);
        }

        inline static bool IsNan(double value)
        {
            uintptr_t nCompare = *((uintptr_t*)(&value));
            return ((~nCompare & 0x7FF0000000000000ull) == 0) & ((nCompare & 0x000FFFFFFFFFFFFFull) != 0);
        }

        inline bool isNone()
        {
            return this->data == (uintptr_t)0x0;
        }

        inline bool isTrue(Value v)
        {
            return v == TrueInline_Value;
        }

        inline bool isFalse(Value v)
        {
            return v == FalseInline_Value;
        }
    };

    inline bool isInlineAtom(Value v)
    {
        return (((uint64_t)v) & AtomTag_Value) != 0;
    }

    inline bool isInlineFloat(Value v)
    {
        return (((uint64_t)v) & FloatTag_Value) != 0;
    }

    inline bool isReference(Value v)
    {
        return (v != NoneInline_Value) & (((uint64_t)v & ReferenceTag_Mask) == 0);
    }

    inline bool isBool(Value v)
    {
        return (((uint64_t)v) & TagInline_Mask) == BoolTagInline_Mask;
    }

    inline bool isInt(Value v)
    {
        return (((uint64_t)v) & TagInline_Mask) == IntTagInline_Mask;
    }

    inline Value boolToValue(bool value)
    {
        return value ? TrueInline_Value : FalseInline_Value;
    }

    inline Value int32ToValue(int32_t value)
    {
        return (Value)(((uintptr_t)(uint32_t)value) | AtomTag_Value);
    }

    inline Value floatToValue(double value)
    {
         if (IsNan(value))
        {
            value = *((double*)(&k_Nan));
        }

        uint64_t val = *((uint64_t*)(&value));
        return (Value)(val ^ FloatTag_Value);
    }

    inline bool valueToBool(Value v)
    {
        return isTrue(v);
    }

    inline int32_t valueToInt32(Value v)
    {
        return (int32_t)((uint64_t)v);
    }

    inline double valueToFloat(Value v)
    {
        uint64_t val = (((uint64_t)v) ^ FloatTag_Value);
        return *((double*)(&val));
    }

    class ReferenceValue
    {
    public:
        const MIRType* vtype;

        ReferenceValue(const MIRType* vtype) : vtype(vtype) { ; }
    };

    class BigIntValue : public ReferenceValue
    {
    public:
        const int64_t val; //TODO: not really a big int yet!!!

        BigIntValue(const MIRType* vtype, int64_t val) : ReferenceValue(vtype), val(val) { ; }
    };

    class StringValue : public ReferenceValue
    {
    public:
        const std::string* val;

        StringValue(const MIRType* vtype, std::string* val) : ReferenceValue(vtype), val(val) { ; }
    };

    class TypedStringValue : public ReferenceValue
    {
    public:
        const MIRType* oftype;
        const std::string* val;

        TypedStringValue(const MIRType* vtype, const MIRType* oftype, std::string* val) : ReferenceValue(vtype), oftype(oftype), val(val) { ; }
    };

    class RegexValue : public ReferenceValue
    {

    };

    class GUIDValue : public ReferenceValue
    {

    };

    class TupleValue : public ReferenceValue
    {

    };

    class RecordValue : public ReferenceValue
    {

    };

    class EntityValue : public ReferenceValue
    {

    };

    class EntityValueSimple : public EntityValue
    {

    };

    class EnumValue : public EntityValue
    {

    };

    class IdKeyValue : public EntityValue
    {

    };

    class ListValue : public EntityValue
    {

    };

    class HashSetValue : public EntityValue
    {

    };

    class HashMapValue : public EntityValue
    {

    };
} // namespace BSQ
