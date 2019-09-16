//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "common.h"

 namespace BSQ
 {
    class MIRTypeOption
    {
        xxxx;
    };

    class MIRTypeEntity : public MIRTypeOption
    {
        xxxx;
    };

    class MIRTypeConcept : public MIRTypeOption
    {
        xxxx;
    };
    
    class MIRTypeTuple : public MIRTypeOption
    {
        xxxx;
    };

    class MIRTypeRecord : public MIRTypeOption
    {
        xxxx;
    };

    class MIRType
    {
        xxxx;
    };

    class RuntimeType
    {
        xxxx;
    };

    class RuntimeEntityType : public RuntimeType
    {
        xxxx;
    };

    class RuntimeTupleType : public RuntimeType
    {
        xxxx;
    };

    class RuntimeRecordType : public RuntimeType
    {
        xxxx;
    };

    class RuntimeTypeEnvironment
    {
    private:
        std::map<std::string, MIRType*> mirTypeMap;
        std::map<std::string, RuntimeType*> runtimeTypeMap;

        RuntimeType* noneType;
        RuntimeType* boolType;
        RuntimeType* intType;
        RuntimeType* stringType;
        RuntimeType* floatType;

    public:
        const RuntimeType* getNoneType() const { return this->noneType; }
        const RuntimeType* getBoolType() const { return this->boolType; }
        const RuntimeType* getIntType() const { return this->intType; }
        const RuntimeType* getStringType() const { return this->stringType; }
        const RuntimeType* getFloatType() const { return this->floatType; }
    };

    extern RuntimeTypeEnvironment s_typeenv;
 }
