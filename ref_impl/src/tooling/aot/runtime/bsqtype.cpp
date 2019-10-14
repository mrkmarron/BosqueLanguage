//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
#include "bsqtype.h"

namespace BSQ
{
const std::vector<MIRTypeTuple> g_tupleTypes = {
#define TUPLE_TYPE_DECL_OP(TDECL) TDECL
#include "generated/tuple_type_decls.h"
#undef TUPLE_TYPE_DECL_OP

};

const std::vector<MIRTypeRecord> g_recordTypes = {
#define RECORD_TYPE_DECL_OP(TDECL) TDECL
#include "generated/record_type_decls.h"
#undef RECORD_TYPE_DECL_OP
};

const std::vector<MIRTypeOption*> g_types_option = {
    new MIRTypeEntity(MIRNominalTypeEnum::NSCore$cc$None),
    new MIRTypeEntity(MIRNominalTypeEnum::NSCore$cc$Bool),
    new MIRTypeEntity(MIRNominalTypeEnum::NSCore$cc$Int),
    new MIRTypeEntity(MIRNominalTypeEnum::NSCore$cc$String),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Any}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Some}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Truthy}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Parsable}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Tuple}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Record}),
    new MIRTypeConcept({MIRNominalTypeEnum::NSCore$cc$Object}),
#define TYPE_OPTION_DECL_OP(TDECL) TDECL
#include "generated/type_option_decls.h"
#undef TYPE_OPTION_DECL_OP
};

const std::vector<MIRType> g_types = {
    MIRType(MIRTypeEnum::NSCore$cc$None, g_types_option[(int)MIRTypeEnum::NSCore$cc$None]),
    MIRType(MIRTypeEnum::NSCore$cc$Bool, g_types_option[(int)MIRTypeEnum::NSCore$cc$Bool]),
    MIRType(MIRTypeEnum::NSCore$cc$Int, g_types_option[(int)MIRTypeEnum::NSCore$cc$Int]),
    MIRType(MIRTypeEnum::NSCore$cc$String, g_types_option[(int)MIRTypeEnum::NSCore$cc$String]),
    
    MIRType(MIRTypeEnum::NSCore$cc$Any, g_types_option[(int)MIRTypeEnum::NSCore$cc$Any]),
    MIRType(MIRTypeEnum::NSCore$cc$Some, g_types_option[(int)MIRTypeEnum::NSCore$cc$Some]),
    MIRType(MIRTypeEnum::NSCore$cc$Truthy, g_types_option[(int)MIRTypeEnum::NSCore$cc$Truthy]),
    MIRType(MIRTypeEnum::NSCore$cc$Parsable, g_types_option[(int)MIRTypeEnum::NSCore$cc$Parsable]),
    MIRType(MIRTypeEnum::NSCore$cc$Tuple, g_types_option[(int)MIRTypeEnum::NSCore$cc$Tuple]),
    MIRType(MIRTypeEnum::NSCore$cc$Record, g_types_option[(int)MIRTypeEnum::NSCore$cc$Record]),
    MIRType(MIRTypeEnum::NSCore$cc$Object, g_types_option[(int)MIRTypeEnum::NSCore$cc$Object]),
#define TYPE_DECL_OP(TDECL) TDECL
#include "generated/type_decls.h"
#undef TYPE_DECL_OP
};

const std::set<std::pair<MIRNominalTypeEnum, MIRNominalTypeEnum>> g_nominalSubtypes = {
#define NOMINAL_SUBTYPE_OP(T, U) {T, U},
#include "generated/nominal_subtypes.h"
#undef NOMINAL_SUBTYPE_OP
};
} // namespace BSQ
