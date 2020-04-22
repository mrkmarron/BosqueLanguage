;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 10000)

(declare-datatypes (
      (StructuralSpecialTypeInfo 0)
    ) (
    ( (StructuralSpecialTypeInfo@cons (StructuralSpecialTypeInfo$PODType Bool) (StructuralSpecialTypeInfo$APIType Bool) (StructuralSpecialTypeInfo$KeyType Bool) (StructuralSpecialTypeInfo$Parsable Bool)) )
))

(declare-datatypes (
      (bsq_bigint 0)
      (bsq_safestring 0)
      (bsq_stringof 0)
      (bsq_uuid 0)
      (bsq_logicaltime 0)
      (bsq_cryptohash 0)
      (bsq_enum 0)
      (bsq_keytuple 0)
      (bsq_keyrecord 0)
      (bsq_idkey 0)
      (BKeyValue 0)
    ) (
    ( (bsq_bigint@cons (bsq_bigint_value Int)) )
    ( (bsq_safestring@cons (bsq_safestring_type String) (bsq_safestring_value String)) )
    ( (bsq_stringof@cons (bsq_stringof_type String) (bsq_stringof_value String)) )
    ( (bsq_uuid@cons (bsq_uuid_value String)) )
    ( (bsq_logicaltime@cons (bsq_logicaltime_value Int)) )
    ( (bsq_cryptohash@cons (bsq_cryptohash String)) )
    ( (bsq_enum@cons (bsq_enum_type String) (bsq_enum_value Int)) )
    ( (bsq_keytuple@cons (bsq_keytuple_concepts StructuralSpecialTypeInfo) (bsq_keytuple_entries (Array Int BKeyValue))) )
    ( (bsq_keyrecord@cons (bsq_keyrecord_concepts StructuralSpecialTypeInfo) (bsq_keyrecord_entries (Array String BKeyValue))) )
    ( (bsq_idkey@cons (bsq_idkey_type String) (bsq_idkey_value BKeyValue)) )
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_bigint (bsqkey_bigint_value bsq_bigint))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_safestring (bsqkey_safestring_value bsq_safestring))
      (bsqkey_stringof (bsqkey_stringof_value bsq_stringof))
      (bsqkey_uuid (bsqkey_uuid_value bsq_guid))
      (bsqkey_logicaltime (bsqkey_logicaltime_value bsq_logicaltime))
      (bsqkey_cryptohash (bsqkey_cryptohash_value bsq_cryptohash))
      (bsqkey_enum (bsqkey_enum_value bsq_enum))
      (bsqkey_tuple (bsqkey_tuple_value bsq_keytuple))
      (bsqkey_record (bsqkey_record_value bsq_keyrecord))
      (bsqkey_idkey (bsqkey_idkey_value bsq_idkey))
    )
))

(declare-datatypes ( 
    (bsq_buffer 0)
    (bsq_bytebuffer 0)
    (bsq_isotime 0)
    (bsq_regex 0)
    (bsq_structural_entry 0)
    (bsq_tuple 0)
    (bsq_record 0)
    ;;NOMINAL_DECLS_FWD;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_buffer@cons (bsq_buffer_type String) (bsq_buffer_contents String)) )
    ( (bsq_bytebuffer@cons (bsq_bytebuffer_contents (Seq Int))) )
    ( (bsq_isotime@cons (bsq_isotime_value Int)) )
    ( (bsq_regex@cons (bsq_regex_value String)) )
    ( (bsq_structural_entry@clear) (bsq_structural_entry@key (bsq_structural_entry_key BKeyValue)) (bsq_structural_entry@term (bsq_structural_entry_term BTerm)) )
    ( (bsq_tuple@cons (bsq_tuple_concepts StructuralSpecialTypeInfo) (bsq_tuple_entries (Array Int bsq_structural_entry)))  )
    ( (bsq_record@cons (bsq_record_concepts StructuralSpecialTypeInfo) (bsq_record_entries (Array String bsq_structural_entry))) )
    ;;NOMINAL_CONSTRUCTORS;;
    (
      (bsq_object@empty)
    ;;NOMINAL_OBJECT_CONSTRUCTORS;;
    )
    (
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_float64 (bsqterm_float64_value (_ FloatingPoint 11 53)))
      (bsqterm_buffer (bsqterm_buffer_value bsq_buffer))
      (bsqterm_bytebuffer (bsqterm_buffer_value bsq_bytebuffer))
      (bsqterm_isotime (bsqterm_isotime_value bsq_isotime))
      (bsqterm_regex (bsqterm_regex_value bsq_regex))
      (bsqterm_keytuple (bsqterm_keytuple_value bsqkey_tuple))
      (bsqterm_tuple (bsqterm_tuple_value bsq_tuple)) 
      (bsqterm_keyrecord (bsqterm_keyrecord_value bsqkey_record))
      (bsqterm_record (bsqterm_record_value bsq_record))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_value bsq_object))
    )
))

(declare-fun nominalDataKinds (String) Int)
;;NOMINAL_TYPE_TO_DATA_KIND_ASSERTS;;

(declare-const MIRNominalTypeEnum_None String)
(declare-const MIRNominalTypeEnum_Bool String)
(declare-const MIRNominalTypeEnum_Int String)
(declare-const MIRNominalTypeEnum_BigInt String)
(declare-const MIRNominalTypeEnum_Float64 String)
(declare-const MIRNominalTypeEnum_String String)
(declare-const MIRNominalTypeEnum_UUID String)
(declare-const MIRNominalTypeEnum_LogicalTime String)
(declare-const MIRNominalTypeEnum_CryptoHash String)
(declare-const MIRNominalTypeEnum_ByteBuffer String)
(declare-const MIRNominalTypeEnum_ISOTime String)
(declare-const MIRNominalTypeEnum_Tuple String)
(declare-const MIRNominalTypeEnum_Record String)
(declare-const MIRNominalTypeEnum_Regex String)

;;SPECIAL_NAME_BLOCK_ASSERTS;;

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) String
  (ite (= keyv bsqkey_none) MIRNominalTypeEnum_None
    (ite (is-bsqkey_bool keyv) MIRNominalTypeEnum_Bool
      (ite (is-bsqkey_int keyv) MIRNominalTypeEnum_Int
        (ite (is-bsqkey_bigint keyv) MIRNominalTypeEnum_BigInt
          (ite (is-bsqkey_string keyv) MIRNominalTypeEnum_String
            (ite (is-bsqkey_safestring keyv) (bsq_safestring_type (bsqkey_safestring_value keyv))
              (ite (is-bsqkey_stringof keyv) (bsq_stringof_type (bsqkey_stringof_value keyv))
                (ite (is-bsqkey_uuid keyv) MIRNominalTypeEnum_UUID
                  (ite (is-bsqkey_logicaltime keyv) MIRNominalTypeEnum_LogicalTime
                    (ite (is-bsqkey_cryptohash keyv) MIRNominalTypeEnum_CryptoHash
                      (ite (is-bsqkey_enum keyv) (bsq_enum_type (bsqkey_enum_value keyv))
                        (ite (is-bsqkey_tuple keyv) MIRNominalTypeEnum_Tuple
                          (ite (is-bsqkey_record keyv) MIRNominalTypeEnum_Record
                            (bsq_idkey_type (bsqkey_idkey_value keyv))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun bsqterm_get_nominal_type ((term BTerm)) String
  (ite (is-bsqterm_float64) MIRNominalTypeEnum_Float64
    (ite (is-bsqterm_key term) (bsqkey_get_nominal_type (bsqterm_key_value term))
      (ite (is-bsqterm_buffer term) (bsq_buffer_type (bsqterm_buffer_value term))
        (ite (is-bsqterm_bytebuffer term) MIRNominalTypeEnum_ByteBuffer
          (ite (is-bsqterm_isotime term) MIRNominalTypeEnum_ISOTime
            (ite (is-bsqterm_regex term) MIRNominalTypeEnum_Regex
              (ite (is-bsqterm_tuple term) MIRNominalTypeEnum_Tuple
                (ite (is-bsqterm_record term) MIRNominalTypeEnum_Record
                  (bsqterm_object_type term)
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun bsqkeyless_basetypes ((k1 BKeyValue) (k2 BKeyValue)) Bool
  (let ((k1t (bsqkey_get_nominal_type k1)) (k2t (bsqkey_get_nominal_type k2)))
    (ite (not (str.= k1t k2t))
      (str.< k1t k2t)
      
      (ite (and (= k1 bsqkey_none) (= k2 bsqkey_none)) false
        (ite (and (is-bsqkey_bool k1) (is-bsqkey_bool k2)) (and (not (bsqkey_bool_value k1)) (bsqkey_bool_value k2))
          (ite (and (is-bsqkey_int k1) (is-bsqkey_int k2)) (< (bsqkey_int_value k1) (bsqkey_int_value k2))
            (ite (and (is-bsqkey_bigint k1) (is-bsqkey_bigint k2)) (< (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
              (ite (and (is-bsqkey_string k1) (is-bsqkey_string k2)) (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
                (ite (and (is-bsqkey_safestring k1) (is-bsqkey_safestring k2)) (str.< (bsq_safestring_value k1) (bsq_safestring_value k2))
                  (ite (and (is-bsqkey_stringof k1) (is-bsqkey_stringof k2)) (str.< (bsqkey_stringof_value k1) (bsqkey_stringof_value k2))
                    (ite (and (is-bsqkey_uuid k1) (is-bsqkey_uuid k2)) (< (bsqkey_uuid_value k1) (bsqkey_uuid_value k2))
                      (ite (and (is-bsqkey_logicaltime k1) (is-bsqkey_logicaltime k2)) (< (bsqkey_logicaltime_value k1) (bsqkey_logicaltime_value k2))
                        (ite (and (is-bsqkey_cryptohash k1) (is-bsqkey_cryptohash k2)) (< (bsqkey_cryptohash k1) (bsqkey_cryptohash k2))
                          (ite (is-bsqkey_enum keyv) (bsq_enum_type (bsqkey_enum_value keyv))
                        (ite (is-bsqkey_tuple keyv) MIRNominalTypeEnum_Tuple
                          (ite (is-bsqkey_record keyv) MIRNominalTypeEnum_Record
                            (bsq_idkey_type (bsqkey_idkey_value keyv))
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
      
    )
  )
)

(define-fun getStructuralSpecialTypeInfoTerm ((term BTerm)) StructuralSpecialTypeInfo
  (ite (= term bsqterm@clear) 3
    (ite (is-bsqterm_tuple term) (bsqterm_tuple_flag (bsqterm_tuple_value term))
      (ite (is-bsqterm_record term) (bsqterm_record_flag (bsqterm_record_value term))
        (nominalDataKinds (bsqterm_get_nominal_type term))
      )
    )
  )
)

(define-fun getStructuralSpecialTypeInfoBKey ((term BKeyValue)) StructuralSpecialTypeInfo
  (ite (= term bsqterm@clear) 3
    (ite (is-bsqterm_tuple term) (bsqterm_tuple_flag (bsqterm_tuple_value term))
      (ite (is-bsqterm_record term) (bsqterm_record_flag (bsqterm_record_value term))
        (nominalDataKinds (bsqterm_get_nominal_type term))
      )
    )
  )
)

(define-fun mergeStructuralSpecialTypeInfo


;;EPHEMERAL_DECLS;;

(declare-const bsqterm_none BTerm)
(assert (= bsqterm_none (bsqterm_key bsqkey_none)))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm@clear)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm@clear)))

;;EMPTY_CONTENT_ARRAY_DECLS;;

(declare-datatypes (
      (ErrorCode 0)
      ;;RESULTS_FWD;;
    ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id String)) )
    ;;RESULTS;;
))

;;current implementation is simple uninterpreted function -- want to implement these in core runtime with bounded checkable impl
(declare-fun stroi (String) Int)

;;current implementation is simple uninterpreted function -- maybe want to make these return a non-decidable error (or have bounded checkable impl)
(declare-fun mult_op (Int Int) Int) 
(declare-fun div_op (Int Int) Int)
(declare-fun mod_op (Int Int) Int)

(declare-const mirconceptsubtypearray_empty (Array String Bool))
(assert (= mirconceptsubtypearray_empty ((as const (Array String Bool)) false)))

;;CONCEPT_SUBTYPE_RELATION_DECLARE;;

;;SUBTYPE_DECLS;;

;;VFIELD_ACCESS;;

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
