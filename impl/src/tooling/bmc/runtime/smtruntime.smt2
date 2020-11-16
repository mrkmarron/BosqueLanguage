;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi true) ; enable model-based quantifier instantiation
(set-option :smt.macro-finder true)

(set-option :timeout 10000)

;;
;; Type Tags
;;

xxxxx --- decl kind and distinct decl

(declare-const TypeTag_None String)
(declare-const TypeTag_Bool String)
(declare-const TypeTag_Int String)
(declare-const TypeTag_Nat String)
(declare-const TypeTag_BigInt String)
(declare-const TypeTag_BigNat String)
(declare-const TypeTag_Float String)
(declare-const TypeTag_Decimal String)
(declare-const TypeTag_String String)
(declare-const TypeTag_Regex String)
(declare-const TypeTag_GeneralTuple String)
(declare-const TypeTag_GeneralRecord String)

;;TYPE_TAG_DECLS;;

xxxxx --- decl kind and distinct decl

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (bsq_none 0)
      ; Bool -> Bool
      ; Int -> Int
      ; Nat -> Int
      ; BigInt -> Int
      ; BigNat -> Int
      ; Float -> Float
      ; Decimal -> Float
      ; String -> (Seq Int)
    ) (
    ( (bsq_none@cons) )
))

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      (bsq_keytuple 0)
      (bsq_keytuple_entry 0)
      (bsq_keyrecord 0)
      (bsq_keyrecord_entry 0)
      ;;KEY_TYPE_DECLS;;
      (bsq_keytype 0)
      (BKey 0)
    ) (
    ( (bsq_keytuple@cons (bsq_keytuple_entries (Array Int bsq_keytype))) )
    ( (bsq_keytuple_entry@empty) (bsq_keytuple_entry@cons (bsq_keytuple_entry_value bsq_keytype)) )
    ( (bsq_keyrecord@cons (bsq_keyrecord_entries (Array String bsq_keytype))) )
    ( (bsq_keyrecord_entry@empty) (bsq_keyrecord_entry@cons (bsq_keyrecord_entry_value bsq_keytype)) )
    ;;KEY_TYPE_CONSTRUCTORS;;
    (
      (bsqkey_none@cons) 
      (bsqkey_bool@cons (bsqkey_bool_value Bool))
      (bsqkey_int@cons (bsqkey_int_value Int))
      (bsqkey_nat@cons (bsqkey_nat_value Int))
      (bsqkey_bigint@cons (bsqkey_bigint_value Int))
      (bsqkey_bignat@cons (bsqkey_bignat_value Int))
      (bsqkey_string@cons (bsqkey_string_value String))
      (bsqkey_keytuple@cons (bsqkey_keytuple_value bsq_keytuple))
      (bsqkey_keyrecord@cons (bsqkey_keyrecord_value bsq_keyrecord))
      ;;KEY_TYPE_BOXING;;
    )
    ( (BKey@cons (BKey_type TypeTag) (BKey_value bsq_keytype)) )
))

;;
;; Any Concept datatypes
;;
(declare-datatypes ( 
    (bsq_tuple 0)
    (bsq_record 0)
    ;;NOMINAL_DECLS_FWD;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_buffer@cons (bsq_buffer_type Int) (bsq_buffer_contents String)) )
    ( (bsq_bufferof@cons (bsq_bufferof_type Int) (bsq_bufferof_contents String)) )
    ( (bsq_bytebuffer@cons (bsq_bytebuffer_contents (Seq Int))) )
    ( (bsq_isotime@cons (bsq_isotime_value Int)) )
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ( (bsq_tuple@cons (bsq_tuple_concepts StructuralSpecialTypeInfo) (bsq_tuple_entries (Array Int BTerm)))  )
    ( (bsq_record@cons (bsq_record_concepts StructuralSpecialTypeInfo) (bsq_record_entries (Array String BTerm))) )
    ;;NOMINAL_CONSTRUCTORS;;
    (
      (bsq_object@empty)
    ;;NOMINAL_OBJECT_CONSTRUCTORS;;
    )
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_float64 (bsqterm_float64_value (_ FloatingPoint 11 53)))
      (bsqterm_buffer (bsqterm_buffer_value bsq_buffer))
      (bsqterm_bufferof (bsqterm_bufferof_value bsq_bufferof))
      (bsqterm_bytebuffer (bsqterm_bytebuffer_value bsq_bytebuffer))
      (bsqterm_isotime (bsqterm_isotime_value bsq_isotime))
      (bsqterm_regex (bsqterm_regex_value bsq_regex))
      (bsqterm_tuple (bsqterm_tuple_value bsq_tuple))
      (bsqterm_record (bsqterm_record_value bsq_record))
      (bsqterm_object (bsqterm_object_type Int) (bsqterm_object_value bsq_object))
    )
))

;;
;; Type Decls
;;
(declare-datatypes (
      (bsq_nominal_type 0)
      (bsq_literal_type 0)
      (bsq_tuple_type 0)
      (bsq_record_type 0)
      (bsq_ephemeral_type 0)
    ) (
    ( (bsq_nominal_type@cons (bsq_nominal_type_id String) (bsq_nominal_type_iskey String) (bsq_nominal_type_isapi String) (bsq_nominal_type_ispod String) (bsq_nominal_type_subtypes (Array String bsq_nominal_type))) )
    ( (bsq_literal_type@cons (bsq_literal_type_id String)) )

    ( (bsq_tuple_type@cons (bsq_tuple_type_id String)) )
    ( (bsq_record_type@cons (bsq_record_type_id String)) )

    ( (bsq_ephemeral_type@cons (bsq_ephemeral_type_id String)) )

    (
      (bsqkey_none@cons) 
      (bsqkey_bool@cons (bsqkey_bool_value Bool))
      (bsqkey_int@cons (bsqkey_int_value Int))
      (bsqkey_nat@cons (bsqkey_nat_value Int))
      (bsqkey_bigint@cons (bsqkey_bigint_value Int))
      (bsqkey_bignat@cons (bsqkey_bignat_value Int))
      (bsqkey_string@cons (bsqkey_string_value String))
      ;;KEY_TYPE_CONSTRUCTORS;;
    )
))


;;NOMINAL_TYPE_KIND_DECLS;;

(declare-const MIRNominalTypeEnum_None Int)
(declare-const MIRNominalTypeEnum_Bool Int)
(declare-const MIRNominalTypeEnum_Int Int)
(declare-const MIRNominalTypeEnum_BigInt Int)
(declare-const MIRNominalTypeEnum_Float64 Int)
(declare-const MIRNominalTypeEnum_String Int)
(declare-const MIRNominalTypeEnum_UUID Int)
(declare-const MIRNominalTypeEnum_LogicalTime Int)
(declare-const MIRNominalTypeEnum_CryptoHash Int)
(declare-const MIRNominalTypeEnum_ByteBuffer Int)
(declare-const MIRNominalTypeEnum_ISOTime Int)
(declare-const MIRNominalTypeEnum_Tuple Int)
(declare-const MIRNominalTypeEnum_Record Int)
(declare-const MIRNominalTypeEnum_Regex Int)

;;SPECIAL_NAME_BLOCK_ASSERTS;;

(declare-fun nominalDataKinds (Int) StructuralSpecialTypeInfo)
;;NOMINAL_TYPE_TO_DATA_KIND_ASSERTS;;

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) Int
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
                        (ite (is-bsqkey_idkeysimple keyv) (bsq_idkeysimple_type (bsqkey_idkeysimple_value keyv))
                          (bsq_idkeycompound_type (bsqkey_idkeycompound_value keyv))
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

(define-fun bsqterm_get_nominal_type ((term BTerm)) Int
  (ite (is-bsqterm_float64 term) MIRNominalTypeEnum_Float64
    (ite (is-bsqterm_key term) (bsqkey_get_nominal_type (bsqterm_key_value term))
      (ite (is-bsqterm_buffer term) (bsq_buffer_type (bsqterm_buffer_value term))
        (ite (is-bsqterm_bufferof term) (bsq_bufferof_type (bsqterm_bufferof_value term))
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
)

(define-fun bsqkeyless_basetypes ((k1 BKeyValue) (k2 BKeyValue)) Bool
  (let ((k1t (bsqkey_get_nominal_type k1)) (k2t (bsqkey_get_nominal_type k2)))
    (ite (not (= k1t k2t))
      (< k1t k2t)
      (ite (and (= k1 bsqkey_none) (= k2 bsqkey_none)) false
        (ite (and (is-bsqkey_bool k1) (is-bsqkey_bool k2)) (and (not (bsqkey_bool_value k1)) (bsqkey_bool_value k2))
          (ite (and (is-bsqkey_int k1) (is-bsqkey_int k2)) (< (bsqkey_int_value k1) (bsqkey_int_value k2))
            (ite (and (is-bsqkey_bigint k1) (is-bsqkey_bigint k2)) (< (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
              (ite (and (is-bsqkey_string k1) (is-bsqkey_string k2)) (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
                (ite (and (is-bsqkey_safestring k1) (is-bsqkey_safestring k2)) (str.< (bsq_safestring_value (bsqkey_safestring_value k1)) (bsq_safestring_value (bsqkey_safestring_value k2)))
                  (ite (and (is-bsqkey_stringof k1) (is-bsqkey_stringof k2)) (str.< (bsq_stringof_value (bsqkey_stringof_value k1)) (bsq_stringof_value (bsqkey_stringof_value k2)))
                    (ite (and (is-bsqkey_uuid k1) (is-bsqkey_uuid k2)) (str.< (bsq_uuid_value (bsqkey_uuid_value k1)) (bsq_uuid_value (bsqkey_uuid_value k2)))
                      (ite (and (is-bsqkey_logicaltime k1) (is-bsqkey_logicaltime k2)) (< (bsq_logicaltime_value (bsqkey_logicaltime_value k1)) (bsq_logicaltime_value (bsqkey_logicaltime_value k2)))
                        (ite (and (is-bsqkey_cryptohash k1) (is-bsqkey_cryptohash k2)) (str.< (bsq_cryptohash_value (bsqkey_cryptohash_value k1)) (bsq_cryptohash_value (bsqkey_cryptohash_value k2)))
                          (< (bsq_enum_value (bsqkey_enum_value k1)) (bsq_enum_value (bsqkey_enum_value k2)))
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

(define-fun bsqkeyless_identitysimple ((idtype Int) (k1 bsq_idkeysimple) (k2 bsq_idkeysimple)) Bool
;;
;;TODO -- need to gas bound and generate this (and bsqkeyless programatically)
;;
false
)

(define-fun bsqkeyless_identitycompound ((idtype Int) (k1 bsq_idkeycompound) (k2 bsq_idkeycompound)) Bool
;;
;;TODO -- need to gas bound and generate this (and bsqkeyless programatically)
;;
false
)

(define-fun bsqkeyless ((k1 BKeyValue) (k2 BKeyValue)) Bool
  (let ((k1t (bsqkey_get_nominal_type k1)) (k2t (bsqkey_get_nominal_type k2)))
    (ite (not (= k1t k2t))
      (< k1t k2t)
      (ite (and (is-bsqkey_idkeycompound k1) (is-bsqkey_idkeycompound k2))
        (bsqkeyless_identitycompound k1t (bsqkey_idkeycompound_value k1) (bsqkey_idkeycompound_value k2))
        (ite (and (is-bsqkey_idkeysimple k1) (is-bsqkey_idkeysimple k2))
          (bsqkeyless_identitysimple k1t (bsqkey_idkeysimple_value k1) (bsqkey_idkeysimple_value k2))
          (bsqkeyless_basetypes k1 k2)
        )
      )
    )
  )
)

(declare-const StructuralSpecialTypeInfo@Clear StructuralSpecialTypeInfo)
(assert (= StructuralSpecialTypeInfo@Clear (StructuralSpecialTypeInfo@cons true true true)))

(define-fun getStructuralSpecialTypeInfoTerm ((term BTerm)) StructuralSpecialTypeInfo
  (ite (= term bsqterm@clear) StructuralSpecialTypeInfo@Clear
    (ite (is-bsqterm_tuple term) (bsq_tuple_concepts (bsqterm_tuple_value term))
      (ite (is-bsqterm_record term) (bsq_record_concepts (bsqterm_record_value term))
        (nominalDataKinds (bsqterm_get_nominal_type term))
      )
    )
  )
)

(define-fun mergeStructuralSpecialTypeInfo ((st1 StructuralSpecialTypeInfo) (st2 StructuralSpecialTypeInfo)) StructuralSpecialTypeInfo
  (StructuralSpecialTypeInfo@cons (and (StructuralSpecialTypeInfo$PODType st1) (StructuralSpecialTypeInfo$PODType st2)) (and (StructuralSpecialTypeInfo$APIType st1) (StructuralSpecialTypeInfo$APIType st2)) (and (StructuralSpecialTypeInfo$Parsable st1) (StructuralSpecialTypeInfo$Parsable st2)))
)

(define-fun @fj ((term BTerm) (sti StructuralSpecialTypeInfo)) StructuralSpecialTypeInfo
  (mergeStructuralSpecialTypeInfo (getStructuralSpecialTypeInfoTerm term) sti)
)

(declare-const @int_min Int)
(assert (= @int_min -9007199254740991))

(declare-const @int_max Int)
(assert (= @int_max 9007199254740991))

(define-fun @int_unsafe ((v Int)) Bool
  (or (< v @int_min) (> v @int_max))
)

;;EPHEMERAL_DECLS;;

(declare-const bsqterm_none BTerm)
(assert (= bsqterm_none (bsqterm_key bsqkey_none)))

(declare-const bsqidkey_array_empty (Array Int BKeyValue))
(assert (= bsqidkey_array_empty ((as const (Array Int BKeyValue)) bsqkey_none)))

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

(declare-const mirconceptsubtypearray_empty (Array Int Bool))
(assert (= mirconceptsubtypearray_empty ((as const (Array Int Bool)) false)))

;;REGEX_DECLS;;

;;CONCEPT_SUBTYPE_RELATION_DECLARE;;

;;SUBTYPE_DECLS;;

;;VFIELD_ACCESS;;

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
