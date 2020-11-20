;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.mbqi true)

(set-option :timeout 10000)

;;
;; Type Tags
;;

(declare-datatypes () (
  (TypeTag
  TypeTag_None
  TypeTag_Bool
  TypeTag_Int
  TypeTag_Nat
  TypeTag_BigInt
  TypeTag_BigNat
  TypeTag_Float
  TypeTag_Decimal
  TypeTag_String
  TypeTag_Regex
  TypeTag_GeneralTuple
  TypeTag_GeneralRecord
  ;;TYPE_TAG_DECLS;;
  )
))

(declare-fun nominal_subtype (TypeTag, TypeTag) Bool)
;;NOMINAL_SUBTYPE_DECLS;;

(declare-fun keytype_tag_less (TypeTag, TypeTag) Bool)
;;KEY_TYPE_TAG_LESS;;

;;
;;UFloat kind and other UF ops for strong refutation checks
;;
(declare-sort UFloat)

(declare-fun UFloatUnary (String, UFloat) UFloat)
(declare-fun UFloatBinary (String, UFloat, UFloat) UFloat)

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
      ; Float ->   Float | UFloat
      ; Decimal -> Float | UFloat
      ; String -> String | (Seq (_ BitVec 64))
    ) (
    ( (bsq_none@literal) )
))

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      (bsq_keytuple_entry 0)
      (bsq_keyrecord_entry 0)
      ;;KEY_TUPLE_DECLS;;
      ;;KEY_RECORD_DECLS;;
      ;;KEY_TYPE_DECLS;;
      (bsq_keyobject 0)
      (BKey 0)
    ) (
    ( (bsq_keytuple_entry@empty) (bsq_keytuple_entry@cons (bsq_keytuple_entry_value bsq_keyobject)) )
    ( (bsq_keyrecord_entry@empty) (bsq_keyrecord_entry@cons (bsq_keyrecord_entry_value bsq_keyobject)) )
    ;;KEY_TUPLE_TYPE_CONSTRUCTORS;;
    ;;KEY_RECORD_TYPE_CONSTRUCTORS;;
    ;;KEY_TYPE_CONSTRUCTORS;;
    (
      (bsqkey_none@literal) 
      (bsqkey_bool@cons (bsqkey_bool_value Bool))
      (bsqkey_int@cons (bsqkey_int_value Int))
      (bsqkey_nat@cons (bsqkey_nat_value Int))
      (bsqkey_bigint@cons (bsqkey_bigint_value Int))
      (bsqkey_bignat@cons (bsqkey_bignat_value Int))
      (bsqkey_string@cons (bsqkey_string_value String))
      ;;KEY_TUPLE_TYPE_BOXING;;
      ;;KEY_RECORD_TYPE_BOXING;;
      ;;KEY_TYPE_BOXING;;
    )
    ( (BKey@cons (BKey_type TypeTag) (BKey_value bsq_keyobject)) )
))

(declare-const BKey@none BKey)
(assert (= BKey@none (BKey@cons TypeTag_None bsqkey_none@literal)))

(define-fun bsqkey_none@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  false
)

(define-fun bsqkey_bool@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (and (not (bsqkey_bool_value k1)) (bsqkey_bool_value k2))
)

(define-fun bsqkey_int@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_int_value k1) (bsqkey_int_value k2))
)

(define-fun bsqkey_nat@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_nat_value k1) (bsqkey_nat_value k2))
)

(define-fun bsqkey_bigint@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_bigint_value k1) (bsqkey_bigint_value k2))
)

(define-fun bsqkey_bignat@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (< (bsqkey_bignat_value k1) (bsqkey_bignat_value k2))
)

(define-fun bsqkey_string@less ((k1 bsq_keyobject) (k2 bsq_keyobject)) Bool
  (str.< (bsqkey_string_value k1) (bsqkey_string_value k2))
)

;;BKEY_LESS_DECLS;;

;;
;; Any Concept datatypes
;;
(declare-datatypes (
    (bsq_regex 0)
    (bsq_tuple_entry 0)
    (bsq_record_entry 0)
    ;;TUPLE_DECLS;;
    ;;RECORD_DECLS;;
    ;;TYPE_DECLS;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ;;TUPLE_TYPE_CONSTRUCTORS;;
    ;;RECORD_TYPE_CONSTRUCTORS;;
    ;;TYPE_CONSTRUCTORS;;
    (
      (bsqobject_key@cons (bsqobject_key_value BKey))
      (bsqobject_regex@cons (bsqobject_regex_value bsq_regex))
      ;;TUPLE_TYPE_BOXING;;
      ;;RECORD_TYPE_BOXING;;
      ;;TYPE_BOXING;;
    )
    ( (BTerm@cons (BTerm_type TypeTag) (BTerm_value bsq_object)) )
))

(declare-const BTerm@none BTerm)
(assert (= BTerm@none (BTerm@cons TypeTag_None (bsqobject_key@cons BKey@none))))

;;EPHEMERAL_DECLS;;

(declare-datatypes () (
  (ErrorID
  ;;ERROR_ID_DECLS;;
  )
))

(declare-datatypes (
      ;;RESULT_DECLS;;
    ) (
    ;;RESULTS;;
))

;;SUBTYPE_DECLS;;

;;V_ACCESS;;

;;FUNCTION_DECLS;;
