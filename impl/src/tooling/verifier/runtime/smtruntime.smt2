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
    TypeTag_Rational
    TypeTag_String
    TypeTag_Regex
    ;;TYPE_TAG_DECLS;;
  )
))

(declare-datatypes () (
  (AbstractTypeTag
    ;;ABSTRACT_TYPE_TAG_DECLS;;
  )
))

(declare-datatypes () (
  (TupleIndexTag
    ;;INDEX_TAG_DECLS;;
  )
))

(declare-datatypes () (
  (RecordPropertyTag
    ;;PROPERTY_TAG_DECLS;;
  )
))

;;
;;TODO: There may be a large number of trivially "false" entries in this relation. 
;;      We can do better by splitting it into some type aware sub-relations (e.g. a tuple is never a subtype of Object etc.).
;;
(declare-fun SubtypeOf@ (TypeTag, AbstractTypeTag) Bool)
;;SUBTYPE_DECLS;;

(declare-fun HasIndex@ (TypeTag, TupleIndexTag) Bool)
;;TUPLE_HAS_INDEX_DECLS;;

(declare-fun HasProperty@ (TypeTag, RecordPropertyTag) Bool)
;;RECORD_HAS_PROPERTY_DECLS;;

(declare-fun TypeTagLess@ (TypeTag, TypeTag) Bool)
;;KEY_TYPE_TAG_LESS;;

;;
;;UFloat kind + UF ops for strong refutation checks
;;
(declare-sort UFloat)

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
      ; Float ->   Float | UFloat as BFloat
      ; Decimal -> Float | UFloat as BDecimal
      ; Rational -> Float | UFloat as BRational
      ; String -> String | (Seq (_ BitVec 64)) as BString
    ) (
    ( (bsq_none@literal) )
))

;;
;; Define sort aliases for Float/String representation options
;;
;;FP_TYPE_ALIAS;;
;;STRING_TYPE_ALIAS;;

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
      (bsqkey_string@cons (bsqkey_string_value BString))
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
      (bsqobject_float@cons (bsqobject_float_value BFloat))
      (bsqobject_decimal@cons (bsqobject_decimal_value BDecimal))
      (bsqobject_rational@cons (bsqobject_rational_value BRational))
      (bsqobject_regex@cons (bsqobject_regex_value bsq_regex))
      ;;TUPLE_TYPE_BOXING;;
      ;;RECORD_TYPE_BOXING;;
      ;;TYPE_BOXING;;
    )
    ( 
      (BTerm@termcons (BTerm_termtype TypeTag) (BTerm_termvalue bsq_object))
      (BTerm@keycons (BTerm_keyvalue BKey)) 
    )
))

(declare-const BTerm@none BTerm)
(assert (= BTerm@none (BTerm@keycons BKey@none)))

;;
;;Define utility functions
;;
(define-fun GetTypeTag@BKey ((t BKey)) TypeTag
  (BKey_type t)
)

(define-fun GetTypeTag@BTerm ((t BKey)) TypeTag
  (ite (is-BTerm@termcons t) (BTerm_termtype t) (BKey_type (BTerm_keyvalue t)))
)

;;
;; Define uninterpreted functions for various kinds
;;
(declare-fun BFloatUnary_UF (String BFloat) BFloat)
(declare-fun BFloatBinary_UF (String BFloat BFloat) BFloat)

(declare-fun BDecimalUnary_UF (String BDecimal) BDecimal)
(declare-fun BDecimalBinary_UF (String BDecimal BDecimal) BDecimal)

(declare-fun BRationalUnary_UF (String BRational) BRational)
(declare-fun BRationalBinary_UF (String BRational BRational) BRational)

(declare-fun BIntNonLinear_UF (String Int Int) Int)
(declare-fun BBigIntNonLinear_UF (String Int Int) Int)

(declare-fun BNatNonLinear_X_UF (String Int Int) Int)
(declare-fun BBigNatNonLinear_X_UF (String Int Int) Int)

(define-fun BNatNonLinear_UF ((op String) (a Int) (b Int)) Int 
  (let ((r (BNatNonLinear_X_UF op a b))) (ite (<= 0 r) r (- r)))
)

(define-fun BBigNatNonLinear_UF ((op String) (a Int) (b Int)) Int 
  (let ((r (BNatNonLinear_X_UF op a b))) (ite (<= 0 r) r (- r)))
)

;;EPHEMERAL_DECLS;;

(declare-datatypes () (
  (ErrorID
    ErrorID_AssumeCheck
    ErrorID_CheckTarget
  )
))

(declare-datatypes (
      ;;RESULT_DECLS;;
      ;;FLAG_RESULT_DECLS;;
    ) (
    ;;RESULTS;;
    ;;FLAG_RESULTS;;
))

;;SUBTYPE_DECLS;;

;;V_ACCESS;;

;;FUNCTION_DECLS;;
