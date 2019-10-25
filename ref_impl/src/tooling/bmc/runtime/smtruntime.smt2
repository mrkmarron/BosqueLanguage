;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

;;NOMINAL_ID_ENUM;;

(declare-const repr_none Int) (assert (= repr_none 1))
(declare-const repr_bool Int) (assert (= repr_bool 2))
(declare-const repr_int Int) (assert (= repr_int 3))
(declare-const repr_string Int) (assert (= repr_string 4))
(declare-const repr_stringof Int) (assert (= repr_stringof 5))
(declare-const repr_tuple Int) (assert (= repr_tuple 6))
(declare-const repr_record Int) (assert (= repr_record 7))
(declare-const repr_enum Int) (assert (= repr_enum 8))
(declare-const repr_idkey Int) (assert (= repr_idkey 9))
(declare-const repr_keyed Int) (assert (= repr_keyed 10))
(declare-const repr_tagged Int) (assert (= repr_tagged 11))
(declare-const repr_object Int) (assert (= repr_object 12))

(declare-datatypes ( 
      (BTerm 0) (BValue) (BTupleEntry 0) (BRecordEntry 0)
      ;;NOMINAL_DECLS_FWD;;
    ) (
    (
      (bsqterm (bsqterm_repr Int) (bsqterm_value BValue))
    )
    (
      (bsqvalue_none) 
      (bsqvalue_bool (bsqvalue_bool_value Bool))
      (bsqvalue_int (bsqvalue_int_value Int))
      (bsqvalue_string (bsqvalue_string_value String))
      (bsqvalue_stringof (bsqvalue_stringof_type String) (bsqvalue_stringof_value String))
      (bsqvalue_tuple (bsqvalue_tuple_entries (Array Int BTupleEntry)))
      (bsqvalue_record (bsqvalue_record_entries (Array String BRecordEntry)))
      (bsqvalue_enum (bsqvalue_enum_type String) (bsqvalue_enum_value String))
      (bsqvalue_idkey (bsqvalue_idkey_type String) (bsqvalue_idkey_value BValue))
      (bsqvalue_keyed_or_tagged (bsqvalue_keyed_or_tagged_type String) (bsqvalue_keyed_or_tagged_key BValue) (bsqvalue_keyed_or_tagged_value BTerm))
      ;;BOXED_NOMINAL_DECLS;;
    )
    (
      (bsqtuple_entry (bsqtuple_entry_valid Bool) (bsqtuple_entry_value BTerm)) 
    )
    ( 
      (bsqrecord_entry (bsqrecord_entry_valid Bool) (bsqrecord_entry_value BTerm)) 
    )
    ;;NOMINAL_DECLS;;
))

(declare-const bsqterm_none_const BTerm) (assert (= bsqterm_none_const (bsqterm bsqvalue_none)))
(declare-const bsqterm_true_const BTerm) (assert (= bsqterm_true_const (bsqterm (bsqterm_bool true))))
(declare-const bsqterm_false_const BTerm) (assert (= bsqterm_false_const (bsqterm (bsqterm_bool false))))

(declare-const bsqtuple_array_empty (Array Int BTupleEntry))
(assert (= bsqtuple_array_empty ((as const (Array Int BTupleEntry)) (bsqtuple_entry false (bsqterm_none_const))))

(declare-const bsqrecord_array_empty (Array String BRecordEntry))
(assert (= bsqrecord_array_empty ((as const (Array String BRecordEntry)) (bsqrecord_entry false bsqterm_none_const))))

(declare-datatypes ( (ErrorCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( 
      (Result$Bool 0) (Result$Int 0) (Result$BTerm 0)
      ;;NOMINAL_RESULT_FWD;;
    ) (
    ( (result_success$Bool (result_success_value$Bool Bool)) (result_error$Bool (result_error_code$Bool ErrorCode)) )
    ( (result_success$Int (result_success_value$Int Int)) (result_error$Int (result_error_code$Int ErrorCode)) )
    ( (result_success$BTerm (result_success_value$BTerm BTerm)) (result_error$BTerm (result_error_code$BTerm ErrorCode)) )
    ;;NOMINAL_RESULT;;
))

(declare-const BINT_MAX Int)
(assert (= BINT_MAX 4503599627370495))

(declare-const BINT_MIN Int)
(assert (= BINT_MIN -4503599627370496))

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
