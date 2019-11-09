;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( (RecordPropertyList 0) ) (
    ( 
      (property_list_nil)
      (property_list_cons (property_list_head String) (property_list_tail RecordPropertyList)) 
    )
))

(declare-datatypes ( 
      (BTerm 0)
      (bsqtuple_0 0)
    ;;FIXED_TUPLE_DECLS_FWD;;
      (bsqrecord_empty 0)
    ;;FIXED_RECORD_DECLS_FWD;;
    ;;NOMINAL_DECLS_FWD;;
    ) (
    (
      (bsqterm_none) 
      (bsqterm_bool (bsqterm_bool_value Bool))
      (bsqterm_int (bsqterm_int_value Int))
      (bsqterm_string (bsqterm_string_value String))
      (bsqterm_typedstring (bsqterm_typedstring_type String) (bsqterm_typedstring_value String))
      (bsqterm_validatedstring (bsqterm_validatedstring_type String) (bsqterm_validatedstring_value String))
      (bsqterm_podbuffer (bsqterm_podbuffer_value (Array Int Int)))
      (bsqterm_guid (bsqterm_guid_value String))
      (bsqterm_enum (bsqterm_enum_name String) (bsqterm_enum_value Int))
      (bsqterm_idkey (bsqterm_idkey_value BTerm))
      (bsqterm_regex (bsqterm_regex_value String))
      (bsqterm_tuple (bsqterm_tuple_length Int) (bsqterm_tuple_entries (Array Int BTerm)))
      (bsqterm_record (bsqterm_record_property_ub RecordPropertyList) (bsqterm_record_properties (Array String Bool)) (bsqterm_record_entries (Array String BTerm)))
      (bsqterm_array (bsqterm_array_length Int) (bsqterm_array_entries (Array Int BTerm)))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_entries (Array String BTerm)))
    )
    ( (bsqtuple_0@cons) )
  ;;FIXED_TUPLE_DECLS;;
    ( (bsqrecord_empty@cons) )
  ;;FIXED_RECORD_DECLS;;
  ;;NOMINAL_DECLS;;
))

;;KNOWN_RECORD_PROPERTY_TYPE_LISTS;;

(declare-const bsqterm_none_const BTerm) (assert (= bsqterm_none_const bsqterm_none))
(declare-const bsqterm_true_const BTerm) (assert (= bsqterm_true_const (bsqterm_bool true)))
(declare-const bsqterm_false_const BTerm) (assert (= bsqterm_false_const (bsqterm_bool false)))

(declare-const bsqtuple_empty_const bsqtuple_0) (assert (= bsqtuple_empty_const bsqtuple_0@cons))
(declare-const bsqrecord_empty_const bsqrecord_$lp$$rp$) (assert (= bsqrecord_empty_const bsqrecord_$lp$$rp$@cons))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm_none_const)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm_none_const)))

(declare-const bsqrecord_property_array_empty (Array String Bool))
(assert (= bsqrecord_property_array_empty ((as const (Array String Bool)) false)))

(declare-const bsqarray_array_empty (Array Int BTerm))
(assert (= bsqarray_array_empty ((as const (Array Int BTerm)) bsqterm_none_const)))

;;RECORD_PROPERTY_LIST_DECLS;;

(declare-datatypes ( (ErrorCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( 
      (Result@Bool 0) (Result@Int 0) (Result@String 0) (Result@BTerm 0)
      ;;FIXED_TUPLE_RESULT_FWD;;
      ;;FIXED_RECORD_RESULT_FWD;;
      ;;NOMINAL_RESULT_FWD;;
    ) (
    ( (result_success@Bool (result_success_value@Bool Bool)) (result_error@Bool (result_error_code@Bool ErrorCode)) )
    ( (result_success@Int (result_success_value@Int Int)) (result_error@Int (result_error_code@Int ErrorCode)) )
    ( (result_success@String (result_success_value@String String)) (result_error@String (result_error_code@String ErrorCode)) )
    ( (result_success@BTerm (result_success_value@BTerm BTerm)) (result_error@BTerm (result_error_code@BTerm ErrorCode)) )
    ;;FIXED_TUPLE_RESULT;;
    ;;FIXED_RECORD_RESULT;;
    ;;NOMINAL_RESULT;;
))

(declare-const BINT_MAX Int)
(assert (= BINT_MAX 4503599627370495))

(declare-const BINT_MIN Int)
(assert (= BINT_MIN -4503599627370496))

(declare-fun stroi (String) Int) ;;current implementation is simple uninterpreted function

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
