;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( 
      (BTerm 0) (BTermList 0) (BTermNamedList 0)
      ;;NOMINAL_DECLS_FWD;;
    ) (
    (
      (bsq_term_none) 
      (bsq_term_bool (bsq_term_bool_value Bool))
      (bsq_term_int (bsq_term_int_value Int))
      (bsq_term_string (bsq_term_string_value String))
      (bsq_term_tuple (bsq_term_tuple_entries BTermList))
      (bsq_term_record (bsq_term_record_entries BTermNamedList))
      ;;BOXED_NOMINAL_DECLS;;
    )
    (
      (bsq_term_list_nil) 
      (bsq_term_list_cons (bsq_term_list_head BTerm) (bsq_term_list_tail BTermList))
    )
    (
      (bsq_term_named_list_nil)
      (bsq_term_named_list_cons (bsq_term_named_list_name String) (bsq_term_named_list_head BTerm) (bsq_term_named_list_tail BTermNamedList))
    )
    ;;NOMINAL_DECLS;;
))

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

(declare-const bsq_term_true_const BTerm)
(assert (= bsq_term_true_const (bsq_term_bool true)))

(declare-const bsq_term_false_const BTerm)
(assert (= bsq_term_false_const (bsq_term_bool false)))

(declare-const BINT_MAX Int)
(assert (= BINT_MAX 4503599627370495))

(declare-const BINT_MIN Int)
(assert (= BINT_MIN -4503599627370496))

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
