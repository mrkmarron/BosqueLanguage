;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( 
      (BTerm 0) (BTermList 0) (BTupleEntry 0) (BRecordEntry 0)
      ;;NOMINAL_DECLS_FWD;;
    ) (
    (
      (bsq_term_none) 
      (bsq_term_NSCore$cc$Bool (bsq_term_value_NSCore$cc$Bool Bool))
      (bsq_term_NSCore$cc$Int (bsq_term_value_NSCore$cc$Int Int))
      (bsq_term_NSCore$cc$String (bsq_term_value_NSCore$cc$String String))
      (bsq_term_tuple (bsq_term_tuple_entries BTermList))
      (bsq_term_record (bsq_term_record_entries (Array String BRecordEntry)))
      ;;BOXED_NOMINAL_DECLS;;
    )
    (
      (bsq_tuple_entry (bsq_tuple_entry_valid Bool) (bsq_tuple_entry_value BTerm)) 
    )
    ( 
      (bsq_record_entry (bsq_record_entry_valid Bool) (bsq_record_entry_value BTerm)) 
    )
    ;;NOMINAL_DECLS;;
))

(declare-const bsq_tuple_entry_array_empty (Array String BTupleEntry))
(assert (= bsq_tuple_entry_array_empty ((as const (Array String BTupleEntry)) (bsq_tuple_entry false bsq_term_none))))

(declare-const bsq_record_entry_array_empty (Array String BRecordEntry))
(assert (= bsq_record_entry_array_empty ((as const (Array String BRecordEntry)) (bsq_record_entry false bsq_term_none))))

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
