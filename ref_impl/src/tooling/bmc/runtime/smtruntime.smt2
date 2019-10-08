;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( (BTerm 0) ) (
    (
      (bsq_term_none) 
      (bsq_term_bool (bsq_term_bool_value Bool))
      (bsq_term_int (bsq_term_int_value Int))
      (bsq_term_string (bsq_term_string_value String))
      (bsq_term_tuple (bsq_term_tuple_size Int) (bsq_term_tuple_entries (Array Int BTerm)))
      (bsq_term_record (bsq_term_record_size Int) (bsq_term_record_entries (Array Int BTerm)))
      ;;TYPE_DECLS;;
    )
))

(declare-datatypes ( (ErrorCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( (ResultNone 0) (ResultBool 0) (ResultInt 0) (Result 0)) (
    ( (result_success_None) (result_error_None ErrorCode) )
    ( (result_success_Bool Bool) (result_error_Bool ErrorCode) )
    ( (result_success_Int Bool) (result_error_Int ErrorCode) )
    ( (result_success BTerm) (result_error ErrorCode) )
))
