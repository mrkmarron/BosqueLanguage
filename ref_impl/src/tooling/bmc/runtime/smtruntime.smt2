;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( (BTerm 0) (BTermList 0) (BTermNamedList 0) (BTermSetList 0) (BTermMapList 0)) (
    (
      (bsq_term_none) 
      (bsq_term_bool (bsq_term_bool_value Bool))
      (bsq_term_int (bsq_term_int_value Int))
      (bsq_term_string (bsq_term_string_value String))
      (bsq_term_stringof (bsq_term_stringof_value String))
      (bsq_term_tuple (bsq_term_tuple_entries BTermList))
      (bsq_term_record (bsq_term_record_entries BTermNamedList))
      ;;TYPE_DECLS;;
    )
    (
      (bsq_term_list_nil) 
      (bsq_term_list_cons (bsq_term_list_head BTerm) (bsq_term_list_tail BTermList))
    )
    (
      (bsq_term_named_list_nil)
      (bsq_term_named_list_cons (bsq_term_named_list_name Int) (bsq_term_named_list_head BTerm) (bsq_term_named_list_tail BTermNamedList))
    )
    (
      (bsq_term_set_list_nil)
      (bsq_term_set_list_cons (bsq_term_set_list_rk BTerm) (bsq_term_set_list_head BTerm) (bsq_term_set_list_tail BTermSetList))
    )
    (
      (bsq_term_map_list_nil)
      (bsq_term_map_list_cons (bsq_term_map_list_rk BTerm) (bsq_term_map_list_head_key BTerm) (bsq_term_map_list_head_val BTerm) (bsq_term_map_list_tail BTermMapList))
    )
))

(declare-datatypes ( (ErrorCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( (ResultNone 0) (ResultBool 0) (ResultInt 0) (Result 0)) (
    ( (result_success_None) (result_error_None (result_error_code_None ErrorCode)) )
    ( (result_success_Bool (result_success_value_Bool Bool)) (result_error_Bool (result_error_code_Bool ErrorCode)) )
    ( (result_success_Int (result_success_value_Int Bool)) (result_error_Int (result_error_code_Int ErrorCode)) )
    ( (result_success (result_success_value BTerm)) (result_error (result_error_code ErrorCode)) )
))

(declare-const bsq_term_true_const BTerm)
(assert (= bsq_term_true_const (bsq_term_bool true)))

(declare-const bsq_term_false_const BTerm)
(assert (= bsq_term_false_const (bsq_term_bool false)))
