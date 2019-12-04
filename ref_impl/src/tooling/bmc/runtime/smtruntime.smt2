;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( 
      (BTerm 0)
      (bsqstring 0)
      (bsqtuple_entry 0)
      (bsqtuple_0 0)
    ;;FIXED_TUPLE_DECLS_FWD;;
      (bsqrecord_entry 0)
      (bsqrecord_empty 0)
    ;;FIXED_RECORD_DECLS_FWD;;
    ;;NOMINAL_DECLS_FWD;;
      (bsqcollection_data 0)
      (bsqlist 0)
      (bsqset 0)
      (bsqmap 0)
    ) (
    (
      (bsqterm_none) 
      (bsqterm_bool (bsqterm_bool_value Bool))
      (bsqterm_int (bsqterm_int_value Int))
      (bsqterm_string (bsqterm_string_value bsqstring))
      (bsqterm_typedstring (bsqterm_typedstring_type String) (bsqterm_typedstring_value bsqstring))
      (bsqterm_podbuffer (bsqterm_podbuffer_type String) (bsqterm_podbuffer_value (Array Int Int)))
      (bsqterm_guid (bsqterm_guid_value String))
      (bsqterm_enum (bsqterm_enum_type String) (bsqterm_enum_value Int))
      (bsqterm_idkey (bsqterm_idkey_type String) (bsqterm_idkey_value BTerm))
      (bsqterm_regex (bsqterm_regex_value String))
      (bsqterm_tuple (bsqterm_tuple_max_length Int) (bsqterm_tuple_entries (Array Int bsqtuple_entry)))
      (bsqterm_record (bsqterm_record_max_properties Int) (bsqterm_record_properties (Array Int String)) (bsqterm_record_entries (Array String bsqrecord_entry)))
      (bsqterm_array (bsqterm_array_length Int) (bsqterm_array_entries (Array Int BTerm)))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_entries (Array String BTerm)) (bsqterm_object_collection (Array Int bsqcollection_data)))
    )
    ( (bsqstring@cons (bsqstring@length Int) (bsqstring@contents (Array Int Int))) )
    ( (bsqtuple_entry@clear) (bsqtuple_entry@value (bsqtuple_entry@term BTerm)) )
    ( (bsqtuple_0@cons) )
  ;;FIXED_TUPLE_DECLS;;
    ( (bsqrecord_entry@clear) (bsqrecord_entry@value (bsqrecord_entry@term BTerm)) )
    ( (bsqrecord_empty@cons) )
  ;;FIXED_RECORD_DECLS;;
  ;;NOMINAL_DECLS;;
    ( (bsqcollection_data@single (bsqcollection_data@elem BTerm)) (bsqcollection_data@tuple (bsqcollection_data@key BTerm) (bsqcollection_data@value BTerm)) )
    ( (cons@bsqlist$none) (cons@bsqlist (bsqlist@size Int) (bsqlist@entries (Array Int bsqcollection_data)) )
    ( (cons@bsqset$none) (cons@bsqset (bsqset@size Int) (bsqset@entries (Array Int bsqcollection_data)) )
    ( (cons@bsqset$none) (cons@bsqmap (bsqmap@size Int) (bsqmap@entries (Array Int bsqcollection_data)) )
))

(declare-const bsqterm_none_const BTerm) (assert (= bsqterm_none_const bsqterm_none))
(declare-const bsqterm_true_const BTerm) (assert (= bsqterm_true_const (bsqterm_bool true)))
(declare-const bsqterm_false_const BTerm) (assert (= bsqterm_false_const (bsqterm_bool false)))

(declare-const bsqstring_array_empty (Array Int Int))
(assert (= bsqstring_array_empty ((as const (Array Int Int)) 0)))

(declare-const bsqtuple_array_empty (Array Int bsqtuple_entry))
(assert (= bsqtuple_array_empty ((as const (Array Int bsqtuple_entry)) bsqtuple_entry@clear)))

(declare-const bsqrecord_array_empty (Array String bsqrecord_entry))
(assert (= bsqrecord_array_empty ((as const (Array String bsqrecord_entry)) bsqrecord_entry@clear)))

(declare-const bsqrecord_prop_array_empty (Array Int String))
(assert (= bsqrecord_prop_array_empty ((as const (Array Int String)) "")))

(declare-const bsqentity_array_empty (Array String BTerm))
(assert (= bsqentity_array_empty ((as const (Array String BTerm)) bsqterm_none_const)))

(declare-const bsqcollection_data_array_single_empty (Array Int bsqcollection_data))
(assert (= bsqcollection_data_array_single_empty ((as const (Array Int bsqcollection_data)) (bsqcollection_data@single bsqterm_none_const))))

(declare-const bsqcollection_data_array_tuple_empty (Array Int bsqcollection_data))
(assert (= bsqcollection_data_array_tuple_empty ((as const (Array Int bsqcollection_data)) (bsqcollection_data@tuple bsqterm_none_const bsqterm_none_const))))

(declare-const mirconceptsubtypearray_empty (Array String Bool))
(assert (= mirconceptsubtypearray_empty ((as const (Array String Bool)) false)))

;;CONCEPT_SUBTYPE_RELATION_DECLARE;;

;;RECORD_PROPERTY_LIST_DECLS;;

(declare-datatypes ( (ErrorCode 0) ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id Int)) )
))

(declare-datatypes ( 
      ;;FIXED_TUPLE_RESULT_FWD;;
      ;;FIXED_RECORD_RESULT_FWD;;
      ;;NOMINAL_RESULT_FWD;;
    ) (
    ;;FIXED_TUPLE_RESULT;;
    ;;FIXED_RECORD_RESULT;;
    ;;NOMINAL_RESULT;;
))

;;current implementation is simple uninterpreted function -- want to implement these in core runtime with bounded checkable impl
(declare-fun stroi (String) Int)

;;current implementation is simple uninterpreted function -- maybe want to make these return a non-decidable error (or have bounded checkable impl)
(declare-fun mult_op (Int Int) Int) 
(declare-fun div_op (Int Int) Int)
(declare-fun mod_op (Int Int) Int)

;;STRING_DECLS;;

;;SUBTYPE_DECLS;;

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
