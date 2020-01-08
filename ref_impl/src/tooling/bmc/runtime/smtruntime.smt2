;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 30000)

(declare-datatypes ( 
      (BKeyValue 0)
    ) (
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_stringof (bsqkey_stringof_type String) (bsqkey_stringof_value String))
      (bsqkey_validatedstring (bsqkey_validatedstring_regex String) (bsqkey_validatedstring_value String))
      (bsqkey_guid (bsqkey_guid_value String))
      (bsqkey_enum (bsqkey_enum_type String) (bsqkey_enum_value Int))
      (bsqkey_idkey (bsqkey_idkey_type String) (bsqkey_idkey_value BKeyValue))
      (bsqkey_tuple (bsqkey_tuple_entries (Array Int BKeyValue)))
      (bsqkey_record (bsqkey_record_entries (Array String BKeyValue)))
    )
))

(declare-datatypes ( 
      (BTerm 0)
    ;;NOMINAL_DECLS_FWD;;
      (bsqobject 0)
      (bsqlist 0)
      (bsqkeylist 0)
      (bsqkvcontainer 0)
    ) (
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_regex (bsqterm_regex_value String))
      (bsqterm_tuple (bsqterm_tuple_entries (Array Int BTerm))) 
      (bsqterm_tuple_key (bsqterm_tuple_key_entries (Array Int BKeyValue)))
      (bsqterm_record (bsqterm_record_entries (Array String BTerm)))
      (bsqterm_record_key (bsqterm_record_key_entries (Array String BKeyValue)))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_obj bsqobject))
      (bsqterm_list (bsqterm_list_type String) (bsqterm_list_entry bsqlist))
      (bsqterm_kvcontainer (bsqterm_bsqkvcontainer_type String) (bsqterm_bsqkvcontainer_entry bsqkvcontainer))
    )
  ;;NOMINAL_DECLS;;
    (
  ;;OBJECT_CONSTRUCTORS;; like (cons@name1 (name1_value nominal_decl1)) (cons@name2 (name2_value nominal_decl2))
    )
    ( (cons@bsqlist$none) (cons@bsqlist (bsqlist@size Int) (bsqlist@entries (Array Int BTerm))) )
    ( (cons@bsqkeylist$none) (cons@bsqkeylist (bsqkeylist@key BKeyValue) (bsqkeylist@tail bsqkeylist)) )
    ( (cons@bsqkvcontainer$none) (cons@bsqkvcontainer (bsqkvcontainer@size Int) (bsqkvcontainer@keylist bsqkeylist) (bsqkvcontainer@entries (Array BKeyValue BTerm))) )
))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm@clear)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm@clear)))

(declare-const bsqentity_array_empty (Array String BTerm))
(assert (= bsqentity_array_empty ((as const (Array String BTerm)) (bsqterm_key bsqkey_none))))

(declare-const bsqlist_data_array_empty (Array Int BTerm))
(assert (= bsqlist_data_array_empty ((as const (Array Int BTerm)) (bsqterm_key bsqkey_none))))

(declare-const bsqkvp_array_empty (Array BKeyValue BTerm))
(assert (= bsqkvp_array_empty ((as const (Array BKeyValue BTerm)) bsqterm@clear)))

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

;;CONCEPT_SUBTYPE_RELATION_DECLARE;;

;;SUBTYPE_DECLS;;

;;FUNCTION_DECLS;;

;;ARG_VALUES;;

;;INVOKE_ACTION;;

(check-sat)
;;GET_MODEL;;
