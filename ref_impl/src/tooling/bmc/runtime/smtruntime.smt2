;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 10000)

(declare-datatypes ( 
      (BKeyValue 0)
    ) (
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_stringof (bsqkey_stringof_type String) (bsqkey_stringof_value String))
      (bsqkey_guid (bsqkey_guid_value String))
      (bsqkey_datahash (bsqkey_datahash Int))
      (bsqkey_cryptohash (bsqkey_cryptohash String))
      (bsqkey_eventtime (bsqkey_eventtime_value Int))
      (bsqkey_enum (bsqkey_enum_type String) (bsqkey_enum_value Int))
      (bsqkey_idkey (bsqkey_idkey_type String) (bsqkey_idkey_value (Array String BKeyValue)))
      (bsqkey_idkey_eventtime (bsqkey_idkey_eventtime_type String) (bsqkey_idkey_eventtime_value Int))
      (bsqkey_idkey_guid (bsqkey_idkey_guid_type String) (bsqkey_idkey_guid_value String))
      (bsqkey_idkey_datahash (bsqkey_idkey_datahash_type String) (bsqkey_idkey_datahash_value Int))
      (bsqkey_idkey_cryptohash (bsqkey_idkey_cryptohash_type String) (bsqkey_idkey_cryptohash_value String))
    )
))

(declare-datatypes ( 
      (BTerm 0)
    ;;NOMINAL_DECLS_FWD;;
      (bsqobject 0)
    ) (
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_isotime (bsqterm_isotime_value Int))
      (bsqterm_regex (bsqterm_regex_value String))
      (bsqterm_tuple (bsqterm_tuple_ispod Bool) (bsqterm_tuple_isapi Bool) (bsqterm_tuple_entries (Array Int BTerm))) 
      (bsqterm_record (bsqterm_tuple_ispod Bool) (bsqterm_tuple_isapi Bool) (bsqterm_record_entries (Array String BTerm)))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_obj bsqobject))
    )
  ;;NOMINAL_DECLS;;
    (
  ;;NOMINAL_CONSTRUCTORS;; like (cons@name1 (name1_value nominal_decl1)) (cons@name2 (name2_value nominal_decl2))
    )
))

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) String
xxxx
)

(define-fun bsqterm_get_nominal_type ((term BTerm)) String
xxxx
)

;;EPHEMERAL_DECLS;;

(declare-const bterm_none BTerm)
(assert (= bterm_none (bsqterm_key bsqkey_none)))

(declare-const bsqtuple_array_empty (Array Int BTerm))
(assert (= bsqtuple_array_empty ((as const (Array Int BTerm)) bsqterm@clear)))

(declare-const bsqrecord_array_empty (Array String BTerm))
(assert (= bsqrecord_array_empty ((as const (Array String BTerm)) bsqterm@clear)))

;;EMPTY_LIST_CONTENT_ARRAY_DECLS;;
;;EMPTY_SET_CONTENT_ARRAY_DECLS;;
;;EMPTY_MAP_CONTENT_ARRAY_DECLS;;

(declare-datatypes (
      (ErrorCode 0)
      ;;RESULTS_FWD;;
    ) (
    ( (result_error (error_id Int)) (result_bmc (bmc_id String)) )
    ;;RESULTS;;
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
