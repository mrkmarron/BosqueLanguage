;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(set-option :timeout 10000)

(declare-datatypes ( 
      (bsq_stringof 0)
      (bsq_guid 0)
      (bsq_datahash 0)
      (bsq_cryptohash 0)
      (bsq_eventtime 0)
      (bsq_enum 0)
      (bsq_idkey 0)
      (bsq_idkey_eventtime 0)
      (bsq_idkey_guid 0)
      (bsq_idkey_datahash 0)
      (bsq_idkey_cryptohash 0)
      (BKeyValue 0)
    ) (
    ( (bsq_stringof@cons (bsq_stringof_type String) (bsq_stringof_value String)) )
    ( (bsq_guid@cons (bsqy_guid_value String)) )
    ( (bsq_datahash@cons (bsq_datahash Int)) )
    ( (bsq_cryptohash@cons (bsq_cryptohash String)) )
    ( (bsq_eventtime@cons (bsq_eventtime_value Int)) )
    ( (bsq_enum@cons (bsq_enum_type String) (bsq_enum_value Int)) )
    ( (bsq_idkey@cons (bsq_idkey_type String) (bsq_idkey_value (Array String BKeyValue))) )
    ( (bsq_idkey_eventtime@cons (bsq_idkey_eventtime_type String) (bsq_idkey_eventtime_value Int)) )
    ( (bsq_idkey_guid@cons (bsq_idkey_guid_type String) (bsq_idkey_guid_value String)) )
    ( (bsq_idkey_datahash@cons (bsq_idkey_datahash_type String) (bsq_idkey_datahash_value Int)) )
    ( (bsq_idkey_cryptohash@cons (bsq_idkey_cryptohash_type String) (bsq_idkey_cryptohash_value String)) )
    (
      (bsqkey_none) 
      (bsqkey_bool (bsqkey_bool_value Bool))
      (bsqkey_int (bsqkey_int_value Int))
      (bsqkey_string (bsqkey_string_value String))
      (bsqkey_stringof (bsqkey_stringof_value bsq_stringof))
      (bsqkey_guid (bsqkey_guid_value bsq_guid))
      (bsqkey_datahash (bsqkey_datahash bsq_datahash))
      (bsqkey_cryptohash (bsqkey_cryptohash bsq_cryptohash))
      (bsqkey_eventtime (bsqkey_eventtime_value bsq_eventtime))
      (bsqkey_enum (bsqkey_enum_value bsq_enum))
      (bsqkey_idkey (bsqkey_idkey_value bsq_idkey))
      (bsqkey_idkey_eventtime (bsqkey_idkey_eventtime_value bsq_idkey_eventtime))
      (bsqkey_idkey_guid (bsqkey_idkey_guid_value bsq_idkey_guid))
      (bsqkey_idkey_datahash (bsqkey_idkey_datahash_value bsq_idkey_datahash))
      (bsqkey_idkey_cryptohash (bsqkey_idkey_cryptohash_value bsq_idkey_cryptohash))
    )
))

(declare-datatypes ( 
    (bsq_buffer 0)
    (bsq_isotime 0)
    (bsq_regex 0)
    (bsq_tuple 0)
    (bsq_record 0)
    ;;NOMINAL_DECLS_FWD;;
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_buffer@cons (bsq_buffer_type String) (bsq_buffer_contents String)) )
    ( (bsq_isotime@cons (bsq_isotime_value Int)) )
    ( (bsq_regex@cons (bsq_regex_value String)) )
    ( (bsq_tuple@cons (bsq_tuple_ispod Bool) (bsq_tuple_isapi Bool) (bsq_tuple_entries (Array Int BTerm)))  )
    ( (bsq_record@cons (bsq_tuple_ispod Bool) (bsq_tuple_isapi Bool) (bsq_record_entries (Array String BTerm))) )
    ;;NOMINAL_CONSTRUCTORS;;
    (
    ;;NOMINAL_OBJECT_CONSTRUCTORS;;
    )
    (
      (bsqterm@clear)
      (bsqterm_key (bsqterm_key_value BKeyValue))
      (bsqterm_buffer (bsqterm_buffer_value bsq_buffer))
      (bsqterm_isotime (bsqterm_isotime_value bsq_isotime))
      (bsqterm_regex (bsqterm_regex_value bsq_regex))
      (bsqterm_tuple (bsqterm_tuple_value bsq_tuple)) 
      (bsqterm_record (bsqterm_record_value bsq_record))
      (bsqterm_object (bsqterm_object_type String) (bsqterm_object_value bsq_object))
    )
))

(define-fun bsqkey_get_nominal_type ((keyv BKeyValue)) String
xxxx
)

(define-fun bsqterm_get_nominal_type ((term BTerm)) String
xxxx
)

;;EPHEMERAL_DECLS;;

(declare-const bsqterm_none BTerm)
(assert (= bsqterm_none (bsqterm_key bsqkey_none)))

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
