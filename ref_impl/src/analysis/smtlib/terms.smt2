;//-------------------------------------------------------------------------------------------------------
;// Copyright (C) Microsoft. All rights reserved.
;// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;//-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( (BNone 0) (BBool 0) (BInt 0) (BString 0)
                     (BTupleExact 3)
                     (BRecordExact 3)
                     ;(BEntity 3)
                     ) (
    ( (bsq_none) )
    ( (bsq_true) (bsq_false) )
    ( (bsq_int (bsq_int_value Int)) )
    ( (bsq_string (bsq_string_value String)) )

    ( par (T0 T1 T2) ((bsq_tuplex (bsq_tuplex_size Int) (bsq_tuplex_entry0 T0) (bsq_tuplex_entry1 T1) (bsq_tuplex_entry2 T2))) )
    ( par (T0 T1 T2) ((bsq_recordx (bsq_recordx_size Int) (bsq_recordx_name0 String) (bsq_recordx_value0 T0) (bsq_recordx_name1 String) (bsq_recordx_value1 T1) (bsq_recordx_name2 String) (bsq_recordx_value2 T2))) )

    ;( par (T0 T1 T2) ((bsq_entity (bsq_entity_size Int) (bsq_entity_name0 String) (bsq_entity_value0 T0) (bsq_entity_name1 String) (bsq_entity_value1 T1) (bsq_entity_name2 String) (bsq_entity_value2 T2))) )
))

(declare-datatypes ( (BTupleGeneral 0)
                     ;(BRecord 3)
                     (BTerm 0) ) (
    ( (bsq_tupleg (bsq_tupleg_size Int) (bsq_tupleg_entry0 BTerm) (bsq_tupleg_entry1 BTerm) (bsq_tupleg_entry2 BTerm)) )
    ;( par (T0 T1 T2) ((bsq_record (bsq_record_size Int) (bsq_record_name0 String) (bsq_record_value0 T0) (bsq_record_name1 String) (bsq_record_value1 T1) (bsq_record_name2 String) (bsq_record_value2 T2))) )

    ( (bsq_term_none) (bsq_term_bool (bsq_term_bool_value BBool)) (bsq_term_int (bsq_term_int_value BInt)) (bsq_term_string (bsq_term_string_value BString)) (bsq_term_tuple (bsq_term_tuple_value BTupleGeneral)) )
))

(define-fun foo ((x BBool)) BInt
    (ite (= x bsq_true) 
        (bsq_int 1)
        (bsq_int 5)
        )
)

(define-fun bar ((x BTerm)) BInt
    (ite ((_ is bsq_term_bool) x)
        (foo (bsq_term_bool_value x))
        (bsq_int 11)
    )
)

(assert (= (bsq_int_value (bar (bsq_term_bool bsq_true))) 1))
(assert (= (bsq_int_value (bar bsq_term_none)) 11))

(declare-const et (BTupleExact BBool BInt BNone))
(assert (= et (bsq_tuplex 2 bsq_false (bsq_int 5) bsq_none)))

(declare-const eg (BTupleGeneral))
(assert (= eg (bsq_tupleg 2 (bsq_term_bool bsq_false) (bsq_term_int (bsq_int 5)) bsq_term_none)))

(check-sat)
(get-model)