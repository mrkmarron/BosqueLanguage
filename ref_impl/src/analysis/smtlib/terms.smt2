;//-------------------------------------------------------------------------------------------------------
;// Copyright (C) Microsoft. All rights reserved.
;// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;//-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ( (BNone 0) (BBool 0) (BInt 0) (BString 0)
                     (BTuple 3)
                     ;(BRecord 3)
                     ;(BEntity 3)
                     (BTerm 0) ) (
    ( (bsq_none) )
    ( (bsq_true) (bsq_false) )
    ( (bsq_int (bsq_int_value Int)) )
    ( (bsq_string (bsq_string_value String)) )

    ( par (T0 T1 T2) ((bsq_tuple (bsq_tuple_size Int) (bsq_tuple_entry0 T0) (bsq_tuple_entry1 T1) (bsq_tuple_entry2 T2))) )
    ;( par (T0 T1 T2) ((bsq_record (bsq_record_size Int) (bsq_record_name0 String) (bsq_record_value0 T0) (bsq_record_name1 String) (bsq_record_value1 T1) (bsq_record_name2 String) (bsq_record_value2 T2))) )

    ;( par (T0 T1 T2) ((bsq_entity (bsq_entity_size Int) (bsq_entity_name0 String) (bsq_entity_value0 T0) (bsq_entity_name1 String) (bsq_entity_value1 T1) (bsq_entity_name2 String) (bsq_entity_value2 T2))) )

    ( (bsq_term_none) (bsq_term_bool (bsq_term_bool_value BBool)) (bsq_term_int (bsq_term_int_value BInt)) (bsq_term_string (bsq_term_string_value BString)) (bsq_term_tuple (bsq_term_tuple_value (BTuple BTerm BTerm BTerm))) ;(bsq_term_record (bsq_term_record_value (BRecord BTerm BTerm BTerm))) (bsq_term_entity (bsq_term_entity_value (BEntity BTerm BTerm BTerm))) 
    )
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

(check-sat)
(get-model)