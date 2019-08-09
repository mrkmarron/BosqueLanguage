;//-------------------------------------------------------------------------------------------------------
;// Copyright (C) Microsoft. All rights reserved.
;// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;//-------------------------------------------------------------------------------------------------------

(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

;;;;;;;;;;;;;;;;
;;Bosque value declarations

(declare-datatypes ( (BNone 0) (BBool 0) (BInt 0) (BString 0)
                     (BTuple0 0) (BTuple1 1) (BTuple2 2) (BTuple3 3)
                     (BRecord0 0) (BRecord1 1) (BRecord2 2) (BRecord3 3)
                     (BEntity0 0) (BEntity1 1) (BEntity2 2) (BEntity3 3)
                     ) (
    ( (bsq_none) )
    ( (bsq_true) (bsq_false) )
    ( (bsq_int (bsq_int_value Int)) )
    ( (bsq_string (bsq_string_value String)) )

    ( (bsq_tuple0) )
    ( par (T0) ((bsq_tuple1 (bsq_tuple1_value0 T0))) )
    ( par (T0 T1) ((bsq_tuple2 (bsq_tuple2_value0 T0) (bsq_tuple2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_tuple3 (bsq_tuple3_value0 T0) (bsq_tuple3_value1 T1) (bsq_tuple3_value2 T2))) )

    ( (bsq_record0) )
    ( par (T0) ((bsq_record1 (bsq_record1_name0 String) (bsq_record1_value0 T0))) )
    ( par (T0 T1) ((bsq_record2 (bsq_record2_name0 String) (bsq_record2_value0 T0) (bsq_record2_name1 String) (bsq_record2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_record3 (bsq_record3_name0 String) (bsq_record3_value0 T0) (bsq_record3_name1 String) (bsq_record3_value1 T1) (bsq_record3_name2 String) (bsq_record3_value2 T2))) )

    ( (bsq_entity0 (bsq_entity0_type String)) )
    ( par (T0) ((bsq_entity1 (bsq_entity1_type String) (bsq_entity1_field0 String) (bsq_entity1_value0 T0))) )
    ( par (T0 T1) ((bsq_entity2 (bsq_entity1_type String) (bsq_entity2_field0 String) (bsq_entity2_value0 T0) (bsq_entity2_field1 String) (bsq_value2_value1 T1))) )
    ( par (T0 T1 T2) ((bsq_entity3 (bsq_entity1_type String) (bsq_entity3_field0 String) (bsq_entity3_value0 T0) (bsq_entity3_field1 String) (bsq_entity3_value1 T1) (bsq_entity3_field2 String) (bsq_entity3_value2 T2))) )
))

(declare-datatypes ( (BTerm 0) ) (
    ( (bsq_term_none) (bsq_term_true) (bsq_term_false) (bsq_term_int (bsq_term_int_value Int)) (bsq_term_string (bsq_term_string_value String)) 
      (bsq_term_tuple (bsq_term_tuple_size Int) (bsq_term_tuple_entries (Array Int BTerm)))
      (bsq_term_record (bsq_term_record_size Int) (bsq_term_record_properties (Array Int String)) (bsq_term_record_entries (Array String BTerm)))
      (bsq_term_entity (bsq_term_entity_type String) (bsq_term_entity_entries (Array String BTerm)))
    )
))

(declare-datatypes ( (Result 1)
                     ) (
    (par (T) ((result_error (error_msg String)) (result_success (result_value T)) ))
))

;;;;;;;;;;;;;;;;
;;MIRType declarations

;;;;;;;;;;;;;;;;
;;Data coercion functions

(define-fun BoxTuple0 ((tup BTuple0)) BTuple 
    (bsq_tuple 0 bsq_term_none bsq_term_none bsq_term_none)
)

;;;;;;;;;;;;;;;;
;;Subtype operation

;;;;;;;;;;;;;;;;
;;Operators

(define-fun foo ((x BBool)) BInt
    (ite (= x bsq_true) 
        (let ((v (bsq_int 1)))
            v
        )
        (let ((v (bsq_int 5)))
            v
        )
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

(declare-const et (BTuple2 BBool BInt))
(assert (= et (bsq_tuple2 bsq_false (bsq_int 5))))

(declare-const eg (BTuple))
(assert (= eg (bsq_tuple 2 (bsq_term_bool bsq_false) (bsq_term_int (bsq_int 5)) bsq_term_none)))

(check-sat)
(get-model)