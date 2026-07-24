(set-info :smt-lib-version 2.6)
(set-logic ALL)

; This file should in principle belong to UFLRA, at least intuitively.
; However, the wonders of the SMT-LIB spec states that in UFLRA, the non-literal
; side of a multiplication does not allow a top symbol that is not an arithmetic
; one (basically, you really need a variable or constant, and not "any expression").

; SZS status Success
(declare-sort $$unsorted 0)
(declare-fun tptp.f (Real) Real)
(assert (not (not (forall ((X Real) (Y Real)) (=> (> Y 0.0) (< (tptp.f X) (+ (+ (* (/ 1 2) (tptp.f (+ X (- Y)))) (* (/ 1 2) (tptp.f (+ X Y)))) (- 1.0))))))))
(check-sat)
