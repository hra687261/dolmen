(set-logic HO_UFLIA)

(declare-sort-parameter A)
(declare-const id_ (-> A A))

(declare-sort Pair 2)

(declare-sort-parameter B)
(declare-sort-parameter C)
(declare-const pair (-> B C (Pair B C)))

; Check whether the printing/export funcitonality correctly inserts
; the required type annotation on the inner `id_`
(define-const b1 Int (id_ (as id_ (-> Int Int)) 5))

; Check that the `as` annotations are correctly interpreted in
; sexpr/annotations too
(assert (
  forall ((x Int)) (
    ! (= x x)
    :pattern ((id_ (as id_ (-> Int Int)) x))
  )
 )
)

(assert (
  forall ((x (-> Int (Pair Int Int)))) (= x (pair 13))
 )
)
