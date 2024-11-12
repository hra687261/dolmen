(set-logic ALL)

(declare-sort E 0)
(declare-const s (Seq E))


(assert (= seq.empty (as seq.empty (Seq E))))
(assert (= s (seq.unit (seq.nth s 0))))
(assert (= s (seq.update s 0 s)))
(assert (= s (seq.extract s 0 (seq.len s))))
(assert (= s (seq.++ seq.empty s)))
(assert (= s (seq.++ s seq.empty)))

(check-sat)