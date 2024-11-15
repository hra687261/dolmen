(set-logic ALL)

(declare-sort E 0)
(declare-const s (NSeq E))


(assert (= (nseq.first s) (nseq.last s)))
(assert (=
  (nseq.set s (nseq.first s) (nseq.get s (nseq.first s)))
  (nseq.const (nseq.first s) (nseq.last s) (nseq.get s (nseq.first s)))
))

(assert (= s (nseq.relocate s (nseq.first s))))
(assert (= s (nseq.concat s s)))
(assert (= s (nseq.slice s (nseq.first s) (nseq.last s))))
(assert (= s (nseq.update s s)))

(check-sat)