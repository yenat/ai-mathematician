;; Lemma hints for a goal, chosen in MeTTa from the library alone (no human
;; proof of the goal is looked at).
;;
;; Definitions only: suggest.metta runs them from the command line, and
;; ../cetta/prove.metta calls (hn:hints-at index statement K) for its goals.
;; Needs &lib bound to meglib.metta; (hn:load) indexes it once.
;;
;; The goal is a statement at a library index; only declarations before that
;; index are used.
;;  1. similar theorems: the k = 10 earlier theorems whose statements share
;;     the most symbols with the goal (cosine similarity, rarer symbols
;;     weigh more: w(c) = 1 + 2 / ln(2 + number of earlier facts using c));
;;  2. from the most similar one ("the neighbour"):
;;     - the neighbour itself,
;;     - bridges: lemmas linking a symbol only the neighbour has (mul_nat) to
;;       one only the goal has (mul_SNo),
;;     - closures: lemmas concluding P (f ..) for P, f only the neighbour has
;;       (nat_p (mul_nat x y)),
;;     - lemmas about a single symbol of the goal, then of the neighbour;
;;  3. then the lemmas used by the proofs of the 10 similar theorems, each
;;     scored by the summed similarity of the theorems that use it.
;; The first K distinct names (default 30) are the hints.

!(import! &self fs)
!(import! &self str)
!(import! &self system)
!(bind! &hn (new-space))

(= (hn:arg $i $default)
   (if (> (system:argc) $i)
       (let $a (system:arg $i) (if (== (get-metatype $a) Symbol) (str:symbol->string $a) $a))
       $default))

;; Connectives and basic set symbols: not counted when comparing vocabularies.
(= (hn:generic) (set In nIn eq meg_and ex meg_or meg_not meg_False meg_True iff Prop meg_Type))

(= (hn:member $x $l)
   (if (== $l ()) false (if (== (car-atom $l) $x) true (hn:member $x (cdr-atom $l)))))
(= (hn:minus $a $b) (filter-atom $a $x (not (hn:member $x $b))))
(= (hn:inter $a $b) (filter-atom $a $x (hn:member $x $b)))
(= (hn:subset $a $b) (== (hn:minus $a $b) ()))
(= (hn:nongen $s) (hn:minus $s (hn:generic)))

;; ------------------------------------------------------------ the library

;; All symbols of an expression.
(= (hn:flat $e)
   (case (get-metatype $e)
     ((Symbol ($e))
      (Expression (hn:flat-list $e))
      ($o ()))))
(= (hn:flat-list $l)
   (if (== $l ()) () (union-atom (hn:flat (car-atom $l)) (hn:flat-list (cdr-atom $l)))))

;; The library constants of an expression, each once.
(= (hn:consts $e)
   (unique-atom (filter-atom (hn:flat $e) $s
     (not (== (collapse (match &hn (Idx $s $i $k) $i)) ())))))

(= (hn:record $r)
   (case $r
     (((MkIndexed $i (MkTheorem $n $p $t)) (Rec $i Thm $n $t $p))
      ((MkIndexed $i (MkAxiom $n $t)) (Rec $i Ax $n $t ()))
      ((MkIndexed $i (MkDefinition $n $b $t)) (Rec $i Def $n $t ())))))

;; Index every record: (Idx name i kind), then (Stmt name syms) and (Ty name type).
;; add-atom stores its argument as written, so values are computed first.
(= (hn:load)
   (let* (($recs (collapse (let $r (match &lib (MkIndexed $i $d) (MkIndexed $i $d)) (hn:record $r))))
          ($a (map-atom $recs $r (let (Rec $i $k $n $t $p) $r (add-atom &hn (Idx $n $i $k)))))
          ($b (map-atom $recs $r (let* (((Rec $i $k $n $t $p) $r) ($s (hn:consts $t)))
                                    (add-atom &hn (Stmt $n $s)))))
          ($c (map-atom $recs $r (let (Rec $i $k $n $t $p) $r (add-atom &hn (Ty $n $t))))))
     (size-atom $recs)))

(= (hn:idx $n) (match &hn (Idx $n $i $k) $i))
(= (hn:kind $n) (match &hn (Idx $n $i $k) $k))
(= (hn:stmt $n) (match &hn (Stmt $n $s) $s))
(= (hn:type $n) (match &hn (Ty $n $t) $t))

;; Lemmas used by a theorem's proof (definitions left out).
(= (hn:uses $n)
   (let $p (match &lib (MkIndexed $i (MkTheorem $n $p $t)) $p)
     (filter-atom (hn:consts $p) $u (not (== (hn:kind $u) Def)))))

;; A lemma: a theorem, or an axiom stating a proposition (not In, set, ...).
(= (hn:concl $t)
   (case $t
     (((∀ $v $b) (hn:concl $b))
      ((→ $a $b) (hn:concl $b))
      ($o $t))))
(= (hn:head $t) (if (== (get-metatype $t) Expression) (car-atom $t) $t))
(= (hn:lemma? $n)
   (case (hn:kind $n)
     ((Thm true)
      (Ax (not (hn:member (hn:head (hn:concl (hn:type $n))) (Prop meg_Type set Type))))
      ($o false))))

;; ------------------------------------------------------------ similarity

(= (hn:ln $x) (log-math 2.718281828459045 $x))

;; Symbol weights from the facts (axioms and theorems) before index $T.
(= (hn:weights $T)
   (let* (($facts (collapse (match &hn (Idx $n $i $k)
                              (if (and (< $i $T) (not (== $k Def))) $n (empty)))))
          ($all (sort-atom (foldl-atom $facts () $acc $n (union-atom (hn:stmt $n) $acc))))
          ($counts (hn:runs $all)))
     (map-atom $counts $c (let* ((($s $m) $c) ($w (+ 1.0 (/ 2.0 (hn:ln (+ 2 $m))))))
                            (add-atom &hn (W $s $w))))))

;; (a a b) -> ((a 2) (b 1)) for a sorted list.
(= (hn:runs $l) (if (== $l ()) () (hn:runs-from (car-atom $l) 1 (cdr-atom $l))))
(= (hn:runs-from $x $m $l)
   (if (== $l ()) (($x $m))
     (if (== (car-atom $l) $x)
         (hn:runs-from $x (+ $m 1) (cdr-atom $l))
         (cons-atom ($x $m) (hn:runs-from (car-atom $l) 1 (cdr-atom $l))))))

(= (hn:w $c) (case (collapse (match &hn (W $c $w) $w)) ((($w) $w) ($o 1.0))))
(= (hn:sq-sum $s) (foldl-atom $s 0.0 $acc $c (+ $acc (* (hn:w $c) (hn:w $c)))))

(= (hn:cos $a $b)
   (let $num (hn:sq-sum (hn:inter $a $b))
     (if (== $num 0.0) 0.0
       (/ $num (sqrt-math (+ (* (hn:sq-sum $a) (hn:sq-sum $b)) 1.0e-9))))))

;; The k theorems before $T most similar to the goal: ((sim name) ...).
(= (hn:similar $gs $T $k)
   (let* (($thms (collapse (match &hn (Idx $n $i Thm) (if (< $i $T) $n (empty)))))
          ($scored (map-atom $thms $n ((- 0.0 (hn:cos $gs (hn:stmt $n))) $n)))
          ($top (hn:take (sort-atom $scored) $k)))
     (map-atom $top $p (let ($m $n) $p ((- 0.0 $m) $n)))))

(= (hn:take $l $k) (if (or (== $l ()) (== $k 0)) () (cons-atom (car-atom $l) (hn:take (cdr-atom $l) (- $k 1)))))

;; Lemmas of the neighbours' proofs, by summed similarity: ((-score name) ...).
(= (hn:from-proofs $sims $T)
   (let* (($pairs (foldl-atom $sims () $acc $p
                    (let* ((($s $n) $p)
                           ($us (filter-atom (hn:uses $n) $u (and (< (hn:idx $u) $T) (hn:lemma? $u)))))
                      (hn:append $acc (cons-atom ($n $s) (map-atom $us $u ($u $s)))))))
          ($names (unique-atom (map-atom $pairs $p (let ($n $s) $p $n))))
          ($scored (map-atom $names $n ((- 0.0 (hn:score-of $n $pairs)) $n))))
     (map-atom (sort-atom $scored) $p (let ($m $n) $p $n))))
(= (hn:score-of $n $pairs)
   (foldl-atom $pairs 0.0 $acc $p (let ($m $s) $p (if (== $m $n) (+ $acc $s) $acc))))

;; ------------------------------------------------------------ the hints

(= (hn:closure? $n $theirs)
   (let $c (hn:concl (hn:type $n))
     (if (and (== (get-metatype $c) Expression) (== (size-atom $c) 2))
         (let ($P $x) $c
           (and (hn:member $P $theirs)
                (and (== (get-metatype $x) Expression) (hn:member (hn:head $x) $theirs))))
         false)))

(= (hn:hints $g $K) (hn:hints-at (hn:idx $g) (hn:stmt $g) $K))

;; Hints for a statement whose symbols are $gsyms, at library index $T.
(= (hn:hints-at $T $gsyms $K)
   (let* (($w (hn:weights $T))
          ($sims (hn:similar $gsyms $T 10))
          (($s0 $nb) (car-atom $sims))
          ($gs (hn:nongen $gsyms))
          ($ns (hn:nongen (hn:stmt $nb)))
          ($theirs (hn:minus $ns $gs))
          ($ours (hn:minus $gs $ns))
          ($both (union-atom $gs $ns))
          ($L (sort-atom (collapse (match &hn (Idx $n $i $k)
                 (if (and (< $i $T) (and (not (== $n $nb)) (hn:lemma? $n)))
                     (if (== (hn:nongen (hn:stmt $n)) ()) (empty) $n)
                     (empty))))))
          ($strict (filter-atom $L $n (let $s (hn:nongen (hn:stmt $n))
                     (and (hn:subset $s $both)
                          (and (not (== (hn:inter $s $theirs) ())) (not (== (hn:inter $s $ours) ())))))))
          ($closure (filter-atom $L $n (let $s (hn:nongen (hn:stmt $n))
                      (and (hn:subset $s $theirs) (and (== (size-atom $s) 2) (hn:closure? $n $theirs))))))
          ($single-g (filter-atom $L $n (let $s (hn:nongen (hn:stmt $n))
                       (and (== (size-atom $s) 1) (hn:subset $s $gs)))))
          ($single-n (filter-atom $L $n (let $s (hn:nongen (hn:stmt $n))
                       (and (== (size-atom $s) 1) (hn:subset $s $theirs)))))
          ($ranked (hn:from-proofs $sims $T))
          ($all (hn:append (cons-atom $nb $strict)
                  (hn:append $closure (hn:append $single-g (hn:append $single-n $ranked))))))
     (hn:take (hn:dedup $all ()) $K)))

;; Lists in order (union-atom does not keep it).
(= (hn:append $a $b)
   (if (== $a ()) $b (cons-atom (car-atom $a) (hn:append (cdr-atom $a) $b))))

(= (hn:dedup $l $seen)
   (if (== $l ()) ()
     (let $h (car-atom $l)
       (if (hn:member $h $seen) (hn:dedup (cdr-atom $l) $seen)
         (cons-atom $h (hn:dedup (cdr-atom $l) (cons-atom $h $seen)))))))
