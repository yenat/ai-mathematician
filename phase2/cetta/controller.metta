;; Phase 2 inference controller on CeTTa (PeTTa dialect): MeTTa decides each
;; proof step, Lean checks it. The same search as ../controller.metta; the
;; operations it calls are MeTTa (host.metta), not Python. Differences from the
;; Hyperon version: the memory is &self, PeTTa has no `unify` (a pattern made
;; at run time is matched with `case`), and no type declarations are needed.

;; ---------------------------------------------------------------- search


;; (prove $st $d): a list of tactics that closes every goal of state $st,
;; using at most $d choice steps, or Fail.
(= (prove $st $d)
   (case (lean-observe $st)
     ((Done ())
      (Loop Fail)                           ; back at a goal already on this path
      ((Goal $g)
       (if (is-binder $g)
           (intro-then-prove $st $d)        ; introducing is never a wrong move
           (if (== $d 0)
               Fail
               (try-each $st $d (candidates $st $g))))))))

;; Goals of the form "for all x, ..." or "A implies B" are introduced first.
(= (is-binder $g)
   (case $g
     (((∀ $v $b) True)
      ((→ $a $b) True)
      ($_ False))))

(= (intro-then-prove $st $d)
   (let* (($t (intro-tactic $st))
          ($n (lean-try $st $t)))
     (if (== $n Fail)
         Fail
         (prepend $t (prove $n $d)))))

(= (prepend $t $rest)
   (if (== $rest Fail) Fail (cons-atom $t $rest)))

;; Try the candidate steps in order; the first that leads to a full proof wins.
(= (try-each $st $d $tacs)
   (if (== $tacs ())
       Fail
       (let* (($t (car-atom $tacs))
              ($others (cdr-atom $tacs))
              ($n (lean-try $st $t)))
         (if (== $n Fail)
             (try-each $st $d $others)
             (let $rest (prove $n (- $d 1))
               (if (== $rest Fail)
                   (try-each $st $d $others)
                   (cons-atom $t $rest)))))))

;; ---------------------------------------------------------------- candidates

;; The control strategy: the order in which steps are tried.
;;  1. a hypothesis that matches the goal, used directly (exact) or backwards
;;  2. a cheap finishing tactic (bridge to Lean's logic, then grind)
;;  3. forward: a one-hypothesis library fact whose hypothesis unifies with
;;     a current hypothesis adds its conclusion (have)
;;  4. a library lemma whose conclusion unifies with the goal (apply)
;;  5. an equivalence P <-> Q from the library with Q (or P) unifying with
;;     the goal: the goal becomes the other side
;;  6. unfolding the definition at the head of the goal
;;  7. stronger finishing tactics (unfolding the goal's definitions, then
;;     with the top facts of Search)
(= (candidates $st $g)
   (let* (($hyps (hyp-steps $st $g))
          ($close (closers $st $g))
          ($forward (forward-steps $st))
          ($lemmas (lemma-steps $g))
          ($iffs (iff-steps $g))
          ($unfold (unfold-steps $g)))
     (concat $hyps (first-of $close) $forward $lemmas $iffs $unfold (rest-of $close))))

;; Forward reasoning: hypotheses (h T) matched against (Elim L i T).
;; Newest hypothesis first: each lemma is used once per step, and applying it
;; to an old hypothesis again mostly re-derives a fact already known.
(= (forward-steps $st)
   (let $fs (reverse (lean-facts $st))
     (forward-tactics
       (collapse
         (let ($h $t) (superpose $fs)
           (match &self (Elim $name $i $t)
             (if (< $i (target-index)) ($name $h) (empty))))))))

;; Equivalences: (Iff name index P Q). Goal ~ Q: prove P instead (Right);
;; goal ~ P: prove Q instead (Left).
(= (iff-steps $g)
   (let* (($r (collapse (match &self (IffR $name $i $g)
                          (if (< $i (target-index)) (Right $name) (empty)))))
          ($l (collapse (match &self (IffL $name $i $g)
                          (if (< $i (target-index)) (Left $name) (empty))))))
     (iff-tactics $r $l)))

;; Hypotheses whose conclusion unifies with the goal.
(= (hyp-steps $st $g)
   (collapse
     (let $hs (lean-hyps $st)
       (let (Hyp $h $n $p) (superpose $hs)
         (case $g (($p (apply-tactic $h)) ($other (empty))))))))

;; Library lemmas that come before the theorem and whose conclusion unifies
;; with the goal: this is the retrieval step, done by MeTTa's own matching.
(= (lemma-steps $g)
   (let $cands
        (collapse
          (match &self (Lemma $name $i $n $g)
            (if (< $i (target-index)) ($name $n) (empty))))
     (map-apply (rank-lemmas $cands))))

(= (map-apply $names)
   (if (== $names ())
       ()
       (let* (($t (apply-tactic (car-atom $names)))
              ($rest (map-apply (cdr-atom $names))))
         (cons-atom $t $rest))))

;; Unfold the definition at the head of the goal, if it is one.
(= (unfold-steps $g)
   (let $head (head-of $g)
     (case (collapse (match &self (Def $head) $head))
       ((() ())
        ($found (let $t (unfold-tactic $head) ($t)))))))

(= (head-of $g)
   (if (== (get-metatype $g) Expression) (car-atom $g) $g))

;; ---------------------------------------------------------------- lists
(= (first-of $xs) (if (== $xs ()) () (let $h (car-atom $xs) ($h))))
(= (rest-of $xs) (if (== $xs ()) () (cdr-atom $xs)))
