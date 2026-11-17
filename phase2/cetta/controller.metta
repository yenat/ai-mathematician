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
           (hint-or-intro $st $d)           ; introducing is never a wrong move
           (let $r (unpack-then-prove $st $d (unpack-steps $st))
             (if (== $r Fail)
                 (if (== $d 0)
                     Fail
                     (try-each $st $d (candidates $st $g)))
                 $r)))))))

;; Unpacking a hypothesis "there is an x with P x" or "A and B" loses nothing,
;; so, like introducing, it costs no choice: it is done before anything else.
;; If it leads nowhere, the goal is searched as usual.
(= (unpack-then-prove $st $d $tacs)
   (if (== $tacs ())
       Fail
       (let* (($t (car-atom $tacs))
              ($n (lean-try $st $t)))
         (if (== $n Fail) Fail (prepend $t (prove $n $d))))))

;; Goals of the form "for all x, ..." or "A implies B" are introduced first.
(= (is-binder $g)
   (case $g
     (((∀ $v $b) True)
      ((→ $a $b) True)
      ($_ False))))

;; A hinted lemma may match a "for all" goal as a whole (a case split over
;; all integers, say), so hints are tried before the goal is introduced.
(= (hint-or-intro $st $d)
   (let $hints (if (== $d 0) () (hint-split-steps (p2:goal-of $st)))
     (let $r (try-each $st $d $hints)
       (if (== $r Fail) (intro-then-prove $st $d) $r))))

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
;;  0. hinted lemmas that fit the goal (see hint-steps), when any are given
;;  1. a hypothesis that matches the goal, used directly (exact) or backwards
;;  2. a cheap finishing tactic (bridge to Lean's logic, then grind); for an
;;     "exists" goal, an object in context as the witness
;;  3. forward: a hinted lemma whose hypotheses all match facts, or a
;;     one-hypothesis library fact whose hypothesis matches a fact, adds its
;;     conclusion (have); rewriting a fact or the goal with a hinted equation
;;  4. a library lemma whose conclusion unifies with the goal (apply)
;;  5. an equivalence P <-> Q from the library with Q (or P) unifying with
;;     the goal: the goal becomes the other side
;;  6. unfolding the definition at the head of the goal
;;  7. stronger finishing tactics (unfolding the goal's definitions, then
;;     with the top facts of Search)
(= (candidates $st $g)
   (let* (($hyps (union-atom (hyp-steps $st $g) (hint-steps $g)))
          ($close (closers $st $g))
          ($forward (union-atom (hint-rewrite-steps $st) (forward-steps $st)))
          ($lemmas (lemma-steps $g))
          ($iffs (iff-steps $g))
          ($unfold (unfold-steps $g)))
     (concat $hyps (p2:in-order $st (union-atom (hint-forward-steps $st) (first-of $close)))
             (witness-steps $st $g True)
             (p2:in-order $st $forward) $lemmas (union-atom (union-atom (hint-rewrite-rev-steps $st) (split-steps $st))
                                          (union-atom $iffs $unfold))
             (union-atom (rest-of $close) (witness-steps $st $g False)))))

;; Adding a fact (have) and rewriting inside a fact commute with each other:
;; "A; B" and "B; A" reach the same state. So two such steps in a row are
;; taken in one fixed order (the order of their keys), unless the second
;; uses what the first produced. Other steps pass unchanged.
(= (p2:in-order $st $tacs)
   (case (collapse (match &self (P2Via $st $t) $t))
     ((($p)
       (case (p2:step-info $p)
         ((none $tacs)
          (($pout $puses $pkey)
           (filter-atom $tacs $t
             (case (p2:step-info $t)
               ((none true)
                (($out $uses $key)
                 (or (p2:member $pout $uses) (p2:after $key $pkey))))))))))
      ($o $tacs))))
;; (output uses key) of a commuting step, or none.
(= (p2:step-info $t)
   (case $t
     (((Have $f $e) ($f (cdr-atom $e) $e))
      ((Rewrite $l $n $k) (if (== $n goal) none ($n ($n) (rw $l $n))))
      ($o none))))
(= (p2:after $e $prev) (and (not (== $e $prev)) (== (car-atom (sort-atom ($prev $e))) $prev)))

;; Forward reasoning: hypotheses (h T) matched against (Elim L i T).
;; Newest hypothesis first: each lemma is used once per step, and applying it
;; to an old hypothesis again mostly re-derives a fact already known.
;; A lemma already applied to the same hypothesis on this path would only
;; re-derive a known fact (which ends the branch, after costing a step), so
;; such pairs are dropped before choosing.
(= (forward-steps $st)
   (let $fs (reverse (lean-facts $st))
     (forward-tactics
       (collapse
         (let ($h $t) (superpose $fs)
           (match &self (Elim $name $i $t)
             (if (and (< $i (target-index)) (not (p2:path-applied $st $name $h)))
                 ($name $h) (empty))))))))

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

;; Unpacking: a hypothesis "there is an x with P x" or "A and B" is used by
;; applying it, after which x and P x (or A and B) are introduced as new
;; hypotheses. The unpacked hypothesis is cleared so it is unpacked only once.
;; A hypothesis already unpacked on this path (still listed when later
;; facts depend on it) is not unpacked again.
;; "A and B" with A and B both known already gives nothing new.
(= (unpack-steps $st)
   (collapse
     (let* (((Obs $g $hyps) (p2:seen $st))
            ($known (p2:types (Obs $g $hyps))))
       (let ($n $t) (superpose $hyps)
         (if (p2:unpacked-on-path $st $n) (empty)
           (case $t
             (((ex $T $p) (unpack-tactic $n))
              ((meg_and $a $b) (if (and (p2:member $a $known) (p2:member $b $known))
                                   (empty) (unpack-tactic $n)))
              ($other (empty)))))))))

;; Rewriting backwards (B to A) with a hinted equation A = B, after the
;; forward steps and the lemmas. Only when B is a compound term: a bare
;; constant on the right (x = Empty, say) would rewrite every Empty into an
;; undetermined x.
(= (hint-rewrite-rev-steps $st)
   (let (Obs $g $hyps) (p2:seen $st)
     (collapse
       (match &self (P2Hint $name)
         (match &self (Lemma $name $i $nh (eq set $a $b))
           (if (and (< $i (target-index)) (== (get-metatype $b) Expression))
               (let $rhead (head-of $b)
                 (superpose
                   ((if (p2:mentions $rhead $g) (rewrite-rev-tactic $name goal) (empty))
                    (let ($n $t) (superpose $hyps)
                      (if (p2:mentions $rhead $t) (rewrite-rev-tactic $name $n) (empty))))))
               (empty)))))))

;; A case split on a fact "A or B": two goals, the current one under A and
;; under B. Unlike unpacking it costs a choice, since it doubles the work and
;; most "or" facts derived along the way are not needed.
(= (split-steps $st)
   (collapse
     (let (Obs $g $hyps) (p2:seen $st)
       (let ($n $t) (superpose $hyps)
         (case $t
           (((meg_or $a $b) (unpack-tactic $n))
            ($other (empty))))))))

;; A witness for "there is an x with P x": an object in context. Objects
;; the goal does not mention (obtained along the way, by unpacking a fact)
;; are the natural candidates and come early, oldest first; the goal's own
;; objects are already fixed by the statement and come last. The goal
;; becomes P x.
(= (witness-steps $st $g $fresh)
   (case $g
     (((ex set $p)
       (let* (((Obs $g2 $hyps) (p2:seen $st))
              ($in-goal (unique-atom (p2:symbols $g)))
              ($objs (collapse (let ($n $t) (superpose $hyps) (if (== $t set) $n (empty)))))
              ($chosen (filter-atom $objs $o (== $fresh (not (p2:member $o $in-goal)))))
              ($ordered (union-atom (filter-atom $objs $o1 (not (p2:member $o1 $in-goal)))
                                    (filter-atom $objs $o2 (p2:member $o2 $in-goal))))
              ($hinted (if $fresh (witness-hint-terms $ordered) ())))
         (union-atom (map-atom $hinted $w (witness-tactic $w))
                     (map-atom $chosen $o (witness-tactic $o)))))
      ($other ()))))

;; Hinted witness terms (witness_hints.metta) for this goal, each placeholder
;; _1, _2 filled with every object in context.
(= (witness-hint-terms $objs)
   (let $templates (let $gn (p2:get goal) (collapse (match &self (WitnessHint $gn $tm) $tm)))
     (p2:dedup (foldl-atom $templates () $acc $tpl (union-atom $acc (p2:instances $tpl $objs))) ())))

(= (p2:instances $tpl $objs)
   (p2:fill-all $tpl (p2:placeholders $tpl) $objs))
(= (p2:fill-all $tpl $phs $objs)
   (if (== $phs ()) ($tpl)
     (let* (($ph (car-atom $phs)) ($rest (cdr-atom $phs)))
       (foldl-atom $objs () $acc2 $ob
         (union-atom $acc2 (p2:fill-all (p2:subst-sym $tpl $ph $ob) $rest $objs))))))
(= (p2:placeholders $t)
   (filter-atom (unique-atom (p2:symbols $t)) $sy (p2:member $sy (_1 _2 _3))))
(= (p2:subst-sym $t $from $to)
   (case (get-metatype $t)
     ((Symbol (if (== $t $from) $to $t))
      (Expression (map-atom $t $u (p2:subst-sym $u $from $to)))
      ($other1 $t))))

;; Forward use of a hinted lemma with several hypotheses: MeTTa matches each
;; hypothesis pattern, in order and with shared variables, against the facts
;; in context; the lemma's conclusion is then added as a new fact.
;; In the premise ranking's order, as for library lemmas: the lemma most like
;; the theorem first (a generic fact applied first would feed its result to
;; the lemma that matters, e.g. the natural-number version applied to n*n).
(= (hint-forward-steps $st)
   (let* (($fs (reverse (lean-facts $st)))
          ($pairs (collapse
            (match &self (P2Hint $name)
              (match &self (Hyps $name $i $pats)
                (if (and (< $i (target-index)) (and (not (p2:equation? $name)) (p2:rigid? $pats)))
                    (let* (($hs (p2:match-hyps $pats $fs))
                           ($t (hint-forward-tactic $st $name $hs)))
                      ((str:symbol->string $name) $t))
                    (empty))))))
          )
     (p2:in-rank-order $pairs)))

(= (p2:match-hyps $pats $fs)
   (if (== $pats ())
       ()
       (let $p (car-atom $pats)
         (let ($n $t) (superpose $fs)
           (case $t
             (($p (let $rest (p2:match-hyps (cdr-atom $pats) $fs) (cons-atom $n $rest)))
              ($other (empty))))))))

;; A hypothesis that is a bare variable matches any fact, so a lemma with one
;; (and A B from A and B, say) would only build ever larger facts: such lemmas
;; are not used forward, as for the one-hypothesis facts of ltm.py.
(= (p2:rigid? $pats)
   (if (== $pats ()) true
     (if (== (get-metatype (car-atom $pats)) Variable) false (p2:rigid? (cdr-atom $pats)))))

;; Equations are used for rewriting, not as forward facts.
(= (p2:equation? $name)
   (not (== (collapse (match &self (Lemma $name $i $k (eq set $a $b)) $name)) ())))

;; Rewriting with a hinted equation L : A = B (under hypotheses): in each fact
;; with an instance of A, and in the goal. The hypotheses of L become
;; new goals.
(= (hint-rewrite-steps $st)
   (let (Obs $g $hyps) (p2:seen $st)
     (collapse
       (match &self (P2Hint $name)
         (match &self (Lemma $name $i $nh (eq set $a $b))
           (if (< $i (target-index))
               (superpose
                 ((if (p2:lhs-occurs $name $g) (rewrite-tactic $name goal) (empty))
                  (let ($n $t) (superpose $hyps)
                    (if (p2:lhs-occurs $name $t) (rewrite-tactic $name $n) (empty)))))
               (empty)))))))

;; Does the left side A of equation L : A = B match a subterm of $t? (A
;; rewrite that finds no instance of A fails, and costs a step.) The lemma is
;; read again for each test, so its pattern variables are fresh.
;; A bare variable A (x = Empty from Subq x Empty) would match everything:
;; such equations are not used for rewriting.
(= (p2:lhs-occurs $name $t)
   (let $a (match &self (Lemma $name $i $nh (eq set $a $b)) $a)
     (if (== (get-metatype $a) Variable) false (p2:occurs $a $t))))
(= (p2:occurs $a $t)
   (case $t
     (($a true)
      ($o (if (== (get-metatype $t) Expression) (p2:occurs-any $a $t) false)))))
(= (p2:occurs-any $a $ts)
   (if (== $ts ()) false
     (if (p2:lhs-occurs-in $a (car-atom $ts)) true (p2:occurs-any $a (cdr-atom $ts)))))
(= (p2:lhs-occurs-in $a $t) (p2:occurs $a $t))

;; Hints: lemmas named from outside the search (by hand now, by a proof graph
;; later), tried first. MeTTa decides where a hint fits before Lean is asked,
;; because Lean's `apply` also succeeds through the library's encodings of
;; "exists" and "and", producing goals that lead nowhere:
;;  - a split lemma (concluding P x for a variable P, for every x in some
;;    domain D) fits a goal "for every x in D"; the search never tries these
;;    unless hinted, since by their conclusion alone they fit everything
;;  - an ordinary lemma fits where its conclusion matches the goal
;;  - a subset lemma A ⊆ B fits a goal x ∈ B
;; A hint is still only a lemma before the theorem.
(= (hint-split-steps $g)
   (collapse
     (match &self (P2Hint $name)
       (match &self (HOLemma $name $i $k $c)
         (if (< $i (target-index))
             (match &self (Hyps $name $i $pats)
               (let $last (car-atom (reverse $pats))
                 (case $g
                   (((∀ $v (→ $h $body)) (case $h (($last (apply-tactic $name)) ($o (empty)))))
                    ($other (empty))))))
             (empty))))))

(= (p2:goal-of $st) (let (Obs $g $hyps) (p2:seen $st) $g))

;; Lemmas about the goal's specific term (a conclusion like nat_p (mul_nat x
;; y)) come before lemmas that fit any term (nat_p x); the ranking orders
;; each group.
(= (hint-steps $g)
   (let $fits (hint-fits $g)
     (union-atom (p2:in-rank-order (filter-atom $fits $f (let ($n $t $s) $f $s)))
                 (p2:in-rank-order (filter-atom $fits $f (let ($n $t $s) $f (not $s)))))))

(= (p2:specific? $c)
   (if (== (get-metatype $c) Expression)
       (p2:any-expression (cdr-atom $c))
       false))
(= (p2:any-expression $xs)
   (if (== $xs ()) false
     (if (== (get-metatype (car-atom $xs)) Expression) true (p2:any-expression (cdr-atom $xs)))))

(= (hint-fits $g)
     (collapse
       (match &self (P2Hint $name)
         (match &self (Lemma $name $i $k $c)
           (if (< $i (target-index))
               (let $s (p2:specific? $c)        ; measured before $c is matched
                 (case $c
                   (((Subq $a $b) (case $g (((In $x $b) ((str:symbol->string $name) (apply-tactic $name) $s)) ($o (empty)))))
                    ($other (case $g (($c ((str:symbol->string $name) (apply-tactic $name) $s)) ($o (empty))))))))
               (empty))))))

;; (name tactic) pairs -> the tactics, lemmas in the premise ranking's order
;; (the lemma most like the theorem first), without repeats.
(= (p2:in-rank-order $pairs)
   (let $order (p2:ranked (p2:dedup (map-atom $pairs $p (car-atom $p)) ()))
     (p2:dedup (foldl-atom $order () $acc $n
                 (union-atom $acc (collapse (let $p (superpose $pairs)
                                              (if (== (car-atom $p) $n) (car-atom (cdr-atom $p)) (empty))))))
               ())))

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
