;; Tactics in MeTTa: each tactic turns a goal into subgoals and a piece of
;; proof term; the finished term is checked by kernel.metta.  No Lean.
;;
;; A goal is (G ctx names T): ctx lists the hypotheses' types, newest first
;; (de Bruijn, as in kernel.metta), names their names, T the target.
;; A tactic step returns (Ok (subgoal ...) template) or (Bad reason); the
;; template is a proof term with (Hole i) where subgoal i's proof goes.
;; Every subgoal lives in exactly the context of its hole, so filling a hole
;; needs no shifting.
;;
;; The tactics:
;;   (Intro x)            ∀x. B / A → B: assume x                    λ
;;   (Have f e)           add f : type of e                          (λ f. _) e
;;   (Apply e)            close the goal by e, its remaining premises
;;                        becoming subgoals (∃/∧ elimination too)    e _ _
;;   (Unpack h)           Apply h (∃ / ∧ elimination), then hide h
;;   (Witness w [k])      prove ∃x. P x by P w (assumptions named q<k> hq<k>)
;;                                                                   λQ h. h w _
;;   (Unfold c)           unfold definition c in the goal and hypotheses
;;   (Rewrite e h)        e : x = y; rewrite x to y in hypothesis h, or in
;;                        the target when h is `goal`
;; In e, `_` is an argument found by matching, as Lean's `@L _ h` does.
;; Unknowns are (M k d): metavariable k seen under d binders.

!(import! &self "/home/yenat/ai-mathematician/phase2/metta/kernel.metta")
!(import! &self json)

;; -------------------------------------------------------------- metavariables

(= (mk:inst-m1 $b $a) (mk:inst $b $a))

(= (mk:lookup $k $sigma)
   (if (== $sigma ()) None
     (let (($m $v) $rest) ((car-atom $sigma) (cdr-atom $sigma))
       (if (== $m $k) (Some $v) (mk:lookup $k $rest)))))

;; t with every assigned metavariable replaced by its value.
(= (mk:resolve $sigma $t)
   (case $t
     (((M $m $d) (case (mk:lookup $m $sigma) (((Some $v) (mk:resolve $sigma (mk:shift $d 0 $v))) (None $t))))
      ((A $f $a) (A (mk:resolve $sigma $f) (mk:resolve $sigma $a)))
      ((L $T $b) (L (mk:resolve $sigma $T) (mk:resolve $sigma $b)))
      ((P $T $b) (P (mk:resolve $sigma $T) (mk:resolve $sigma $b)))
      ($other $t))))

(= (mk:has-m $t)
   (case $t
     (((M $m $d) true)
      ((A $f $a) (if (mk:has-m $f) true (mk:has-m $a)))
      ((L $T $b) (if (mk:has-m $T) true (mk:has-m $b)))
      ((P $T $b) (if (mk:has-m $T) true (mk:has-m $b)))
      ($other false))))

;; Is every free variable of t (under c binders) at least d?
(= (mk:free-from $t $d $c)
   (case $t
     (((V $i) (if (< $i $c) true (>= (- $i $c) $d)))
      ((A $f $a) (if (mk:free-from $f $d $c) (mk:free-from $a $d $c) false))
      ((L $T $b) (if (mk:free-from $T $d $c) (mk:free-from $b $d (+ $c 1)) false))
      ((P $T $b) (if (mk:free-from $T $d $c) (mk:free-from $b $d (+ $c 1)) false))
      ($other true))))

;; ------------------------------------------------------------------- matching

;; (mk:pmatch p t sigma fuel): extend sigma so that p (with metavariables) and
;; t agree, or Bad.  Syntactic first; if that fails, unfold definitions as
;; the kernel's conversion does, at most `fuel` times.
(= (mk:pmatch $p $t $sigma $fuel)
   (let $p1 (mk:resolve $sigma $p)
     (case $p1
       (((M $m $d)
         (if (mk:free-from $t $d 0) (cons-atom ($m (mk:shift (- 0 $d) 0 $t)) $sigma) (Bad (escapes $t))))
        ($other
         (if (== $p1 $t) $sigma
           (let $r (mk:pmatch-struct $p1 $t $sigma $fuel)
             (if (mk:bad? $r) (mk:pmatch-delta $p1 $t $sigma $fuel) $r))))))))

(= (mk:pmatch-struct $p $t $sigma $fuel)
   (case ($p $t)
     ((((P $T1 $B1) (P $T2 $B2)) (mk:pmatch-both $T1 $T2 $B1 $B2 $sigma $fuel))
      (((L $T1 $B1) (L $T2 $B2)) (mk:pmatch-both $T1 $T2 $B1 $B2 $sigma $fuel))
      (((A $f1 $a1) (A $f2 $a2))
       (let* ((($h1 $as1) (mk:spine $p ())) (($h2 $as2) (mk:spine $t ())))
         (if (and (== $h1 $h2) (== (size-atom $as1) (size-atom $as2)))
             (mk:pmatch-args $as1 $as2 $sigma $fuel)
             (Bad (heads differ)))))
      ($other (Bad (no match))))))

(= (mk:pmatch-both $a1 $a2 $b1 $b2 $sigma $fuel)
   (let $s (mk:pmatch $a1 $a2 $sigma $fuel)
     (if (mk:bad? $s) $s (mk:pmatch $b1 $b2 $s $fuel))))

(= (mk:pmatch-args $as $bs $sigma $fuel)
   (if (== $as ()) $sigma
     (let $s (mk:pmatch (car-atom $as) (car-atom $bs) $sigma $fuel)
       (if (mk:bad? $s) $s (mk:pmatch-args (cdr-atom $as) (cdr-atom $bs) $s $fuel)))))

(= (mk:pmatch-delta $p $t $sigma $fuel)
   (if (<= $fuel 0) (Bad (no match))
     (let* (($x (mk:whnf-core $p)) ($y (mk:whnf-core $t)) ($hx (mk:height $x)) ($hy (mk:height $y)))
       (if (and (>= $hx 0) (>= $hx $hy)) (mk:pmatch (mk:unfold $x) $y $sigma (- $fuel 1))
         (if (>= $hy 0) (mk:pmatch $x (mk:unfold $y) $sigma (- $fuel 1))
           (if (and (== $x $p) (== $y $t)) (Bad (no match))
             (mk:pmatch $x $y $sigma (- $fuel 1))))))))

;; ---------------------------------------------------------------- elaboration

;; A name entry is a name, (Moved name age) for a hypothesis rewritten in
;; place (shown at its old position, as Lean keeps it), or (Hidden entry).
(= (mk:entry-name $e) (case $e (((Moved $x $a) $x) ((Hidden $h) (Hidden)) ($o $e))))

(= (mk:index-of $n $names $i)
   (if (== $names ()) -1
     (if (== (mk:entry-name (car-atom $names)) $n) $i (mk:index-of $n (cdr-atom $names) (+ $i 1)))))

;; Position from the oldest hypothesis, kept by a hypothesis rewritten in place.
(= (mk:age-at $i $names)
   (case (mk:nth $i $names)
     (((Moved $x $a) $a)
      ($o (- (- (size-atom $names) 1) $i)))))

;; A name: a hypothesis (newest of that name) or a library constant.
(= (mk:ref $ctx $names $n)
   (let $i (mk:index-of $n $names 0)
     (if (>= $i 0) ((V $i) (mk:shift (+ $i 1) 0 (mk:nth $i $ctx)))
       (let $T (mk:const-type $n) (if (mk:bad? $T) $T ((C $n) $T))))))

;; (mk:elab ctx names e sigma k): (term type sigma k), k the next metavariable.
(= (mk:elab $ctx $names $e $sigma $k)
   (case (get-metatype $e)
     ((Symbol (let $r (mk:ref $ctx $names $e) (if (mk:bad? $r) $r (let ($t $T) $r ($t $T $sigma $k)))))
      ($other
       (let $h (mk:elab $ctx $names (car-atom $e) $sigma $k)
         (if (mk:bad? $h) $h
           (mk:elab-args $ctx $names $h (cdr-atom $e))))))))

(= (mk:elab-args $ctx $names $acc $args)
   (if (== $args ()) $acc
     (let ($f $F $sigma $k) $acc
       (case (mk:whnf (mk:resolve $sigma $F))
         (((P $T $B)
           (let $a (car-atom $args)
             (if (== $a _)
                 (mk:elab-args $ctx $names ((A $f (M $k 0)) (mk:inst-m1 $B (M $k 0)) $sigma (+ $k 1)) (cdr-atom $args))
                 (let $r (mk:elab $ctx $names $a $sigma $k)
                   (if (mk:bad? $r) $r
                     (let ($t $U $s1 $k1) $r
                       (let $s2 (mk:pmatch $T $U $s1 8)
                         (if (mk:bad? $s2) (Bad (argument $a does not fit))
                           (mk:elab-args $ctx $names ((A $f $t) (mk:inst-m1 $B $t) $s2 $k1) (cdr-atom $args))))))))))
          ($o (Bad (too many arguments))))))))

;; ------------------------------------------------------------------- tactics

(= (mk:step (G $ctx $names $T) $tac)
   (case $tac
     (((Intro $x)
       (case (mk:whnf $T)
         (((P $A $B) (Ok ((G (cons-atom $A $ctx) (cons-atom $x $names) $B)) (L $A (Hole 0))))
          ($o (Bad (nothing to introduce))))))
      ((Have $f $e)
       (let $r (mk:elab $ctx $names $e () 0)
         (if (mk:bad? $r) $r
           (let ($t $U $sigma $k) $r
             (let* (($t2 (mk:resolve $sigma $t)) ($U2 (mk:resolve $sigma $U)))
               (if (or (mk:has-m $t2) (mk:has-m $U2)) (Bad (Have $f: argument not determined))
                 (Ok ((G (cons-atom $U2 $ctx) (cons-atom $f $names) (mk:shift 1 0 $T)))
                     (A (L $U2 (Hole 0)) $t2))))))))
      ((Apply $e)
       (let $r (mk:elab $ctx $names $e () 0)
         (if (mk:bad? $r) $r
           (let ($t $U $sigma $k) $r (mk:apply-tele $T $t $U $sigma $k () 0 12)))))
      ((Rewrite $e $at) (mk:rewrite $ctx $names $T $e $at))
      ($other (Bad (unknown tactic $other))))))

;; Apply: try to match the type against the target; if it does not match,
;; take one more premise: a ∀ gets a metavariable, an → becomes a subgoal.
(= (mk:apply-tele $T $t $U $sigma $k $goals $n $fuel)
   (let $s (mk:pmatch $U $T $sigma 8)
     (if (not (mk:bad? $s)) (mk:apply-done $t $s $goals)
       (if (<= $fuel 0) (Bad (apply: does not fit the goal))
         (case (mk:whnf (mk:resolve $sigma $U))
           (((P $A $B)
             (if (mk:free-from $B 1 0)
                 ;; B does not use the bound variable: a premise, proved later
                 (mk:apply-tele $T (A $t (Hole $n)) (mk:shift -1 0 $B) $sigma $k
                             (union-atom $goals ($A)) (+ $n 1) (- $fuel 1))
                 (mk:apply-tele $T (A $t (M $k 0)) (mk:inst-m1 $B (M $k 0)) $sigma (+ $k 1)
                             $goals $n (- $fuel 1))))
            ($o (Bad (apply: does not fit the goal)))))))))

(= (mk:apply-done $t $sigma $goals)
   (let* (($t2 (mk:resolve $sigma $t))
          ($gs (map-atom $goals $g (mk:resolve $sigma $g))))
     (if (or (mk:has-m $t2) (not (== (filter-atom $gs $g (mk:has-m $g)) ()))) (Bad (apply: argument not determined))
       ($t2 $gs))))

;; The goals of Apply live in the goal's own context.
(= (mk:with-ctx $ctx $names $types) (map-atom $types $T (G $ctx $names $T)))

;; Rewrite with e : eq A x y (after its premises): find x in the hypothesis
;; (or target), turn x into y, and keep e's premises as later subgoals.
;; Megalodon's eq A x y is ∀Q. Q x y → Q y x, so with Q a b := P a,
;; e Q (h : P x) : P y.  At the target, Q a b := P b turns a proof of P y
;; into one of P x.
(= (mk:rewrite $ctx $names $T $e $at)
   (let $r (mk:elab $ctx $names $e () 0)
     (if (mk:bad? $r) $r
       (let ($t $U $sigma $k) $r (mk:rewrite-tele $ctx $names $T $at $t $U $sigma $k () 0 12)))))

(= (mk:rewrite-tele $ctx $names $T $at $t $U $sigma $k $sides $n $fuel)
   (let $V (mk:whnf-core (mk:resolve $sigma $U))
     (case (mk:spine $V ())
       ((((C eq) ($Ty $x $y)) (mk:rewrite-at $ctx $names $T $at $t $Ty $x $y $sigma $sides))
        ($o (if (<= $fuel 0) (Bad (rewrite: not an equation))
              (case (mk:whnf $V)
                (((P $A $B)
                  (if (mk:free-from $B 1 0)
                      (mk:rewrite-tele $ctx $names $T $at (A $t (Hole $n)) (mk:shift -1 0 $B) $sigma $k
                                    (union-atom $sides ($A)) (+ $n 1) (- $fuel 1))
                      (mk:rewrite-tele $ctx $names $T $at (A $t (M $k 0)) (mk:inst-m1 $B (M $k 0)) $sigma (+ $k 1)
                                    $sides $n (- $fuel 1))))
                 ($o2 (Bad (rewrite: not an equation)))))))))))

(= (mk:rewrite-at $ctx $names $T $at $t $Ty $x $y $sigma $sides)
   (let* (($i (if (== $at goal) -1 (mk:index-of $at $names 0)))
          ($H (if (== $at goal) $T (mk:shift (+ $i 1) 0 (mk:nth $i $ctx))))
          ($s (mk:find-instance $x $H $sigma 0)))
     (if (mk:bad? $s) (Bad (rewrite: $at has no instance of the left side))
       (let* (($t2 (mk:resolve $s $t)) ($Ty2 (mk:resolve $s $Ty)) ($x2 (mk:resolve $s $x)) ($y2 (mk:resolve $s $y))
              ($gs (map-atom $sides $g (mk:resolve $s $g))))
         (if (or (mk:has-m $t2) (not (== (filter-atom $gs $g (mk:has-m $g)) ()))) (Bad (rewrite: argument not determined))
           (let $Hy (mk:replace $H $x2 $y2 0)
             (if (== $at goal)
                 ;; target P x from a proof of P y, Q a b := P b: hole 0 is P y
                 (let $Q (L $Ty2 (L (mk:shift 1 0 $Ty2) (mk:abstract (mk:shift 2 0 $H) (mk:shift 2 0 $x2) 0 0)))
                   (Ok (cons-atom (G $ctx $names $Hy) (mk:shift-holes $gs $ctx $names))
                       (A (A (mk:shift-hole-term $t2) $Q) (Hole 0))))
                 ;; hypothesis h : P x becomes h : P y (a new, newer h)
                 (let $Q (L $Ty2 (L (mk:shift 1 0 $Ty2) (mk:abstract (mk:shift 2 0 $H) (mk:shift 2 0 $x2) 0 1)))
                   (Ok (cons-atom (G (cons-atom $Hy $ctx) (cons-atom (Moved $at (mk:age-at $i $names)) (mk:hide-at $i $names)) (mk:shift 1 0 $T))
                                  (mk:shift-holes $gs $ctx $names))
                       (A (L $Hy (Hole 0)) (A (A (mk:shift-hole-term $t2) $Q) (V $i))))))))))))

;; The equation's own premise holes are numbered from 0; the main goal takes
;; hole 0, so they move up by one.
(= (mk:shift-hole-term $t)
   (case $t
     (((Hole $i) (Hole (+ $i 1)))
      ((A $f $a) (A (mk:shift-hole-term $f) (mk:shift-hole-term $a)))
      ($other $t))))
(= (mk:shift-holes $gs $ctx $names) (mk:with-ctx $ctx $names $gs))

;; First subterm of H (in order) that x matches; returns sigma or Bad.
(= (mk:find-instance $x $H $sigma $c)
   (let $s (if (mk:free-from $H $c 0) (mk:pmatch $x (mk:shift (- 0 $c) 0 $H) $sigma 0) (Bad (bound)))
     (if (not (mk:bad? $s)) $s
       (case $H
         (((A $f $a) (let $s1 (mk:find-instance $x $f $sigma $c)
                       (if (mk:bad? $s1) (mk:find-instance $x $a $sigma $c) $s1)))
          ((P $T $b) (let $s1 (mk:find-instance $x $T $sigma $c)
                       (if (mk:bad? $s1) (mk:find-instance $x $b $sigma (+ $c 1)) $s1)))
          ((L $T $b) (let $s1 (mk:find-instance $x $T $sigma $c)
                       (if (mk:bad? $s1) (mk:find-instance $x $b $sigma (+ $c 1)) $s1)))
          ($o (Bad (none))))))))

;; H with x (seen under c binders) replaced by y.
(= (mk:replace $H $x $y $c)
   (if (== $H (mk:shift $c 0 $x)) (mk:shift $c 0 $y)
     (case $H
       (((A $f $a) (A (mk:replace $f $x $y $c) (mk:replace $a $x $y $c)))
        ((P $T $b) (P (mk:replace $T $x $y $c) (mk:replace $b $x $y (+ $c 1))))
        ((L $T $b) (L (mk:replace $T $x $y $c) (mk:replace $b $x $y (+ $c 1))))
        ($o $H)))))

;; H (already under the two binders a b) with x replaced by a (which = 1) or
;; b (which = 0), seen under c more binders.
(= (mk:abstract $H $x $c $which)
   (if (== $H (mk:shift $c 0 $x)) (V (+ $c $which))
     (case $H
       (((A $f $a) (A (mk:abstract $f $x $c $which) (mk:abstract $a $x $c $which)))
        ((P $T $b) (P (mk:abstract $T $x $c $which) (mk:abstract $b $x (+ $c 1) $which)))
        ((L $T $b) (L (mk:abstract $T $x $c $which) (mk:abstract $b $x (+ $c 1) $which)))
        ($o $H)))))

;; Apply's result as a step.
(= (mk:step-apply $ctx $names $r)
   (if (mk:bad? $r) $r (let ($t $gs) $r (Ok (mk:with-ctx $ctx $names $gs) $t))))

;; ---------------------------------------------------------------- scripts

;; (mk:prove goal script): (term rest-of-script) or Bad.  The first goal is
;; worked on first, as in Lean.
(= (mk:prove $goal $script)
   (if (== $script ()) (Bad (unsolved goal $goal))
     (let* (($tac (car-atom $script)) ($rest (cdr-atom $script)))
       (case $tac
         (((Witness $w)
           (mk:prove $goal (union-atom (mk:witness-steps $w q hq) $rest)))
          ((Witness $w $k)
           (mk:prove $goal (union-atom (mk:witness-steps $w (mk:sym q $k) (mk:sym hq $k)) $rest)))
          ($o
           (let $r (mk:run-step $goal $tac)
             (if (mk:bad? $r) (Bad (at $tac $r (mk:goal-text $goal)))
               (let (Ok $subgoals $template) $r
                 (let $pr (mk:prove-all $subgoals $rest ())
                   (if (mk:bad? $pr) $pr
                     (let ($proofs $rest2) $pr ((mk:fill $template $proofs) $rest2)))))))))))))

(= (mk:run-step (G $ctx $names $T) $tac)
   (case $tac
     (((Apply $e) (mk:step-apply $ctx $names (mk:step (G $ctx $names $T) $tac)))
      ;; Unpack h: apply h (∃ or ∧ elimination), then h is hidden, as Lean's
      ;; `apply h; try clear h` removes it
      ((Unpack $h)
       (let $r (mk:step-apply $ctx $names (mk:step (G $ctx $names $T) (Apply $h)))
         (if (mk:bad? $r) $r
           (let (Ok $gs $tmpl) $r
             (Ok (map-atom $gs $g (let (G $c $ns $U) $g (G $c (mk:hide-name $h $ns) $U))) $tmpl)))))
      ((Unfold $c) (mk:unfold-step $ctx $names $T $c))
      ((Rewrite $e $at $k) (mk:step (G $ctx $names $T) (Rewrite $e $at)))
      ($o (mk:step (G $ctx $names $T) $tac)))))

;; The three steps of a witness: assume Q and h : ∀x. P x → Q, then h w.
(= (mk:witness-steps $w $q $hq) ((Intro $q) (Intro $hq) (Apply ($hq $w))))
(= (mk:sym $prefix $k)
   (str:string->symbol (str:concat (str:symbol->string $prefix) (str:number->string $k))))

;; A hidden hypothesis keeps its place (de Bruijn indices do not move) but
;; can no longer be named, and observations leave it out.
(= (mk:hide-at $i $names)
   (if (== $i 0) (cons-atom (Hidden (car-atom $names)) (cdr-atom $names))
     (cons-atom (car-atom $names) (mk:hide-at (- $i 1) (cdr-atom $names)))))
(= (mk:hide-name $n $names)
   (let $i (mk:index-of $n $names 0) (if (< $i 0) $names (mk:hide-at $i $names))))

;; Unfold c everywhere (goal and hypotheses), β-reducing where it applied.
;; Only types change, by definitional equality, so the proof term is the
;; subgoal's own: the kernel compares types up to unfolding.
(= (mk:unfold-step $ctx $names $T $c)
   (case (mk:def-of $c)
     (((($b $h))
       (let* (($T2 (mk:unfold-c $c $b $T)) ($ctx2 (map-atom $ctx $U (mk:unfold-c $c $b $U))))
         (if (and (== $T2 $T) (== $ctx2 $ctx)) (Bad (unfold: $c does not occur))
           (Ok ((G $ctx2 $names $T2)) (Hole 0)))))
      ($o (Bad (unfold: $c is not a definition))))))

(= (mk:unfold-c $c $body $t)
   (case $t
     (((C $n) (if (== $n $c) $body $t))
      ((A $f $a) (mk:whnf-core (A (mk:unfold-c $c $body $f) (mk:unfold-c $c $body $a))))
      ((L $T $b) (L (mk:unfold-c $c $body $T) (mk:unfold-c $c $body $b)))
      ((P $T $b) (P (mk:unfold-c $c $body $T) (mk:unfold-c $c $body $b)))
      ($o $t))))

(= (mk:prove-all $goals $script $proofs)
   (if (== $goals ()) ($proofs $script)
     (let $r (mk:prove (car-atom $goals) $script)
       (if (mk:bad? $r) $r
         (let ($p $rest) $r
           (mk:prove-all (cdr-atom $goals) $rest (union-atom $proofs ($p))))))))

(= (mk:fill $t $proofs)
   (case $t
     (((Hole $i) (mk:nth $i $proofs))
      ((A $f $a) (A (mk:fill $f $proofs) (mk:fill $a $proofs)))
      ((L $T $b) (L $T (mk:fill $b $proofs)))
      ($other $t))))

;; ------------------------------------------------------------ β normal form

;; β everywhere (no unfolding): how goals and hypotheses are shown.
(= (mk:beta-nf $t)
   (case $t
     (((A $f $a)
       (let* (($g (mk:beta-nf $f)) ($b (mk:beta-nf $a)))
         (case $g (((L $T $body) (mk:beta-nf (mk:inst $body $b))) ($o (A $g $b))))))
      ((L $T $b) (L (mk:beta-nf $T) (mk:beta-nf $b)))
      ((P $T $b) (P (mk:beta-nf $T) (mk:beta-nf $b)))
      ($o $t))))

;; ------------------------------------------------------------ named form

;; A goal as text for messages: the hypotheses with their names, then ⊢ T.
(= (mk:goal-text (G $ctx $names $T))
   (let $d (size-atom $ctx)
     ((mk:hyps-text (mk:cdr-atom-n $ctx 0) $names $d) ⊢ (mk:named $T $d))))
(= (mk:cdr-atom-n $x $n) $x)
(= (mk:hyps-text $ctx $names $d)
   (if (== $ctx ()) ()
     (cons-atom ((car-atom $names) : (mk:named (car-atom $ctx) (- $d 1)))
                (mk:hyps-text (cdr-atom $ctx) (cdr-atom $names) (- $d 1)))))

;; Back to the export's notation: a binder at depth d is _bd.
(= (mk:bname $d) (str:string->symbol (str:concat "_b" (str:number->string $d))))

(= (mk:named $t $d)
   (case $t
     (((V $i) (mk:bname (- (- $d 1) $i)))
      ((C $n) $n)
      ((S 0) Prop)
      ((S 1) meg_Type)
      ((L $T $b) (λ ((mk:bname $d) (mk:named $T $d)) (mk:named $b (+ $d 1))))
      ((P $T $b) (if (mk:free-from $b 1 0)
                     (→ (mk:named $T $d) (mk:named $b (+ $d 1)))
                     (∀ ((mk:bname $d) (mk:named $T $d)) (mk:named $b (+ $d 1)))))
      ((A $f $a) (let ($h $as) (mk:spine $t ())
                   (cons-atom (mk:named $h $d) (map-atom $as $x (mk:named $x $d)))))
      ($other $other))))

;; ------------------------------------------------------- loading the library

;; The library's types and definitions up to (not including) index n, taken
;; as checked: check.metta checks them all, in order, on its own.
(= (mk:load-kb $n)
   (let $recs (collapse (match &lib (MkIndexed $i $r) ($i $r)))
     (size-atom (filter-atom (map-atom $recs $x (let ($i $r) $x (if (< $i $n) (mk:load-rec $i $r) skip)))
                             $y (== $y done)))))

(= (mk:load-rec $i $rec)
   (case $rec
     (((MkAxiom $n $T) (let $t (mk:db $T 0) (let $_ (add-atom &kb (Ty $n $t)) done)))
      ((MkDefinition $n $V $T)
       (let* (($t (mk:db $T 0)) ($v (mk:db $V 0))
              ($_ (add-atom &kb (Ty $n $t))) ($_2 (add-atom &kb (Df $n $v $i)))) done))
      ((MkTheorem $n $Pf $T) (let $t (mk:db $T 0) (let $_ (add-atom &kb (Ty $n $t)) done))))))

;; Prove a goal with a script and check the proof with the kernel.
;; Returns (Proved (: proof statement)) or (Failed reason).
(= (mk:prove-and-check $T $script)
   (let $r (mk:prove (G () () $T) $script)
     (if (mk:bad? $r) (Failed $r)
       (let ($term $rest) $r
         (if (not (== $rest ())) (Failed (script continues after the proof $rest))
           (let $u (mk:infer () $term)
             (if (mk:bad? $u) (Failed (kernel rejects the proof $u))
               (if (mk:conv $u $T) (Proved (: (mk:named $term 0) (mk:named $T 0)))
                 (Failed (kernel: proof proves something else))))))))))
