;; The operations controller.metta calls, in MeTTa: the CeTTa port of the Host
;; class in ../prove.py. Lean is reached through lean.metta; the long-term
;; memory, statements and argument patterns are atoms of data/library.metta.
;;
;; Run state lives in &self: (P2 <key> <value>) for the current theorem, and
;; (P2Seen <state> <observation>), (P2Parent <state> <parent>),
;; (P2Trace <k> <state> <tactic> <ok> <ms>) per step.

(= (p2:heartbeats) 100000)
(= (p2:top-lemmas) 8)
(= (p2:premises) 8)
(= (p2:bridge) "b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex")
(= (p2:objects) (set Prop meg_Type))

;; ---------------------------------------------------------------- run state

(= (p2:get $k) (match &self (P2 $k $v) $v))
(= (p2:set $k $v)
   (let $old (collapse (match &self (P2 $k $x) (P2 $k $x)))
     (let $gone (map-atom $old $a (remove-atom &self $a))
       (add-atom &self (P2 $k $v)))))
(= (p2:bump $k)
   (let $n (+ (p2:get $k) 1) (let $s (p2:set $k $n) $n)))
(= (p2:now-ms) (/ (system:monotonic-ns) 1000000))
(= (p2:over-budget)
   (or (>= (p2:get steps) (p2:get budget)) (> (p2:now-ms) (p2:get deadline))))
(= (p2:abort $why)
   (if (== (p2:get aborted) none) (p2:set aborted $why) done))

;; ---------------------------------------------------------------- names

(= (p2:text $x) (if (== (get-metatype $x) Symbol) (str:symbol->string $x) (repr $x)))
(= (p2:from-metta $sym)
   (let $s (str:symbol->string $sym)
     (if (str:starts-with $s "meg_") (str:byte-slice $s 4 (str:byte-length $s)) $s)))
(= (p2:lean-name $s) (str:join "" ("Megalodon.«" $s "»")))
(= (p2:library? $sym) (not (== (collapse (match &self (Index $sym $i) $i)) ())))
(= (p2:fact? $name) (not (== (collapse (match &self (Binders $name $b) $b)) ())))
(= (p2:binders $name) (match &self (Binders $name $b) $b))

;; ---------------------------------------------------------------- lists

(= (p2:member $x $xs)
   (if (== $xs ()) false (if (== (car-atom $xs) $x) true (p2:member $x (cdr-atom $xs)))))
(= (p2:take $xs $n)
   (if (or (== $xs ()) (<= $n 0)) ()
     (cons-atom (car-atom $xs) (p2:take (cdr-atom $xs) (- $n 1)))))
(= (p2:dedup $xs $seen)
   (if (== $xs ()) ()
     (let* (($h (car-atom $xs)) ($t (cdr-atom $xs)))
       (if (p2:member $h $seen) (p2:dedup $t $seen)
         (cons-atom $h (p2:dedup $t (cons-atom $h $seen)))))))
;; names (strings) in ranking order, then the rest sorted
(= (p2:ranked $names)
   (let* (($rank (p2:get ranking))
          ($first (filter-atom $rank $n (p2:member $n $names)))
          ($rest (sort-atom (filter-atom $names $n (not (p2:member $n $rank))))))
     (union-atom $first $rest)))

;; ---------------------------------------------------------------- terms

;; Rename bound variables by depth from the root of t, as ltm.canon does;
;; $ren maps names (old new).
(= (p2:lookup $s $ren)
   (if (== $ren ()) $s
     (let ($old $new) (car-atom $ren)
       (if (== $old $s) $new (p2:lookup $s (cdr-atom $ren))))))
(= (p2:bound $d) (str:string->symbol (str:concat "_b" (str:number->string $d))))
(= (p2:canon $t $d $ren)
   (case (get-metatype $t)
     ((Symbol (p2:lookup $t $ren))
      (Expression
       (case $t
         (((∀ ($v $ty) $b)
           (let $n (p2:bound $d)
             (∀ ($n (p2:canon $ty $d $ren)) (p2:canon $b (+ $d 1) (cons-atom ($v $n) $ren)))))
          ((λ ($v $ty) $b)
           (let $n (p2:bound $d)
             (λ ($n (p2:canon $ty $d $ren)) (p2:canon $b (+ $d 1) (cons-atom ($v $n) $ren)))))
          ((→ $a $b) (→ (p2:canon $a $d $ren) (p2:canon $b (+ $d 1) $ren)))
          ($o (map-atom $t $x (p2:canon $x $d $ren))))))
      ($other $t))))

;; Does term $t mention symbol $s? Stops at the first occurrence.
(= (p2:mentions $s $t)
   (case (get-metatype $t)
     ((Symbol (== $s $t))
      (Expression (p2:any-mentions $s $t))
      ($other false))))
(= (p2:any-mentions $s $xs)
   (if (== $xs ()) false
     (if (p2:mentions $s (car-atom $xs)) true (p2:any-mentions $s (cdr-atom $xs)))))

(= (p2:symbols $t)
   (case (get-metatype $t)
     ((Symbol ($t))
      (Expression (foldl-atom $t () $acc $x (union-atom $acc (p2:symbols $x))))
      ($other ()))))

;; Peel leading ∀ and →: (Split (vars) (hyps) conclusion).
(= (p2:split $t $vs $hs)
   (case $t
     (((∀ ($v $ty) $b) (p2:split $b (union-atom $vs ($v)) $hs))
      ((→ $a $b) (p2:split $b $vs (union-atom $hs ($a))))
      ($other (Split $vs $hs $t)))))

;; ---------------------------------------------------------------- tactics

;; Tactics are MeTTa atoms (../metta/tactics.metta runs them).  For the Lean
;; backend each is rendered to the Lean text the prover has always sent:
;;   (Intro x5)                 intro x5
;;   (Apply L) / (Apply h)      apply Megalodon.«L» / apply h
;;   (Unpack h)                 (apply h; try clear h)
;;   (Witness o k)              (intro qk hqk; apply hqk o)
;;   (Have fk (L a ...))        have fk := @Megalodon.«L» a ...
;;   (Rewrite L h k)            (have ek := @Megalodon.«L»; simp only [b_eq] at ek; rw [ek] at h)
;;   (RewriteRev L h k)         the same with rw [← ek]
;;   (Witness (f a ...) k)      a witness term: Megalodon names, applications in parentheses
;;   (Unfold c)                 unfold Megalodon.«c» at *
;;   (IffRefine rule L bs)      refine Megalodon.«rule» _ _ (@Megalodon.«L» bs ...) ?_
;;   (Closer text)              text (grind: no MeTTa tactic)
(= (p2:render $t)
   (case $t
     (((Intro $x) (str:concat "intro " (p2:text $x)))
      ((Apply $n) (if (p2:library? $n)
                      (str:concat "apply " (p2:lean-name (str:symbol->string $n)))
                      (str:concat "apply " (p2:text $n))))
      ((Unpack $n) (str:join "" ("(apply " (p2:text $n) "; try clear " (p2:text $n) ")")))
      ((Witness $n $k)
       (let $ks (str:number->string $k)
         (str:join "" ("(intro q" $ks " hq" $ks "; apply hq" $ks " " (p2:lean-term $n) ")"))))
      ((Have $f $e)
       (str:join "" ("have " (p2:text $f) " := @" (p2:lean-name (str:symbol->string (car-atom $e))) " "
                     (str:join " " (map-atom (cdr-atom $e) $a (p2:text $a))))))
      ((Rewrite $n $where $k)
       (let* (($e (str:concat "e" (str:number->string $k)))
              ($at (if (== $where goal) "" (str:concat " at " (p2:text $where)))))
         (str:join "" ("(have " $e " := @" (p2:lean-name (str:symbol->string $n)) "; simp only [b_eq] at " $e
                       "; rw [" $e "]" $at ")"))))
      ((RewriteRev $n2 $where2 $k2)
       (let* (($e2 (str:concat "e" (str:number->string $k2)))
              ($at2 (if (== $where2 goal) "" (str:concat " at " (p2:text $where2)))))
         (str:join "" ("(have " $e2 " := @" (p2:lean-name (str:symbol->string $n2)) "; simp only [b_eq] at " $e2
                       "; rw [← " $e2 "]" $at2 ")"))))
      ((Unfold $c) (str:join "" ("unfold " (p2:lean-name (p2:from-metta $c)) " at *")))
      ((IffRefine $rule $n $bs)
       (str:join "" ("refine " (p2:lean-name (str:symbol->string $rule)) " _ _ (@"
                     (p2:lean-name (str:symbol->string $n)) " "
                     (str:join " " (map-atom $bs $b (str:symbol->string $b))) ") ?_")))
      ((Closer $text) $text)
      ($o (repr $t)))))

;; A MeTTa term as Lean text: names as Lean knows them (meg_ dropped).
(= (p2:lean-term $t)
   (case (get-metatype $t)
     ((Symbol (p2:from-metta $t))
      (Expression (str:join "" ("(" (str:join " " (map-atom $t $u (p2:lean-term $u))) ")")))
      ($other (repr $t)))))

;; ---------------------------------------------------------------- Lean state

;; Process handles cannot be removed from a space, so each theorem's Lean is
;; kept under the theorem's index and never replaced.
(= (p2:lean) (let $i (p2:get target) (match &self (P2Lean $i $l) $l)))

(= (p2:read-obs $st)
   (if (== (p2:get backend) metta) (mt:observe $st) (p2:read-obs-lean $st)))

(= (p2:read-obs-lean $st)
   (let* (((Lean $p $env) (p2:lean))
          ($r (lean:send $p (JsonObject ((JsonPair "tactic" "goal_sexpr") (JsonPair "proofState" $st)))))
          ($infos (filter-atom (json:items (json:get $r "messages")) $m
                    (str:starts-with (json:get $m "data") "GOAL "))))
     (if (== $infos ()) NoGoal
       (let* (($lines (str:split "\n" (json:get (car-atom $infos) "data")))
              ($goal (parse-first (str:byte-slice (car-atom $lines) 5 (str:byte-length (car-atom $lines)))))
              ($hyps (map-atom (cdr-atom $lines) $l
                       (let (HYP $n $t) (parse-first (str:join "" ("(" $l ")"))) ($n $t)))))
         (Obs $goal $hyps)))))

(= (p2:seen $st) (match &self (P2Seen $st $o) $o))

(= (p2:types (Obs $g $hyps)) (map-atom $hyps $h (let ($n $t) $h $t)))
(= (p2:facts-of $obs) (filter-atom (p2:types $obs) $t (not (p2:member $t (p2:objects)))))

;; The same goal and hypotheses earlier on this path.
(= (p2:repeats $st $key)
   (case (collapse (match &self (P2Parent $st $p) $p))
     ((() false)
      (($p) (case (collapse (p2:seen $p))
              ((((Obs $g $hs)) (if (== ($g (p2:types (Obs $g $hs))) $key) true (p2:repeats $p $key)))
               ($other (p2:repeats $p $key))))))))

(= (lean-observe $st)
   (if (not (== (p2:get aborted) none)) Loop
     (let* (($obs (p2:read-obs $st))
            ($saved (add-atom &self (P2Seen $st $obs))))
       (case $obs
         ((NoGoal Done)
          ((Obs $g $hyps)
           (if (p2:over-budget)
               (let $a (p2:abort budget) Loop)
               (let $facts (p2:facts-of $obs)
                 (if (< (size-atom (unique-atom $facts)) (size-atom $facts))
                     (let $m (p2:mark-dead $st) Loop) ; a fact derived twice
                     (if (p2:repeats $st ($g (p2:types $obs)))
                         Loop
                         (Goal $g)))))))))))

(= (lean-try $st $tac)
   (if (or (not (== (p2:get aborted) none)) (p2:over-budget))
       (let $a (p2:abort budget) Fail)
       (if (== (p2:get backend) metta) (p2:metta-try $st $tac)
       (let* (($k (p2:bump steps))
              ((Lean $p $env) (p2:lean))
              ($t0 (p2:now-ms))
              ($r (lean:send $p (JsonObject ((JsonPair "tactic" (p2:render $tac)) (JsonPair "proofState" $st)))))
              ($ms (- (p2:now-ms) $t0)))
         (if (== $r LeanTimeout)
             (let* (($a (p2:abort "lean timeout")) ($t (add-atom &self (P2Trace $k $st $tac false $ms)))) Fail)
             (let $ok (p2:step-ok $r)
               (let $t (add-atom &self (P2Trace $k $st $tac $ok $ms))
                 (if $ok
                     (let* (($n (json:get $r "proofState")) ($s (add-atom &self (P2Parent $n $st)))
                            ($v (add-atom &self (P2Via $n $tac))) ($u (p2:record-applied $n $st $tac))) $n)
                     Fail))))))))

;; The same step on the MeTTa backend (mettahost.metta): no Lean.
(= (p2:metta-try $st $tac)
   (let* (($k (p2:bump steps))
          ($t0 (p2:now-ms))
          ($n (mt:try $st $tac))
          ($ms (- (p2:now-ms) $t0))
          ($ok (not (== $n Fail)))
          ($t (add-atom &self (P2Trace $k $st $tac $ok $ms))))
     (if $ok
         (let* (($s (add-atom &self (P2Parent $n $st))) ($v (add-atom &self (P2Via $n $tac)))
                ($u (p2:record-applied $n $st $tac))) $n)
         Fail)))

(= (p2:step-ok $r)
   (let $ms (json:items (json:get $r "messages"))
     (and (not (== (get-type (json:get $r "message")) String))
          (== (filter-atom $ms $m (or (== (json:get $m "severity") "error")
                                      (str:starts-with (json:get $m "data") "declaration uses 'sorry'")))
              ()))))

;; ---------------------------------------------------------------- operations

(= (lean-hyps $st)
   (let (Obs $g $hyps) (p2:seen $st)
     (let $text (str:join " " (p2:hyp-atoms $hyps 0))
       (parse-first (str:join "" ("(" $text ")"))))))

;; One (Hyp name n conclusion) text per usable conclusion of each fact, with
;; the fact's own variables as MeTTa variables $H<i>V<j>.
(= (p2:hyp-atoms $hyps $i)
   (if (== $hyps ()) ()
     (let* ((($n $t) (car-atom $hyps))
            ($rest (p2:hyp-atoms (cdr-atom $hyps) (+ $i 1))))
       (if (p2:member $t (p2:objects)) $rest
         (union-atom (p2:hyp-texts $n $t $i) $rest)))))

(= (p2:hyp-texts $n $t $i)
   (let* (((Split $vs $hs $c) (p2:split $t () ()))
          ($top (p2:var-names $vs $i 0))
          ($tops (map-atom $top $p (let ($o $v) $p $v)))
          ($concl (p2:canon $c 0 $top)))
     (filter-atom
       (map-atom (p2:conclusions $concl (size-atom $hs)) $cn
         (let ($cc $nh) $cn
           (if (and (== (get-metatype $cc) Symbol) (p2:member $cc $tops)) Skip
             (repr (Hyp $n $nh $cc)))))
       $x (not (== $x Skip)))))

(= (p2:var-names $vs $i $j)
   (if (== $vs ()) ()
     (cons-atom ((car-atom $vs)
                 (str:string->symbol (str:join "" ("$H" (str:number->string $i) "V" (str:number->string $j)))))
                (p2:var-names (cdr-atom $vs) $i (+ $j 1)))))

;; A fact concluding (not P) also closes False, with one more hypothesis.
(= (p2:conclusions $c $nh)
   (case $c
     (((meg_not $x) (($c $nh) (meg_False (+ $nh 1))))
      ($other (($c $nh))))))

(= (intro-tactic $st)
   (let* (((Obs $g $hyps) (p2:seen $st)) ($k (p2:bump fresh)))
     (Intro (str:string->symbol (str:concat (case $g (((∀ $v $b) "x") ($o "h"))) (str:number->string $k))))))

(= (closers $st $goal)
   (let* (((Obs $g $hyps) (p2:seen $st))
          ($syms (unique-atom (foldl-atom (cons-atom $g (p2:types (Obs $g $hyps))) () $acc $x
                   (union-atom $acc (p2:symbols $x)))))
          ($defs (sort-atom (p2:dedup (map-atom (filter-atom $syms $s (p2:def? $s)) $s (p2:from-metta $s)) ())))
          ($cap (str:join "" ("set_option maxHeartbeats " (str:number->string (p2:heartbeats)) " in ")))
          ($unfold (str:join "" (map-atom $defs $d (str:concat ", " (p2:lean-name $d)))))
          ($plain (str:join "" ($cap "((try simp only [" (p2:bridge) "] at *) <;> grind)")))
          ($with-defs (if (== $defs ()) ()
                        ((str:join "" ($cap "((try simp only [" (p2:bridge) $unfold "] at *) <;> grind)")))))
          ($hinted (p2:ranked (collapse (match &self (P2Hint $h) (str:symbol->string $h)))))
          ($ranked (p2:take (filter-atom (p2:get ranking) $n (p2:fact? (str:string->symbol $n))) (p2:premises)))
          ($prem (p2:take (p2:dedup (union-atom $hinted $ranked) ()) (p2:premises)))
          ($haves (str:join "; " (p2:haves $prem 0)))
          ($with-prem (if (== $prem ()) ()
                        ((str:join "" ($cap "(" $haves "; (try simp only [" (p2:bridge) $unfold "] at *); grind)"))))))
     (map-atom (cons-atom $plain (union-atom $with-defs $with-prem)) $c (Closer $c))))

(= (p2:def? $s) (not (== (collapse (match &self (Def $s) $s)) ())))
(= (p2:haves $names $k)
   (if (== $names ()) ()
     (cons-atom (str:join "" ("have p" (str:number->string $k) " := @" (p2:lean-name (car-atom $names))))
                (p2:haves (cdr-atom $names) (+ $k 1)))))

(= (apply-tactic $name) (Apply $name))
(= (unpack-tactic $n) (Unpack $n))
(= (witness-tactic $n) (Witness $n (p2:bump fresh)))

;; have f<k> := @L _ h1 _ h2 ... : the binders of L, '?_' filled in order.
;; A hinted lemma with several hypotheses is used forward at most once on a
;; path: a hint says the lemma is used in the proof, and lemmas such as
;; "n m natural -> n*m natural" would otherwise combine every new fact with
;; every other. One-hypothesis lemmas cannot do that, and a fact derived
;; twice already ends a branch.
(= (hint-forward-tactic $st $name $hs)
   (if (or (and (> (size-atom $hs) 1) (p2:path-has $st $name))
           (p2:path-applied-all $st $name $hs))
       (empty)
       (let* (($args (map-atom (p2:fill-binders (p2:binders $name) $hs) $a (str:string->symbol $a)))
              ($k (p2:bump fresh)))
         (Have (p2:fresh-name f $k) (cons-atom $name $args)))))

(= (p2:fresh-name $prefix $k)
   (str:string->symbol (str:concat (str:symbol->string $prefix) (str:number->string $k))))

(= (p2:fill-binders $bs $hs)
   (if (== $bs ()) ()
     (if (== (car-atom $bs) ?_)
         (cons-atom (p2:text (car-atom $hs)) (p2:fill-binders (cdr-atom $bs) (cdr-atom $hs)))
         (cons-atom "_" (p2:fill-binders (cdr-atom $bs) $hs)))))

;; Was (Have f (name ...)) used to reach state $st?
(= (p2:path-has $st $name)
   (case (collapse (match &self (P2Via $st $t) $t))
     ((($t) (if (p2:have-of? $t $name) true
               (case (collapse (match &self (P2Parent $st $p) $p))
                 ((($p) (p2:path-has $p $name)) ($o false)))))
      ($o false))))
(= (p2:have-of? $t $name)
   (case $t (((Have $f $e) (== (car-atom $e) $name)) ($o false))))

;; The lemma applications (have f := L args) on the path to a state, kept
;; with the state when it is made: (P2Applied state ((f L args) ...)).
(= (p2:applied-of $st)
   (case (collapse (match &self (P2Applied $st $l) $l)) ((($l) $l) ($o ()))))
(= (p2:record-applied $n $st $tac)
   (let* (($old (p2:applied-of $st))
          ($new (case $tac (((Have $f $e) (cons-atom (cons-atom $f $e) $old))
                            ((Unpack $h) (cons-atom (Unpacked $h) $old))
                            ($o $old)))))
     (add-atom &self (P2Applied $n $new))))

;; Was hypothesis $h unpacked on the path to $st?
(= (p2:unpacked-on-path $st $h)
   (p2:member (Unpacked $h) (p2:applied-of $st)))

;; State $st re-derived a known fact by (have f := L args): the parent
;; records that application as done, so its later children skip it.
(= (p2:mark-dead $st)
   (case (collapse (match &self (P2Via $st $t) $t))
     ((((Have $f $e))
       (let* (($p (match &self (P2Parent $st $p) $p))
              ($old (p2:applied-of $p))
              ($new (cons-atom (cons-atom $f $e) $old))
              ($rm (map-atom (collapse (match &self (P2Applied $p $l) (P2Applied $p $l)))
                             $x (remove-atom &self $x))))
         (add-atom &self (P2Applied $p $new))))
      ($o done))))

;; Was lemma $name applied to hypothesis $h on the path to $st, or is $h a
;; fact that $name itself produced? The second stops a lemma feeding on its
;; own conclusions (SNo x -> SNo (-x) -> SNo (-(-x)) ...).
(= (p2:path-applied $st $name $h)
   (not (== (filter-atom (p2:applied-of $st) $e
              (and (== (car-atom (cdr-atom $e)) $name)
                   (or (== (car-atom $e) $h) (p2:member $h (cdr-atom (cdr-atom $e))))))
            ())))

;; The same lemma already applied to all of $hs on this path: its conclusion
;; is a known fact.
(= (p2:path-applied-all $st $name $hs)
   (if (== $hs ()) false (p2:all-applied $st $name $hs)))
(= (p2:all-applied $st $name $hs)
   (if (== $hs ()) true
     (if (p2:path-applied $st $name (car-atom $hs))
         (p2:all-applied $st $name (cdr-atom $hs))
         false)))

;; The library's equality is turned into Lean's (b_eq), then used by rw.
(= (rewrite-tactic $name $where) (Rewrite $name $where (p2:bump fresh)))
(= (rewrite-rev-tactic $name $where) (RewriteRev $name $where (p2:bump fresh)))

(= (unfold-tactic $c) (Unfold $c))

(= (rank-lemmas $cands)
   (let* (($names (p2:dedup (map-atom $cands $c (let ($n $k) $c (str:symbol->string $n))) ()))
          ($order (p2:take (p2:ranked $names) (p2:top-lemmas))))
     (map-atom $order $n (str:string->symbol $n))))

(= (iff-tactics $right $left)
   (let* (($dirs (p2:first-dirs (union-atom
                    (map-atom $right $r (let (Right $n) $r ((str:symbol->string $n) "iffEL")))
                    (map-atom $left $l (let (Left $n) $l ((str:symbol->string $n) "iffER")))) ()))
          ($names (map-atom $dirs $d (let ($n $rule) $d $n)))
          ($order (p2:take (p2:ranked $names) (p2:top-lemmas))))
     (map-atom $order $n
       (IffRefine (str:string->symbol (p2:rule-of $n $dirs)) (str:string->symbol $n)
                  (p2:binders (str:string->symbol $n))))))

(= (p2:first-dirs $pairs $seen)
   (if (== $pairs ()) ()
     (let* ((($n $rule) (car-atom $pairs)) ($t (cdr-atom $pairs)))
       (if (p2:member $n $seen) (p2:first-dirs $t $seen)
         (cons-atom ($n $rule) (p2:first-dirs $t (cons-atom $n $seen)))))))
(= (p2:rule-of $n $dirs)
   (let ($m $rule) (car-atom $dirs) (if (== $m $n) $rule (p2:rule-of $n (cdr-atom $dirs)))))

(= (lean-facts $st)
   (let (Obs $g $hyps) (p2:seen $st)
     (filter-atom (map-atom $hyps $h (let ($n $t) $h
                                        (if (p2:member $t (p2:objects)) Skip ($n (p2:canon $t 0 ())))))
                  $x (not (== $x Skip)))))

;; have f<k> := @L _ .. h : the lemma's only hypothesis is h. One h per lemma.
(= (forward-tactics $pairs)
   (let* (($firsts (p2:first-dirs (map-atom $pairs $p (let ($l $h) $p ((str:symbol->string $l) $h))) ()))
          ($names (map-atom $firsts $f (let ($n $h) $f $n)))
          ($order (p2:take (filter-atom (p2:get ranking) $n (p2:member $n $names)) (p2:top-lemmas))))
     (map-atom $order $n
       (let* (($h (p2:rule-of $n $firsts))
              ($k (p2:bump fresh))
              ($args (map-atom (p2:binders (str:string->symbol $n)) $b (if (== $b ?_) $h $b))))
         (Have (p2:fresh-name f $k) (cons-atom (str:string->symbol $n) $args))))))

(= (concat $a $b $c $d $e $f $g)
   (union-atom $a (union-atom $b (union-atom $c (union-atom $d (union-atom $e (union-atom $f $g)))))))

(= (target-index) (p2:get target))
