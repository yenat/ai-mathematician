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

;; ---------------------------------------------------------------- Lean state

;; Process handles cannot be removed from a space, so each theorem's Lean is
;; kept under the theorem's index and never replaced.
(= (p2:lean) (let $i (p2:get target) (match &self (P2Lean $i $l) $l)))

(= (p2:read-obs $st)
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
                 (if (< (size-atom (p2:dedup $facts ())) (size-atom $facts))
                     Loop                            ; a fact derived twice
                     (if (p2:repeats $st ($g (p2:types $obs)))
                         Loop
                         (Goal $g)))))))))))

(= (lean-try $st $tac)
   (if (or (not (== (p2:get aborted) none)) (p2:over-budget))
       (let $a (p2:abort budget) Fail)
       (let* (($k (p2:bump steps))
              ((Lean $p $env) (p2:lean))
              ($t0 (p2:now-ms))
              ($r (lean:send $p (JsonObject ((JsonPair "tactic" $tac) (JsonPair "proofState" $st)))))
              ($ms (- (p2:now-ms) $t0)))
         (if (== $r LeanTimeout)
             (let* (($a (p2:abort "lean timeout")) ($t (add-atom &self (P2Trace $k $st $tac false $ms)))) Fail)
             (let $ok (p2:step-ok $r)
               (let $t (add-atom &self (P2Trace $k $st $tac $ok $ms))
                 (if $ok
                     (let* (($n (json:get $r "proofState")) ($s (add-atom &self (P2Parent $n $st)))) $n)
                     Fail)))))))

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
     (str:concat (case $g (((∀ $v $b) "intro x") ($o "intro h"))) (str:number->string $k))))

(= (closers $st $goal)
   (let* (((Obs $g $hyps) (p2:seen $st))
          ($syms (foldl-atom (cons-atom $g (p2:types (Obs $g $hyps))) () $acc $x
                   (union-atom $acc (p2:symbols $x))))
          ($defs (sort-atom (p2:dedup (map-atom (filter-atom $syms $s (p2:def? $s)) $s (p2:from-metta $s)) ())))
          ($cap (str:join "" ("set_option maxHeartbeats " (str:number->string (p2:heartbeats)) " in ")))
          ($unfold (str:join "" (map-atom $defs $d (str:concat ", " (p2:lean-name $d)))))
          ($plain (str:join "" ($cap "((try simp only [" (p2:bridge) "] at *) <;> grind)")))
          ($with-defs (if (== $defs ()) ()
                        ((str:join "" ($cap "((try simp only [" (p2:bridge) $unfold "] at *) <;> grind)")))))
          ($prem (p2:take (filter-atom (p2:get ranking) $n (p2:fact? (str:string->symbol $n))) (p2:premises)))
          ($haves (str:join "; " (p2:haves $prem 0)))
          ($with-prem (if (== $prem ()) ()
                        ((str:join "" ($cap "(" $haves "; (try simp only [" (p2:bridge) $unfold "] at *); grind)"))))))
     (cons-atom $plain (union-atom $with-defs $with-prem))))

(= (p2:def? $s) (not (== (collapse (match &self (Def $s) $s)) ())))
(= (p2:haves $names $k)
   (if (== $names ()) ()
     (cons-atom (str:join "" ("have p" (str:number->string $k) " := @" (p2:lean-name (car-atom $names))))
                (p2:haves (cdr-atom $names) (+ $k 1)))))

(= (apply-tactic $name)
   (if (p2:library? $name)
       (str:concat "apply " (p2:lean-name (str:symbol->string $name)))
       (str:concat "apply " (p2:text $name))))

(= (unfold-tactic $c) (str:join "" ("unfold " (p2:lean-name (p2:from-metta $c)) " at *")))

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
       (str:join "" ("refine " (p2:lean-name (p2:rule-of $n $dirs)) " _ _ (@" (p2:lean-name $n) " "
                     (str:join " " (map-atom (p2:binders (str:string->symbol $n)) $b (str:symbol->string $b)))
                     ") ?_")))))

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
              ($args (map-atom (p2:binders (str:string->symbol $n)) $b
                       (if (== $b ?_) (p2:text $h) (str:symbol->string $b)))))
         (str:join "" ("have f" (str:number->string $k) " := @" (p2:lean-name $n) " " (str:join " " $args)))))))

(= (concat $a $b $c $d $e $f $g)
   (union-atom $a (union-atom $b (union-atom $c (union-atom $d (union-atom $e (union-atom $f $g)))))))

(= (target-index) (p2:get target))
