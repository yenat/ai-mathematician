;; The prover's proof states in MeTTa, in place of Lean's (lean.metta):
;; tactics are run by ../metta/tactics.metta on goals in de Bruijn form, and
;; the finished script is replayed into one proof term that the MeTTa kernel
;; checks (../metta/kernel.metta).  No Lean.
;;
;;   (mt:start T)        -> state number of the goal T (de Bruijn)
;;   (mt:try st tactic)  -> new state number, or Fail
;;   (mt:observe st)     -> (Obs goal ((name type) ...)) | NoGoal, written as
;;                          Lean's goal_sexpr writes them, so the controller
;;                          reads both alike
;;
;; A state is (MSt n (goal ...)) in &self; the first goal is worked on.

(= (mt:next)
   (let $n (case (collapse (match &self (MtNext $k) $k)) ((($k) $k) ($o 0)))
     (let* (($old (collapse (match &self (MtNext $k) (MtNext $k))))
            ($gone (map-atom $old $a (remove-atom &self $a)))
            ($m (+ $n 1))
            ($new (add-atom &self (MtNext $m))))
       $n)))

(= (mt:store $goals) (let $n (mt:next) (let $_ (add-atom &self (MSt $n $goals)) $n)))

(= (mt:reset)
   (let* (($a (collapse (match &self (MSt $n $g) (MSt $n $g))))
          ($b (map-atom $a $x (remove-atom &self $x)))
          ($c (collapse (match &self (MtNext $k) (MtNext $k))))
          ($d (map-atom $c $x (remove-atom &self $x))))
     done))

(= (mt:start $T) (mt:store ((G () () $T))))

(= (mt:goals $st) (match &self (MSt $st $gs) $gs))

;; A witness is three steps; every other tactic is one.
(= (mt:try $st $tac)
   (let $gs (mt:goals $st)
     (if (== $gs ()) Fail
       (let $r (case $tac (((Witness $w $k) (mt:run-seq $gs (mk:witness-steps $w (mk:sym q $k) (mk:sym hq $k))))
                           ($o (mt:run-one $gs $tac))))
         (if (== $r Fail) Fail (mt:store $r))))))

(= (mt:run-one $gs $tac)
   (let $r (mk:run-step (car-atom $gs) (mt:engine-form $tac))
     (if (mk:bad? $r) Fail
       (let (Ok $sub $tmpl) $r (union-atom $sub (cdr-atom $gs))))))

(= (mt:run-seq $gs $tacs)
   (if (== $tacs ()) $gs
     (let $r (mt:run-one $gs (car-atom $tacs))
       (if (== $r Fail) Fail (mt:run-seq $r (cdr-atom $tacs))))))

;; Tactic atoms carry Lean's fresh numbers for rendering; the engine ignores them.
(= (mt:engine-form $tac)
   (case $tac (((Rewrite $e $at $k) (Rewrite $e $at)) ($o $tac))))

;; ---------------------------------------------------------------- observing

(= (mt:observe $st)
   (let $gs (mt:goals $st)
     (if (== $gs ()) NoGoal
       (let (G $ctx $names $T) (car-atom $gs)
         (Obs (mt:show (mk:beta-nf $T) $names 0) (mt:hyps $ctx $names))))))

;; Oldest first, as Lean lists its local context; hidden ones left out; a
;; hypothesis rewritten in place at its old position (Lean's replaceLocalDecl).
(= (mt:hyps $ctx $names)
   (map-atom (mt:by-age (mt:aged $ctx $names 0)) $r (let ($a $n $t) $r ($n $t))))

(= (mt:aged $ctx $names $i)
   (if (== $ctx ()) ()
     (let* (($rest (mt:aged (cdr-atom $ctx) (cdr-atom $names) (+ $i 1)))
            ($e (car-atom $names)))
       (case $e
         (((Hidden $x) $rest)
          ($o (cons-atom ((mk:age-at 0 $names) (mk:entry-name $e)
                          (mt:show (mk:beta-nf (car-atom $ctx)) (cdr-atom $names) 0))
                         $rest)))))))

;; Insertion sort on the age.
(= (mt:by-age $rs)
   (if (== $rs ()) () (mt:insert (car-atom $rs) (mt:by-age (cdr-atom $rs)))))
(= (mt:insert $r $sorted)
   (if (== $sorted ()) ($r)
     (let (($a $n $t) ($b $m $u)) ($r (car-atom $sorted))
       (if (<= $a $b) (cons-atom $r $sorted)
         (cons-atom (car-atom $sorted) (mt:insert $r (cdr-atom $sorted)))))))

;; A term in goal_sexpr's notation: hypotheses by name, binders inside the
;; term by depth from 0.
(= (mt:show $t $names $d)
   (case $t
     (((V $i) (if (< $i $d) (mk:bname (- (- $d 1) $i)) (mt:name-at (- $i $d) $names)))
      ((C $n) $n)
      ((S 0) Prop)
      ((S 1) meg_Type)
      ((L $T $b) (λ ((mk:bname $d) (mt:show $T $names $d)) (mt:show $b $names (+ $d 1))))
      ((P $T $b) (if (mk:free-from $b 1 0)
                     (→ (mt:show $T $names $d) (mt:show $b $names (+ $d 1)))
                     (∀ ((mk:bname $d) (mt:show $T $names $d)) (mt:show $b $names (+ $d 1)))))
      ((A $f $a) (let ($h $as) (mk:spine $t ())
                   (cons-atom (mt:show $h $names $d) (map-atom $as $x (mt:show $x $names $d)))))
      ($o $t))))

(= (mt:name-at $i $names)
   (let $n (mk:nth $i $names) (case $n (((Hidden $x) (mk:entry-name $x)) ($o (mk:entry-name $n))))))

;; ------------------------------------------------------------ the goal

;; The statement of a library theorem or a test goal, and the index before
;; which the library may be used: (index T).
(= (mt:statement $name)
   (case (collapse (match &goals (Goal $name $i $t) ($i $t)))
     (((($i $t)) ($i (mk:db $t 0)))
      ($o (let ($i $t) (match &lib (MkIndexed $i (MkTheorem $name $p $t)) ($i $t))
            ($i (mk:db $t 0)))))))

(= (mt:load-library $index)
   (let* (($old (collapse (match &kb $x $x)))
          ($gone (map-atom $old $x (remove-atom &kb $x))))
     (mk:load-kb $index)))

;; Replay a found script from the statement into one term; the kernel checks it.
(= (mt:verdict $T $script) (mk:prove-and-check $T $script))
