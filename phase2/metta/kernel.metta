;; The MeTTa kernel: Lean's type theory, as the library uses it, in MeTTa.
;; Imported by check.metta (checks the library) and tactics.metta (builds
;; and checks proofs found by the prover).
;;
;; The logic is the fragment of Lean's type theory the library uses:
;; sorts Prop : Type : Type1, dependent functions (∀ / →), λ, application,
;; definitions, let.  Two types are compared up to β, η, let and unfolding of
;; definitions (lazily, later definitions first, as Lean does).
;;
;; Terms are read into de Bruijn form, where a variable is its distance to its
;; binder, because MeTTa's $x has no scope and cannot be a binder:
;;   (V i) variable   (C name) constant   (S k) sort, Prop = (S 0)
;;   (A f a) application   (L T b) λ   (P T b) ∀ or →   (Let T v b)
;; The export names a binder at depth d `_bd`, so a use of `_bn` at depth d
;; is (V (d-1-n)).

!(import! &self str)
!(import! &self system)
!(bind! &lib (new-space))
!(bind! &kb (new-space))

(= (ck:arg $i $default)
   (if (> (system:argc) $i)
       (let $a (system:arg $i) (if (== (get-metatype $a) Symbol) (str:symbol->string $a) $a))
       $default))

;; ------------------------------------------------------------ reading terms

(= (ck:bound? $s) (str:starts-with (str:symbol->string $s) "_b"))
(= (ck:level $s) (str:string->number (car-atom (cdr-atom (str:split "_b" (str:symbol->string $s))))))

(= (mk:db $t $d)
   (case (get-metatype $t)
     ((Symbol (mk:db-sym $t $d))
      (Expression (mk:db-expr $t $d))
      ($other (Bad (cannot read $t))))))

(= (mk:db-sym $t $d)
   (if (== $t Prop) (S 0)
     (if (or (== $t Type) (== $t meg_Type)) (S 1)
       (if (ck:bound? $t) (V (- (- $d 1) (ck:level $t)))
         (C $t)))))

(= (mk:db-expr $t $d)
   (case $t
     (((λ ($x $T) $b) (L (mk:db $T $d) (mk:db $b (+ $d 1))))
      ((∀ ($x $T) $b) (P (mk:db $T $d) (mk:db $b (+ $d 1))))
      ((→ $a $b) (P (mk:db $a $d) (mk:db $b (+ $d 1))))
      ((let ($x $T $v) $b) (Let (mk:db $T $d) (mk:db $v $d) (mk:db $b (+ $d 1))))
      ($app (foldl-atom (cdr-atom $app) (mk:db (car-atom $app) $d) $f $x (A $f (mk:db $x $d)))))))

;; --------------------------------------------------- shifting and substitution

;; (M m d) is tactics.metta's metavariable m seen under d binders; it never
;; occurs in library terms.
(= (mk:shift $k $c $t)
   (case $t
     (((V $i) (if (< $i $c) (V $i) (V (+ $i $k))))
      ((M $m $d) (M $m (+ $d $k)))
      ((A $f $a) (A (mk:shift $k $c $f) (mk:shift $k $c $a)))
      ((L $T $b) (L (mk:shift $k $c $T) (mk:shift $k (+ $c 1) $b)))
      ((P $T $b) (P (mk:shift $k $c $T) (mk:shift $k (+ $c 1) $b)))
      ((Let $T $v $b) (Let (mk:shift $k $c $T) (mk:shift $k $c $v) (mk:shift $k (+ $c 1) $b)))
      ($other $t))))

;; (mk:subst j s t): t with variable j replaced by s, and the binder removed.
(= (mk:subst $j $s $t)
   (case $t
     (((V $i) (if (== $i $j) $s (if (> $i $j) (V (- $i 1)) (V $i))))
      ((M $m $d) (if (< $j $d) (M $m (- $d 1)) (M $m $d)))
      ((A $f $a) (A (mk:subst $j $s $f) (mk:subst $j $s $a)))
      ((L $T $b) (L (mk:subst $j $s $T) (mk:subst (+ $j 1) (mk:shift 1 0 $s) $b)))
      ((P $T $b) (P (mk:subst $j $s $T) (mk:subst (+ $j 1) (mk:shift 1 0 $s) $b)))
      ((Let $T $v $b) (Let (mk:subst $j $s $T) (mk:subst $j $s $v) (mk:subst (+ $j 1) (mk:shift 1 0 $s) $b)))
      ($other $t))))

(= (mk:inst $b $a) (mk:subst 0 $a $b))

;; ----------------------------------------------------------- reduction

;; β and let at the head, no unfolding.
(= (mk:whnf-core $t)
   (case $t
     (((A $f $a)
       (let $g (mk:whnf-core $f)
         (case $g (((L $T $b) (mk:whnf-core (mk:inst $b $a))) ($o (A $g $a))))))
      ((Let $T $v $b) (mk:whnf-core (mk:inst $b $v)))
      ($other $t))))

(= (mk:def-of $n) (collapse (match &kb (Df $n $b $h) ($b $h))))

;; Height of the definition at the head of t's spine, or -1.
(= (mk:height $t)
   (case $t
     (((C $n) (case (mk:def-of $n) (((($b $h)) $h) ($o -1))))
      ((A $f $a) (mk:height $f))
      ($other -1))))

;; t with the definition at its head unfolded (only called when height >= 0).
(= (mk:unfold $t)
   (case $t
     (((C $n) (let (($b $h)) (mk:def-of $n) $b))
      ((A $f $a) (A (mk:unfold $f) $a)))))

(= (mk:whnf $t)
   (let $u (mk:whnf-core $t)
     (if (>= (mk:height $u) 0) (mk:whnf (mk:unfold $u)) $u)))

;; ---------------------------------------------------------- conversion

(= (mk:conv $a $b)
   (if (== $a $b) true
     (let* (($x (mk:whnf-core $a)) ($y (mk:whnf-core $b)))
       (if (== $x $y) true
         (if (mk:conv-struct $x $y) true (mk:conv-delta $x $y))))))

(= (mk:conv-struct $x $y)
   (case ($x $y)
     ((((P $T1 $B1) (P $T2 $B2)) (if (mk:conv $T1 $T2) (mk:conv $B1 $B2) false))
      (((L $T1 $B1) (L $T2 $B2)) (if (mk:conv $T1 $T2) (mk:conv $B1 $B2) false))
      ;; Applications agree argument by argument only when they have the
      ;; same head and as many arguments; otherwise unfold (mk:conv-delta), so
      ;; (Pi_nat f 0) against (nat_primrec ... 0) unfolds Pi_nat, not
      ;; everything under nat_primrec.
      (((A $f1 $a1) (A $f2 $a2))
       (let* ((($h1 $as1) (mk:spine $x ())) (($h2 $as2) (mk:spine $y ())))
         (if (and (== $h1 $h2) (== (size-atom $as1) (size-atom $as2)))
             (mk:conv-args $as1 $as2)
             false)))
      (((L $T $B) $o) (mk:conv-eta $B $o))
      (($o (L $T $B)) (mk:conv-eta $B $o))
      ($other false))))

;; (mk:spine (A (A h a) b) ()) is (h (a b)).
(= (mk:spine $t $args)
   (case $t (((A $f $a) (mk:spine $f (cons-atom $a $args))) ($o ($t $args)))))

(= (mk:conv-args $as $bs)
   (if (== $as ()) true
     (if (mk:conv (car-atom $as) (car-atom $bs)) (mk:conv-args (cdr-atom $as) (cdr-atom $bs)) false)))

;; η: (λ x. f x) is f.
(= (mk:conv-eta $body $other)
   (case $other
     (((L $T $B) false)
      ($o (mk:conv $body (A (mk:shift 1 0 $o) (V 0)))))))

(= (mk:conv-delta $x $y)
   (let* (($hx (mk:height $x)) ($hy (mk:height $y)))
     (if (and (>= $hx 0) (>= $hx $hy)) (mk:conv (mk:unfold $x) $y)
       (if (>= $hy 0) (mk:conv $x (mk:unfold $y)) false))))

;; -------------------------------------------------------------- typing

(= (mk:nth $i $ctx) (if (== $i 0) (car-atom $ctx) (mk:nth (- $i 1) (cdr-atom $ctx))))

(= (mk:const-type $n)
   (case (collapse (match &kb (Ty $n $t) $t))
     ((($t) $t) ($o (Bad (unknown constant $n))))))

(= (mk:bad? $t) (case $t (((Bad $r) true) ($o false))))

;; The sort of a type, as a number (Prop = 0), or Bad.
(= (mk:sort-of $ctx $T)
   (let $s (mk:infer $ctx $T)
     (if (mk:bad? $s) $s
       (case (mk:whnf $s) (((S $k) $k) ($o (Bad (not a type $T))))))))

(= (mk:infer $ctx $t)
   (case $t
     (((V $i) (mk:shift (+ $i 1) 0 (mk:nth $i $ctx)))
      ((C $n) (mk:const-type $n))
      ((S $k) (S (+ $k 1)))
      ((P $T $b)
       (let $k1 (mk:sort-of $ctx $T)
         (if (mk:bad? $k1) $k1
           (let $k2 (mk:sort-of (cons-atom $T $ctx) $b)
             (if (mk:bad? $k2) $k2
               (S (if (== $k2 0) 0 (if (> $k1 $k2) $k1 $k2))))))))
      ((L $T $b)
       (let $k (mk:sort-of $ctx $T)
         (if (mk:bad? $k) $k
           (let $B (mk:infer (cons-atom $T $ctx) $b)
             (if (mk:bad? $B) $B (P $T $B))))))
      ((A $f $a)
       (let $F (mk:infer $ctx $f)
         (if (mk:bad? $F) $F
           (case (mk:whnf $F)
             (((P $T $B)
               (let $U (mk:infer $ctx $a)
                 (if (mk:bad? $U) $U
                   (if (mk:conv $U $T) (mk:inst $B $a) (Bad (argument mismatch in $t))))))
              ($o (Bad (not a function $f))))))))
      ((Let $T $v $b)
       (let $U (mk:infer $ctx $v)
         (if (mk:bad? $U) $U
           (if (mk:conv $U $T) (mk:infer $ctx (mk:inst $b $v)) (Bad (let mismatch $t))))))
      ($other (Bad $other)))))

