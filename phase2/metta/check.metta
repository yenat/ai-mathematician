;; Checks the library, exported from Lean by export.py, in MeTTa.
;;
;;   cetta --lang petta@1.0.6 check.metta [first] [last] [file]
;;
;; checks records first..last (default: all) of meglib.metta, or of
;; [file].metta: CeTTa runs any argument ending in .metta as a program, and
;; import! reads only .metta files, so [file] is given without the extension.
;;
;; Like pc-xp.metta in trueagi-io/chaining (experimental/metamath), the
;; library is processed in order: each axiom, definition and theorem is
;; checked against what came before it (kernel.metta), then added to &kb.
;; A proof can therefore only use lemmas stated before it.  Lean is not
;; involved.

!(import! &self "/home/yenat/ai-mathematician/phase2/metta/kernel.metta")

;; ------------------------------------------------- processing the library

;; Check one record; on success add it to &kb.  Returns Ok or (Bad ...).
(= (process $i $rec)
   (case $rec
     (((MkAxiom $n $T)
       (let* (($t (mk:db $T 0)) ($k (mk:sort-of () $t)))
         (if (mk:bad? $k) $k (let $_ (add-atom &kb (Ty $n $t)) Ok))))
      ((MkDefinition $n $V $T)
       (let* (($t (mk:db $T 0)) ($v (mk:db $V 0)) ($k (mk:sort-of () $t)))
         (if (mk:bad? $k) $k
           (let $u (mk:infer () $v)
             (if (mk:bad? $u) $u
               (if (mk:conv $u $t)
                   (let* (($_ (add-atom &kb (Ty $n $t))) ($_2 (add-atom &kb (Df $n $v $i)))) Ok)
                   (Bad (body does not have the stated type))))))))
      ((MkTheorem $n $Pf $T)
       (let* (($t (mk:db $T 0)) ($p (mk:db $Pf 0)) ($k (mk:sort-of () $t)))
         (if (mk:bad? $k) $k
           (if (not (== $k 0)) (Bad (statement is not a proposition))
             (let $u (mk:infer () $p)
               (if (mk:bad? $u) $u
                 (if (mk:conv $u $t)
                     (let $_ (add-atom &kb (Ty $n $t)) Ok)
                     (Bad (proof proves something else))))))))))))

(= (name-of $rec) (car-atom (cdr-atom $rec)))

(= (run $i $last $ok $bad)
   (if (> $i $last) ($ok $bad)
     (case (collapse (match &lib (MkIndexed $i $rec) $rec))
       ((() ($ok $bad))
        (($rec)
         (let $r (process $i $rec)
           (if (== $r Ok) (run (+ $i 1) $last (+ $ok 1) $bad)
             (let $_ (println! (FAILED $i (name-of $rec) $r))
               (run (+ $i 1) $last $ok (+ $bad 1))))))))))

!(let* (($file (str:concat (ck:arg 2 "/home/yenat/ai-mathematician/phase2/metta/meglib") ".metta"))
        ($first (str:string->number (ck:arg 0 "0")))
        ($last (str:string->number (ck:arg 1 "100000")))
        ($loaded (import! &lib $file))
        ($ok-bad (run $first $last 0 0)))
   (let ($ok $bad) $ok-bad
     (println! (CHECKED $ok OK $bad FAILED))))
