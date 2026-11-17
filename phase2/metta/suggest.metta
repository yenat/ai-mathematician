;; Lemma hints for a library theorem or a test goal, chosen in MeTTa
;; (hints.metta) from the library alone.
;;
;;   cetta --lang petta@1.0.6 suggest.metta <goal> [K]
;;
;; Prints the first K (default 30) hints, comma-separated, as prove.metta
;; takes them.

!(import! &self str)
!(import! &self system)
!(bind! &goals (new-space))
!(import! &lib "/home/yenat/ai-mathematician/phase2/metta/meglib.metta")
!(import! &goals "/home/yenat/ai-mathematician/phase2/metta/goals.metta")
!(import! &self "/home/yenat/ai-mathematician/phase2/metta/hints.metta")

(= (sg:arg $i $default)
   (if (> (system:argc) $i)
       (let $a (system:arg $i) (if (== (get-metatype $a) Symbol) (str:symbol->string $a) $a))
       $default))

(= (sg:csv $l)
   (if (== $l ()) ""
     (foldl-atom (cdr-atom $l) (str:symbol->string (car-atom $l)) $acc $n
       (str:concat $acc (str:concat "," (str:symbol->string $n))))))

;; A test goal's statement, or a library theorem's.
(= (sg:hints $g $K)
   (case (collapse (match &goals (Goal $g $i $t) ($i $t)))
     (((($i $t)) (hn:hints-at $i (hn:consts $t) $K))
      ($o (hn:hints $g $K)))))

!(let* (($g (str:string->symbol (sg:arg 0 "quotient_remainder_int")))
        ($K (str:string->number (sg:arg 1 "30")))
        ($n (hn:load)))
   (println! (sg:csv (sg:hints $g $K))))
