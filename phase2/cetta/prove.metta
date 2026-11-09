;; Phase 2 on CeTTa: MeTTa drives Lean, with no Python during search.
;;
;;   cetta --lang petta@1.0.6 prove.metta <name,name,...> <out.jsonl> [depth] [budget] [seconds]
;;
;; Defaults: depth 4, 300 Lean steps, 120 s per theorem.
;; Premise ranking is the Phase 1 MeTTa port of phase1/search.py; a finished
;; script counts only after that port's Phase 1 guard accepts it
;; (statement identity, no sorryAx, nothing cited from after the theorem).
;; Needs data/ from prepare.py, and CETTA_ITP_RUNTIME=native with lean on PATH.

!(import! &self proc)
!(import! &self fs)
!(import! &self str)
!(import! &self json)
!(import! &self system)
!(import! &self (library list))
!(import! &self "/home/yenat/cetta-demo/repo/phase1/library.metta")
!(import! &self "/home/yenat/cetta-demo/repo/phase1/search.metta")
!(import! &self "/home/yenat/cetta-demo/repo/phase1/itp.metta")
!(import! &self "lean.metta")
!(import! &self "host.metta")
!(import! &self "controller.metta")
!(import! &self "data/library.metta")

(= (p2:corpus) "/home/yenat/ai-mathematician/data/corpus.sexpr")
(= (p2:guard-root) "/home/yenat/cetta-demo/repo")
(= (p2:lean-bin) "/home/yenat/lean4-toolchain/lean-4.34.0-linux/bin/lean")

(= (p2:arg $i $default)
   (if (> (system:argc) $i)
       (let $a (system:arg $i) (if (== (get-metatype $a) Symbol) (str:symbol->string $a) $a))
       $default))
(= (p2:number $text) (str:string->number $text))

;; Forget the previous theorem's run.
(= (p2:reset $name $index $depth $budget $seconds $ranking $lean)
   (let* (($old (collapse (match &self (P2Seen $s $o) (P2Seen $s $o))))
          ($a (map-atom $old $x (remove-atom &self $x)))
          ($old2 (collapse (match &self (P2Parent $s $p) (P2Parent $s $p))))
          ($b (map-atom $old2 $x (remove-atom &self $x)))
          ($old3 (collapse (match &self (P2Trace $k $s $t $o $m) (P2Trace $k $s $t $o $m))))
          ($c (map-atom $old3 $x (remove-atom &self $x)))
          ($d (p2:set target $index)) ($e (p2:set steps 0)) ($f (p2:set fresh 0))
          ($g (p2:set budget $budget)) ($h (p2:set aborted none))
          ($i (p2:set deadline (+ (p2:now-ms) (* 1000 $seconds))))
          ($j (p2:set ranking $ranking)) ($k (add-atom &self (P2Lean $index $lean))))
     done))

(= (p2:start $name)
   (let* (((Lean $p $env) (p2:lean))
          ($sig (match &self (Statement $name $s) $s))
          ($src (str:join "" ("namespace Megalodon\ntheorem attempt__" (str:symbol->string $name) $sig
                              " := by sorry\nend Megalodon")))
          ($r (lean:send $p (JsonObject ((JsonPair "cmd" $src) (JsonPair "env" $env)))))
          ($sorries (json:items (json:get $r "sorries"))))
     (if (== $sorries ()) (CannotOpen $r) (json:get (car-atom $sorries) "proofState"))))

(= (p2:trace-json)
   (let $rows (sort-atom (collapse (match &self (P2Trace $k $s $t $o $m) ($k $s $t $o $m))))
     (JsonArray (map-atom $rows $r (let ($k $s $t $o $m) $r (JsonArray ($s $t $o $m)))))))

(= (p2:prove-one $search $ctx $name $depth $budget $seconds)
   (let* (($index (match &self (Index $name $i) $i))
          ($ranking (ai-math:entry-names (ai-math:rank-with $search $index 400 ())))
          ($t0 (p2:now-ms))
          ($lean (lean:open))
          ($reset (p2:reset $name $index $depth $budget $seconds $ranking $lean))
          ($st (p2:start $name))
          ($res (if (== (get-metatype $st) Expression) Fail (prove $st $depth)))
          ($closed (lean:close $lean))
          ($secs (/ (- (p2:now-ms) $t0) 1000))
          ($script (if (== $res Fail) () $res))
          ($verdict (if (== $res Fail) none
                      (ai-math:itp-check $ctx (str:symbol->string $name) (str:join "\n" $script))))
          ($proved (case $verdict (((AiITP:Accepted $n $u $a) true) ($other false))))
          ($check (case $verdict ((none none) ((AiITP:Accepted $n $u $a) "ok") ($other (repr $other))))))
     (JsonObject ((JsonPair "goal" (str:symbol->string $name))
                  (JsonPair "steps" (p2:get steps)) (JsonPair "secs" $secs)
                  (JsonPair "aborted" (p2:text (p2:get aborted)))
                  (JsonPair "proved" $proved)
                  (JsonPair "script" (JsonArray $script))
                  (JsonPair "check" (p2:text $check))
                  (JsonPair "trace" (p2:trace-json))))))

(= (p2:run $names $out $depth $budget $seconds)
   (let* (($decls (ai-math:load-library (p2:corpus)))
          ($search (ai-math:search $decls))
          ($ctx (ai-math:itp $decls (p2:guard-root) (p2:lean-bin)))
          ($cleared (fs:write $out "")))
     (foldl-atom $names 0 $won $name
       (let* (($row (p2:prove-one $search $ctx $name $depth $budget $seconds))
              ($line (fs:append-text $out (str:concat (json:stringify $row) "\n")))
              ($ok (json:get $row "proved"))
              ($shown (println! (str:join "" ((str:symbol->string $name) " "
                         (if $ok "PROVED" (json:get $row "aborted")) " ("
                         (str:number->string (json:get $row "steps")) " steps, "
                         (str:number->string (json:get $row "secs")) "s)")))))
         (if $ok (+ $won 1) $won)))))

!(let* (($names (map-atom (str:split "," (p2:arg 0 "andI")) $n (str:string->symbol $n)))
        ($out (p2:arg 1 "results/cetta_run.jsonl"))
        ($depth (p2:number (p2:arg 2 "4")))
        ($budget (p2:number (p2:arg 3 "300")))
        ($seconds (p2:number (p2:arg 4 "120")))
        ($t0 (p2:now-ms))
        ($won (p2:run $names $out $depth $budget $seconds)))
   (println! (str:join "" ("MeTTa-driven search on CeTTa proved " (str:number->string $won) "/"
                           (str:number->string (size-atom $names)) " in "
                           (str:number->string (/ (- (p2:now-ms) $t0) 1000)) "s"))))
