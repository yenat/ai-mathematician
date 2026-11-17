;; Phase 2 on CeTTa: MeTTa drives Lean, with no Python during search.
;;
;;   cetta --lang petta@1.0.6 prove.metta <name,name,...> <out.jsonl> [depth] [budget] [seconds] [hint,hint,...|auto|auto:K] [lean|metta]
;;
;; Hints: lemma names, or auto (auto:K) for the first 30 (K) chosen per goal
;; by ../metta/hints.metta from the library alone, without the goal's proof.
;;
;; Defaults: depth 4, 300 steps, 120 s per theorem, backend lean.
;; Tactics are MeTTa atoms (host.metta).  Backend lean: each is rendered to
;; Lean text and run in the Lean REPL, and the script is checked by the Phase 1
;; guard.  Backend metta: each is run by ../metta/tactics.metta, and the script
;; is replayed into one proof term checked by the MeTTa kernel; Lean is not
;; started.
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
;; The MeTTa engine first: CeTTa compiles each file as it is imported, so a
;; function must be defined before a file that calls it is imported.
!(import! &self "/home/yenat/ai-mathematician/phase2/metta/tactics.metta")
!(import! &self "mettahost.metta")
!(bind! &goals (new-space))
!(import! &lib "/home/yenat/ai-mathematician/phase2/metta/meglib.metta")
!(import! &goals "/home/yenat/ai-mathematician/phase2/metta/goals.metta")
!(import! &self "/home/yenat/ai-mathematician/phase2/metta/hints.metta")
!(import! &self "lean.metta")
!(import! &self "host.metta")
!(import! &self "controller.metta")
!(import! &self "witness_hints.metta")
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
          ($old4 (collapse (match &self (P2Via $s $t) (P2Via $s $t))))
          ($c2 (map-atom $old4 $x (remove-atom &self $x)))
          ($old5 (collapse (match &self (P2Applied $s $l) (P2Applied $s $l))))
          ($c3 (map-atom $old5 $x (remove-atom &self $x)))
          ($d (p2:set target $index)) ($e (p2:set steps 0)) ($f (p2:set fresh 0))
          ($g (p2:set budget $budget)) ($h (p2:set aborted none))
          ($i (p2:set deadline (+ (p2:now-ms) (* 1000 $seconds))))
          ($j (p2:set ranking $ranking)) ($k (add-atom &self (P2Lean $index $lean)))
          ($gname (p2:set goal $name))
          ($m (mt:reset)))
     done))

(= (p2:start $name)
   (if (== (p2:get backend) metta) (p2:start-metta $name) (p2:start-lean $name)))

;; The statement as exported from Lean (../metta/export.py), the library
;; before it loaded into the kernel's &kb.
(= (p2:start-metta $name)
   (let* ((($i $T) (mt:statement $name))
          ($n (mt:load-library $i))
          ($s (p2:set statement $T)))
     (mt:start $T)))

(= (p2:start-lean $name)
   (let* (((Lean $p $env) (p2:lean))
          ($sig (match &self (Statement $name $s) $s))
          ($src (str:join "" ("namespace Megalodon\ntheorem attempt__" (str:symbol->string $name) $sig
                              " := by sorry\nend Megalodon")))
          ($r (lean:send $p (JsonObject ((JsonPair "cmd" $src) (JsonPair "env" $env)))))
          ($sorries (json:items (json:get $r "sorries"))))
     (if (== $sorries ()) (CannotOpen $r) (json:get (car-atom $sorries) "proofState"))))

(= (p2:trace-json)
   (let $rows (sort-atom (collapse (match &self (P2Trace $k $s $t $o $m) ($k $s $t $o $m))))
     (JsonArray (map-atom $rows $r (let ($k $s $t $o $m) $r (JsonArray ($s (p2:render $t) $o $m)))))))

(= (p2:prove-one $search $ctx $name $depth $budget $seconds)
   (let* (($index (match &self (Index $name $i) $i))
          ($ranking (ai-math:entry-names (ai-math:rank-with $search $index 400 ())))
          ($t0 (p2:now-ms))
          ($metta (== (p2:get backend) metta))
          ($lean (if $metta none (lean:open)))
          ($reset (p2:reset $name $index $depth $budget $seconds $ranking $lean))
          ($st (p2:start $name))
          ($res (if (== (get-metatype $st) Expression) Fail (prove $st $depth)))
          ($closed (if $metta done (lean:close $lean)))
          ($secs (/ (- (p2:now-ms) $t0) 1000))
          ($script (if (== $res Fail) () $res))
          ($verdict (if (== $res Fail) none
                      (if $metta (mt:verdict (p2:get statement) $script)
                        (ai-math:itp-check $ctx (str:symbol->string $name)
                                           (str:join "\n" (map-atom $script $tac (p2:render $tac)))))))
          ($proved (case $verdict (((AiITP:Accepted $n $u $a) true) ((Proved $x) true) ($other false))))
          ($proof (case $verdict (((Proved (: $pterm $pstmt)) (repr $pterm)) ($other ""))))
          ($check (case $verdict ((none none) ((AiITP:Accepted $n $u $a) "ok") ((Proved $x) "ok: MeTTa kernel")
                                  ($other (repr $other))))))
     (JsonObject ((JsonPair "goal" (str:symbol->string $name))
                  (JsonPair "steps" (p2:get steps)) (JsonPair "secs" $secs)
                  (JsonPair "aborted" (p2:text (p2:get aborted)))
                  (JsonPair "proved" $proved)
                  (JsonPair "hints" (JsonArray (collapse (match &self (P2Hint $h) (str:symbol->string $h)))))
                  (JsonPair "backend" (p2:text (p2:get backend)))
                  (JsonPair "script" (JsonArray (map-atom $script $tac (p2:render $tac))))
                  (JsonPair "tactics" (repr $script))
                  (JsonPair "proof" $proof)
                  (JsonPair "check" (p2:text $check))
                  (JsonPair "trace" (p2:trace-json))))))

;; The hints for one goal: the names given, or (Auto K): chosen from the
;; goal's statement and the library before it (hints.metta).
(= (p2:set-hints $name $hints)
   (let* (($old (collapse (match &self (P2Hint $h) (P2Hint $h))))
          ($a (map-atom $old $x (remove-atom &self $x)))
          ($names (case $hints
                    (((Auto $k) (let ($i $T) (mt:statement $name) (hn:hints-at $i (hn:consts $T) $k)))
                     ($given $given)))))
     (map-atom $names $h (add-atom &self (P2Hint $h)))))

(= (p2:run $names $out $depth $budget $seconds $hints $backend)
   (let* (($b (p2:set backend $backend))
          ($decls (ai-math:load-library (p2:corpus)))
          ($search (ai-math:search $decls))
          ($ctx (ai-math:itp $decls (p2:guard-root) (p2:lean-bin)))
          ($cleared (fs:write $out ""))
          ($indexed (case $hints (((Auto $k) (hn:load)) ($o none)))))
     (foldl-atom $names 0 $won $name
       (let* (($hinted (p2:set-hints $name $hints))
              ($row (p2:prove-one $search $ctx $name $depth $budget $seconds))
              ($line (fs:append-text $out (str:concat (json:stringify $row) "\n")))
              ($ok (json:get $row "proved"))
              ($shown (println! (str:join "" ((str:symbol->string $name) " "
                         (if $ok "PROVED" (json:get $row "aborted")) " ("
                         (str:number->string (json:get $row "steps")) " steps, "
                         (str:number->string (json:get $row "secs")) "s)")))))
         (if $ok (+ $won 1) $won)))))

;; "" -> (), "auto" -> (Auto 30), "auto:K" -> (Auto K), else a list of names.
(= (p2:hint-arg $h)
   (if (== $h "") ()
     (if (== $h "auto") (Auto 30)
       (if (str:starts-with $h "auto:")
           (Auto (str:string->number (str:byte-slice $h 5 (str:byte-length $h))))
           (map-atom (str:split "," $h) $n (str:string->symbol $n))))))

!(let* (($names (map-atom (str:split "," (p2:arg 0 "andI")) $n (str:string->symbol $n)))
        ($out (p2:arg 1 "results/cetta_run.jsonl"))
        ($depth (p2:number (p2:arg 2 "4")))
        ($budget (p2:number (p2:arg 3 "300")))
        ($seconds (p2:number (p2:arg 4 "120")))
        ($t0 (p2:now-ms))
        ($hints (p2:hint-arg (p2:arg 5 "")))
        ($backend (str:string->symbol (p2:arg 6 "lean")))
        ($won (p2:run $names $out $depth $budget $seconds $hints $backend)))
   (println! (str:join "" ("MeTTa-driven search on CeTTa proved " (str:number->string $won) "/"
                           (str:number->string (size-atom $names)) " in "
                           (str:number->string (/ (- (p2:now-ms) $t0) 1000)) "s"))))
