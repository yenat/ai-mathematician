;; Prove a goal from a MeTTa tactic script and check the proof, all in MeTTa.
;;
;;   cetta --lang petta@1.0.6 replay.metta <goal> <out.jsonl>
;;
;; Reads goals.metta (Goal name index type) and scripts.metta
;; (Script name (tactic ...)) (import! takes only literal paths); loads the library before the goal's index
;; (check.metta checks all of it on its own); runs the tactics
;; (tactics.metta), checks the proof term with the kernel, and appends
;;   {"goal", "proved", "tactics", "proof", "statement", "reason", "secs"}
;; to out.jsonl, where proof and statement are MeTTa expressions.

!(import! &self "/home/yenat/ai-mathematician/phase2/metta/tactics.metta")
!(import! &self fs)
!(import! &self json)
!(bind! &goals (new-space))
!(bind! &scripts (new-space))

!(import! &lib "/home/yenat/ai-mathematician/phase2/metta/meglib.metta")
!(import! &goals "/home/yenat/ai-mathematician/phase2/metta/goals.metta")
!(import! &scripts "/home/yenat/ai-mathematician/phase2/metta/scripts.metta")

(= (rp:json $name $res $script $secs)
   (case $res
     (((Proved (: $p $t))
       (JsonObject ((JsonPair "goal" (str:symbol->string $name)) (JsonPair "proved" true)
                    (JsonPair "tactics" (repr $script)) (JsonPair "proof" (repr $p))
                    (JsonPair "statement" (repr $t)) (JsonPair "secs" $secs))))
      ((Failed $why)
       (JsonObject ((JsonPair "goal" (str:symbol->string $name)) (JsonPair "proved" false)
                    (JsonPair "tactics" (repr $script)) (JsonPair "reason" (repr $why))
                    (JsonPair "secs" $secs)))))))

!(let* (($name (str:string->symbol (ck:arg 0 "quotient_remainder_int_nat")))
        ($out (ck:arg 1 "/home/yenat/ai-mathematician/phase2/metta/results/replay.jsonl"))
        ($t0 (/ (system:monotonic-ns) 1000000))
        ((Goal $name $index $T) (match &goals (Goal $name $i $t) (Goal $name $i $t)))
        ($script (match &scripts (Script $name $s) $s))
        ($n (mk:load-kb $index))
        ($res (mk:prove-and-check (mk:db $T 0) $script))
        ($secs (/ (- (/ (system:monotonic-ns) 1000000) $t0) 1000))
        ($row (rp:json $name $res $script $secs))
        ($w (fs:append-text $out (str:concat (json:stringify $row) "\n"))))
   (println! (case $res (((Proved $x) (PROVED $name in MeTTa, kernel-checked, $secs s, $n declarations loaded))
                         ((Failed $why) (FAILED $name $why))))))
