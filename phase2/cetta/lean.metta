;; Lean from MeTTa: the leanprover-community REPL as a CeTTa stream process.
;; Requests are JSON; each answer ends with a blank line. One REPL per theorem.
;;
;;   (lean:open)                 -> (Lean <process> <env>)  library + goal printer loaded
;;   (lean:start $l $name $sig)  -> proof state number, or (LeanError <text>)
;;   (lean:step $l $st $tactic)  -> proof state number, or (LeanError <text>)
;;   (lean:observe $l $st)       -> (Obs <goal text> ((<name> <type text>) ...)) | NoGoal
;;   (lean:close $l)

!(import! &self proc)
!(import! &self str)
!(import! &self json)
!(import! &self fs)

(= (lean:repl) "/home/yenat/ai-mathematician/tools/repl/.lake/build/bin/repl")
(= (lean:lib) "/home/yenat/ai-mathematician/lib")
(= (lean:sysroot) "/home/yenat/lean4-toolchain/lean-4.34.0-linux")
(= (lean:sexpr-source) "/home/yenat/ai-mathematician/phase2/cetta/data/sexpr.lean")
;; 100 ms polls: an answer missing after 30 s is a timeout (as in ../lean_step.py).
(= (lean:max-polls) 300)

(= (lean:frame $p $acc $n)
   (if (str:ends-with $acc "\n\n")
       (json:parse $acc)
       (if (> $n (lean:max-polls))
           LeanTimeout
           (case (proc:read $p stdout 100)
             (((proc:chunk $part) (lean:frame $p (str:concat $acc $part) $n))
              (proc:pending (lean:frame $p $acc (+ $n 1)))
              ($other LeanTimeout))))))

(= (lean:send $p $request)
   (let $q (proc:write $p (str:concat (json:stringify $request) "\n\n"))
     (lean:frame $p "" 0)))

(= (lean:open)
   (let* (($repl (lean:repl)) ($root (lean:sysroot)) ($lib (lean:lib))
          ($path (str:concat $root "/bin:/usr/bin:/bin"))
          ($p (proc:spawn ($repl)
                ((mode stream) (max-bytes 16777216) (timeout-ms 3600000) (lifetime owner)
                 (env (("LEAN_SYSROOT" $root) ("LEAN_PATH" $lib) ("PATH" $path))))))
          ($base (lean:send $p (JsonObject ((JsonPair "cmd" "import Lean\nimport Bridge")))))
          ($src (fs:read-text (lean:sexpr-source)))
          ($r (lean:send $p (JsonObject ((JsonPair "cmd" $src) (JsonPair "env" (json:get $base "env")))))))
     (Lean $p (json:get $r "env"))))

;; Cancel rather than wait: after a timeout the REPL may still be busy, and
;; waiting for it would block until the process lifetime runs out.
(= (lean:close (Lean $p $env))
   (let* (($a (proc:cancel $p)) ($c (proc:close $p))) closed))

;; Error messages of a reply, as a list of strings.
(= (lean:errors $r)
   (collapse (let $m (superpose (lean:messages $r))
               (if (== (json:get $m "severity") "error") (json:get $m "data") (empty)))))
(= (lean:messages $r)
   (case (json:get $r "messages") ((($ms) $ms) ($ms $ms))))

(= (json:items $x) (case $x (((JsonArray $xs) $xs) ($other ()))))
