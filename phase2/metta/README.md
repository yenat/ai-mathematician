# MeTTa checks the proofs

The Lean library is translated to MeTTa once. From then on, MeTTa checks the
library and runs tactics, and the proofs it builds are MeTTa terms checked by
a kernel written in MeTTa. Lean is not used at any later step. The format
follows the Metamath port in trueagi-io/chaining (`experimental/metamath`).

```bash
python3 export.py                                           # Lean -> meglib.metta, goals.metta; round trip
cetta --lang petta@1.0.6 check.metta                        # check the whole library in MeTTa
cetta --lang petta@1.0.6 replay.metta quotient_remainder_int_nat   # tactics -> proof -> kernel
python3 test_check.py; python3 test_tactics.py              # broken proofs and scripts are rejected
```

| file | what it is |
|---|---|
| `../Sexpr.lean` | the Lean → MeTTa translator; `#export_metta` (strict), `#metta_roundtrip`, `#export_type`, `#check_metta_proof` |
| `meglib.metta` | the library: `(MkIndexed i (MkAxiom name type))`, `(MkDefinition name body type)`, `(MkTheorem name proof type)` |
| `goals.metta` | test goals: `(Goal name index type)` |
| `kernel.metta` | the MeTTa kernel: types, β/η/let, unfolding of definitions |
| `check.metta` | checks the library in order, each entry against the ones before it |
| `tactics.metta` | `Intro`, `Have`, `Apply`, `Witness`, `Rewrite` as MeTTa atoms, each building a piece of proof term |
| `scripts.metta` | tactic scripts: `(Script name (tactic ...))` |
| `replay.metta` | runs a script, checks the proof, appends JSON with the proof as a MeTTa expression |

## Results (2026-11-13)

| | |
|---|---|
| Translation | 1160 / 1160 declarations translate back to exactly the Lean originals; a changed file is caught |
| Library check in MeTTa | 1160 / 1160 (21 axioms, 140 definitions, 999 theorems) in 96 s on CeTTa |
| Broken proofs | 6 / 6 rejected (wrong argument, wrong binder type, changed statement, another theorem's proof, lemma cited before it is proved, proof citing itself) |
| Case 1 of quotient_remainder_int | proved in MeTTa from 52 tactics, kernel-checked, 1.1 s; Lean's kernel also accepts the MeTTa proof term (offline audit) |
| Broken scripts | 5 / 5 fail, the original passes |

A result row (`results/replay.jsonl`):

```
{"goal": "quotient_remainder_int_nat", "proved": true,
 "tactics": "((Intro x1) (Intro h2) ... (Apply f325))",
 "proof": "(λ (_b0 set) (λ (_b1 (In _b0 (setminus omega (Sing meg_Empty)))) ...",
 "statement": "(∀ (_b0 set) (→ (In _b0 (setminus omega (Sing meg_Empty))) ...", "secs": 1.09}
```

## The search on MeTTa (2026-11-14)

The prover (`../cetta/`) now builds its tactics as MeTTa atoms and runs on
either backend, chosen by its 7th argument:

```bash
cd ../cetta
cetta --lang petta@1.0.6 prove.metta <names> <out.jsonl> 40 3000 600 <hints> metta   # no Lean
cetta --lang petta@1.0.6 prove.metta <names> <out.jsonl> 40 3000 600 <hints> lean    # as before
```

On `metta`, `mettahost.metta` keeps the proof states: each tactic runs in
`tactics.metta`, observations are written as Lean's `goal_sexpr` writes them,
and the finished script is replayed into one proof term that the MeTTa kernel
checks. Tracing the run (`strace -f -e execve`) shows no process other than
CeTTa itself.

| | Lean backend | MeTTa backend |
|---|---|---|
| Case 1 of quotient_remainder_int, 17 hints | 260 steps, 11 s; script identical to before the change | **PROVED, 259 steps, 7.9 s, kernel-checked in MeTTa**; Lean's kernel also accepts the proof (offline audit) |
| 19 sample theorems (depth 4, 300 steps) | 8 / 19, 615 s | **3 / 19, 37 s** (andI, binintersectE1, SNoR_0) |

6 of the 8 Lean proofs end with `grind`, which has no MeTTa tactic; the two
that do not are both found on the MeTTa backend.

## Not yet

- Lean's `grind` has no MeTTa counterpart: the 5 sample proofs that need it
  are lost on the MeTTa backend until its steps exist as MeTTa rules.
- `IffRefine` (refine with an equivalence) has no MeTTa version yet.
- Case 2 of quotient_remainder_int has not been attempted.
