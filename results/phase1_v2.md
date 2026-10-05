# Phase 1 v2 — distilling LLM proofs into free strategies

Run: 2026-09-24. Builds on `phase1_baseline_v1.md` and `phase1_llm_v1.md`.

## What changed (no LLM calls)

The 51 proofs the LLM found kept using three mechanical patterns. They are
now deterministic strategies in `phase1/prover.py` (`candidate_tactics`):

- `goal-unfold-grind` / `goal-unfold-sbe`: unfold only the goal's own
  definitions, introduce what that reveals, then `grind` or `solve_by_elim`.
- `ext-grind`: prove set equality through `set_ext`.

Also fixed: when one slow candidate hit the batch timeout it took every
other candidate down with it (43 of the 140 reconstruction failures).
Timed-out batches are now retried one candidate at a time.

## Result

Re-ran only the deterministic battery (`phase1/rebuild_failures.py`) on
the 140 theorems where Vampire found a proof but v1 reconstruction failed,
reusing v1's stored premises: **33 / 140 recovered**, 18 of which the LLM
had also proved and 15 new.

| | Proved | Rate |
|---|---|---|
| v1, no LLM | 418 / 999 | 41.8% |
| v2, no LLM | **451 / 999** | **45.1%** |
| v2 + LLM proofs from v1 | **484 / 999** | **48.4%** |

Caveat: 451 is v1's 418 plus the 33 recovered, not a fresh full
999 rerun. A full rerun with all improvements is planned.

## Where the remaining failures are

441 theorems fail because Vampire finds no proof. Only 114 of them cite an
induction principle in their original proof (nat_ind 65, SNoLev_ind 17,
ordinal_ind 12, In_ind 11, nat_complete_ind 7, finite_ind 3); 327 do not.

Oracle test: give Vampire the exact facts the original proof cited
(40 random theorems from each group):

| Group | Size | Vampire proves with perfect facts |
|---|---|---|
| Non-induction | 327 | 18 / 40 (45%) |
| Induction | 114 | 2 / 40 (5%) |

So for non-induction theorems the bottleneck is **Search** (premise
selection); for induction the missing piece is the induction predicate
itself, which better facts do not supply.

## Learned Search (2026-09-25, no LLM)

Added a naive Bayes premise selector (Sledgehammer's MaSh), trained only
on proofs of theorems BEFORE the goal, over richer statement features
(`library._features`: constants plus shape, e.g. `concl:eq>add_SNo`,
`hyp:SNo`). Blended with the existing Search (`search.Search._nb`).
Settings were tuned only on the first half of the library; the
differences between settings were small (about 1 point).

Recall (`phase1/eval_search.py`), "all facts the real proof cited found":

| Set | old @32 | new @32 | old @64 | new @64 |
|---|---|---|---|---|
| second half (untuned) | 31.9% | 36.2% | 46.4% | 51.8% |
| 327 non-induction failures | 12.2% | 19.6% | 22.6% | 33.0% |

End to end on the 441 theorems where Vampire had found no proof
(`phase1/rerun_vampire.py`, then `rebuild_failures.py`):

- Vampire now proves 38 of them. Control: with the old ranking, Vampire
  proves 7 of those 38 in a rerun, so about 31 are due to the new Search
  and the rest to Vampire's timing variation.
- Lean rebuilds **21 / 38** as kernel-checked, leak-guarded proofs. Of
  those 21, the old ranking also reaches 4 on a rerun (SNoLe_ref,
  SNo_foil_mm, Pi_SNo_S, divides_int_prime_nat_eq).

| | Proved | Rate |
|---|---|---|
| v2, no LLM | 451 / 999 | 45.1% |
| v2 + learned Search, no LLM | **472 / 999** | **47.2%** |
| ... + LLM proofs from v1 | **505 / 999** | **50.5%** |

Same caveat as above: these are cumulative gains, not yet a fresh full rerun.

## Induction without the LLM (2026-09-25)

`phase1/induction.py` builds the induction predicate itself: it reads the
goal as a statement P(x) about one of its variables and writes out the
cases of each available principle (nat_ind, nat_complete_ind,
ordinal_ind, SNoLev_ind, finite_ind, In_ind), each as a stand-alone
goal for Vampire. Only principles proved before the goal are used. In
Lean: introduce everything, revert all but x and its guard, `apply` the
principle, and prove each case with the usual battery.

On the 114 induction theorems where Vampire had found no proof
(`phase1/try_induction.py`, Vampire only):

| Premises | All cases proved by Vampire |
|---|---|
| none (plain Vampire, v1 oracle test) | 2 / 40 sampled (5%) |
| split + facts the original proof cited (ceiling) | 34 / 114 |
| split + Search's facts (real setting) | 25 / 114 |

Lean (`phase1/rebuild_induction.py`) proves **18 / 25**, all re-verified
in a fresh Lean run. Among them: commutativity of addition and
multiplication on naturals, associativity of both, and closure of
naturals under +, *, exponentiation. Each (case, tactic) is first tried
as its own declaration because Lean's heartbeat budget is per
declaration; putting all of them in one proof let a slow failure starve
the rest (16 / 25 before that fix).

| | Proved | Rate |
|---|---|---|
| + induction, no LLM | **490 / 999** | **49.0%** |
| ... + LLM proofs from v1 | **523 / 999** | **52.3%** |

## Clean full run (2026-09-25)

One run of the whole integrated pipeline (learned Search, Vampire, Lean
battery, automatic induction) over all 999 theorems, held out as before,
no LLM (`phase1/experiment.py 1 7 results/phase1_full_v2.jsonl`; resumed
once with `--resume` after a restart to use more workers; same code
throughout). Fixes made while running it, before the final launch:

- `ext-grind` never parsed (multi-line block in parentheses); fixed.
- Vampire proofs are not unique: all three premise slices now run and
  every distinct premise set Vampire used is offered to Lean (29 of the
  proofs below came from a second or third set); a proof from 0-1 facts
  also gets Search's top 8 facts.
- Candidates for extra premise sets run only if the first batch fails;
  retries after a batch timeout are capped at 480 s per goal.

**Result: 514 / 999 (51.5%), no LLM.** 999 distinct goals; 11,291 s wall
clock for the final 733 goals at 7 workers.

| | Proved | Rate |
|---|---|---|
| v1 full run, no LLM | 418 / 999 | 41.8% |
| **v2 full run, no LLM** | **514 / 999** | **51.5%** |
| v2 + the 51 LLM proofs from the v1 LLM stage (30 of them now also proved without LLM) | **535 / 999** | **53.6%** |

The v2 run replaces the cumulative 490 / 523 estimates above, which
stitched separate partial runs together.

Against v1: 113 gained, 17 lost. The losses are Vampire finding a
different proof (or none within 5 s) under the new ranking, e.g.
`equip_sym`, `equip_atleastp`, `UPairE`, `binunionE`; the pipeline has
run-to-run variation on borderline goals because of Vampire's time limit.

First successful strategy per proved theorem: prem-grind 263,
prem-unfold-grind 100, unfold-grind 50, solve_by_elim 38, intro-grind 33,
induction 18 (nat_ind 13, In_ind 3, SNoLev_ind 2), ext-grind 9,
goal-unfold-sbe 2, goal-unfold-grind 1.

Unproved: 485. Vampire found a proof for 90 of them but Lean could not
rebuild it; for 395 Vampire found none.

Time per goal (single goal, as in use rather than benchmark): proved
goals median 25 s, 90% within 76 s; failures give up at a median of 85 s.

## Follow-up: new reconstruction strategies on the 90 (2026-09-26)

`phase1/try_rebuild.py` tried new Lean strategies on the 90 goals where
Vampire found a proof but v2 could not rebuild it, reusing the stored
premise sets (no Vampire rerun, no LLM): premises as `grind` e-matching
lemmas, higher `grind` effort (`splits`/`ematch`/`gen`), `simp_all` with
premises and definitions, and `all_goals grind` so a goal already closed
by `simp` is not an error.

**6 / 90 rebuilt** (iff_refl, Repl_Empty, equip_0_Empty, form100_22_v1,
add_SNo_Lt4, int_lin_comb_I), all re-verified in fresh Lean runs;
`simp_all` with the premises was the most useful strategy. add_SNo_Lt4 was
already among the v1 LLM proofs. Counting them: 520 / 999 (52.1%) without
LLM, 540 / 999 (54.1%) with the v1 LLM proofs. This is a targeted run, not
part of the single clean run, so the headline stays 514.

The typical remaining failure is a proof that needs a higher-order
instance of a premise, e.g. `UPairE`, which needs `Eps_i_ax` at a specific
predicate: Vampire finds the instance, `grind` does not.

## v3 clean full run (2026-09-26/27)

Both follow-up levers built into the pipeline: Vampire 30 s per slice on
16/32/64/128 facts (on the 395 v2 goals without a Vampire proof this found
66 proofs, Lean rebuilt 32: `vampire30_*.jsonl`, `rebuild30_*.jsonl`), and
`followup_tactics` as a second line after the battery. A larger budget for
induction cases was tried and dropped (1 of 42 sampled splits).

**Result: 563 / 999 (56.4%), no LLM**, single run
(`phase1_full_v3.jsonl`, 6 workers, 24,960 s). All 563 re-verified in fresh
Lean runs (`recheck_v3.jsonl`: 563 / 563). With the 51 v1 LLM proofs:
584 / 999 (58.5%). Against v2: 57 gained, 8 lost (run-to-run variation).

Unproved: 436; Vampire found a proof for 115 of them. Time per goal:
proved median 42 s (90% within 157 s), failures median 190 s; the larger
Vampire budget is the cost.

## Follow-ups on top of v3 (2026-09-28/29), all re-verified

| Lever | New proofs | Files |
|---|---|---|
| Vampire 256-fact slice (30 s) | 11 | `vampire256_*.jsonl`, `rebuild256.jsonl` |
| Vampire 512-fact slice (30 s) | 7 | `vampire512.jsonl`, `rebuild512.jsonl` |
| Apply-then-grind (`apply_tactics`) | 10 | `try_apply.jsonl` |
| Vampire 4/8-fact slices | 3 | `vampire_small.jsonl`, `rebuild_small.jsonl` |
| **Duper reconstruction** (`duper_tactics`) | **51** | `try_duper.jsonl` |

Cumulative: **645 / 999 (64.6%) without LLM**, 650 with the LLM proofs; the
list of the 82 goals added to v3 is `followup_v3_new.json`. Tried without
gain: diverse small slices (Search.diverse_slices), all facts with
Vampire's own SInE filter (4/71 oracle goals), Duper from Search facts on
goals without a Vampire proof (0/30), a second Duper pass with all premise
sets and expensive higher-order rules (0/8, stopped), and the direct LLM
mode on the reconstruction residue (1/32, 96 calls).

**Duper.** Duper (leanprover-community/duper, v4.34.0; built in
`tools/duper-env`, not committed) is a superposition prover written in
Lean that produces Lean proof terms: the counterpart of Isabelle's Metis
in Sledgehammer. Given the facts Vampire used, it rebuilt 51 of the 109
goals where Vampire had a proof but every Lean strategy failed, largely
the higher-order cases (`grind` cannot instantiate predicate variables).
In the pipeline it is the last reconstruction line, each attempt in its
own Lean process with a 300 s limit (in one batch, a slow failing attempt
starved the successful one).

## v4 clean full run (launched 2026-09-29 13:36)

All of the above built in: slices 16-512, `followup_tactics`,
`apply_tactics`, Duper. Results: `phase1_full_v4.jsonl` (pending).

## v4 (2026-10-03/05): Duper as a fourth proof line

Three changes on top of v3: **Duper** (a proof-producing superposition prover
that runs natively inside Lean) as a fourth line in `prove()`, premise slices
extended to 256 and 512 facts, and `apply_tactics` as a third line.

**Result: 640 / 999 (64.1%), no LLM**, single run
(`phase1_full_v4.jsonl`, 4 workers, 79 core-hours). All 640 re-verified in
fresh Lean runs (`recheck_v4.jsonl`: **640 / 640**). Against v3: 82 gained,
5 lost to run-to-run variation.

| line | v4 | v3 | change |
|---|---:|---:|---:|
| `duper` | 44 | 0 | **+44** |
| `prem-grind` | 302 | 287 | +15 |
| `prem-unfold-grind` | 133 | 122 | +11 |
| `apply` | 7 | 0 | +7 |
| `solve_by_elim` | 40 | 37 | +3 |
| `induction` | 14 | 15 | -1 |
| `goal-unfold` | 4 | 7 | -3 |

Duper alone accounts for well over half the gain, and it is a classical
symbolic prover with no learning in it. Unproved: 359, of which Vampire
found a proof for 59. Time per goal: proved median 60 s (90% within 266 s),
failures median 265 s.

Note this 640 supersedes the earlier 645 figure quoted for v3-plus-follow-ups.
That number was cumulative over several separate passes; 640 is one run.

## Why the remaining 359 fail (2026-10-05)

Four measurements, all from this corpus, that together explain the ceiling.

**1. Premise *recall* is not the problem.** Compared against the premises
Megalodon's own proof of each goal cites, Search's top-512 contains 100% of
them even on goals that fail (top-128: 92%). v4 already slices to 512, so the
needed facts are being supplied.

**2. Premise *precision* is.** Give Vampire exactly the premises the original
proof used -- typically about 8 facts, no distractors -- and it solves 32% of
a sample of goals it had previously failed (8/25). Same facts, no noise.

**3. Prefix slicing cannot escape this.** On goals that fail, the deepest
needed fact sits at median rank 116 (75th percentile 198, 90th 396), and the
proof needs a median of 8 of them. Only 8% have all their premises inside the
top-16. So a slice small enough to be clean omits a premise, and a slice deep
enough to be complete buries Vampire in ~120 distractors. On goals that
succeed, the deepest needed fact is at rank 5 and the proof needs 2 facts.

**4. The real split is structural.** Taking each goal's original proof term
and counting its `have` steps (beta-redexes of the form
`PPFAP (PLAM p ...) ...`, i.e. "assume p, justified by ..."):

| | have-steps in the human proof | >= 1 step |
|---|---|---|
| goals v4 **proves** | median 0 | 5% |
| goals v4 **fails** | median 1, mean 4.0 | 64% |

The system solves the theorems whose human proof is a single leap, and fails
on the ones proved in steps. It has no mechanism for an intermediate lemma,
so it fails on exactly the goals that need one.

And the hops are easy: across 1592 hops from 161 decomposable failed goals,
one hop cites a median of **1** fact (82% cite at most 2) against a median of
**12** for the whole goal -- putting each hop squarely in the range the system
already proves at close to 100%.

Every lever so far (better Search, bigger slices, Duper, the LLM) has
optimised the single leap. None has removed the need for one.

## Next

1. **A `have`-chain prover.** Obtain intermediate lemma statements, prove each
   hop with the existing stack, chain to the conclusion. Two sources, in
   order: Megalodon's own proof term as an oracle (costs no API budget, and
   establishes the ceiling), then an LLM proposing the lemmas. The second is
   the right job for an LLM -- `dsp.py` failed at 1/32 because it asked for
   rigour, which the kernel judges, rather than structure, which it does not.
2. The 59 goals with a Vampire proof that even Duper cannot rebuild. Vampire's
   TPTP output carries the full derivation (numbered formulas with
   `inference(rule,[],[parents])` links) and the pipeline currently discards
   all of it, keeping only the axiom names. Replaying it as a `have` chain is
   the same idea as (1) from a different source.
3. Richer induction (generalising the goal, strengthening the predicate).
