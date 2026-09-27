# Phase 1: LLM informal proof → formal outline (draft, sketch, prove)

Run: 2026-09-26. Code: `phase1/dsp.py`, via
`llm_experiment.py ... --mode dsp`. Model: openai/gpt-oss-120b.

## Method

1. Draft (1 call): informal numbered proof, naming the facts used.
2. Sketch (1 call): Lean outline following the draft; routine steps may be
   left as `sorry`.
3. Prove (no LLM): each `sorry` is replaced by the automatic tactics
   (`grind` / `solve_by_elim` over the selected facts); Lean checks the
   whole with the usual acceptance checks (kernel, statement identity,
   leak guard, no sorryAx).
4. Repair (1 call): Lean's error goes back once.

## Budget and sample

- Hard cap: 100 calls (`LLM_CALL_CAP`), ledger `llm_usage_dsp.jsonl`.
- Sample: every 15th of the 485 theorems the v2 run did not prove, i.e. 33
  theorems (fixed rule, not hand-picked). Only 5 of the 33 had a Vampire
  proof, so this is the hard remainder.
- Theorem 1 (`iff_refl`) was a live smoke test (3 calls). It failed only
  because the model's correct script continued after the goal was closed
  ("No goals to be solved"). This led to a no-call fix: retry with trailing
  lines removed. The stored reply passes after that fix, checked offline,
  but it is NOT counted.
- The other 32 were run with the final code (`llm_dsp.jsonl`).

## Result

**0 / 32 proved.** 99 calls in total (including the smoke test), with
438,254 prompt and 287,695 completion tokens; 4 requests were retried after
API errors and count against the cap. Median 27.6 s per completed call.

The final failure reason for each theorem:

| Reason | Theorems |
|---|---|
| Lean heartbeat budget exhausted (gap filling) | 13 |
| Model treats encoded logic / opaque sets as Lean-native (`cases`, `constructor`, `Or.inl`, projections on `In`, `and`, `or`, ...) | 11 |
| Type mismatch | 3 |
| Wrong number of `intro`s | 2 |
| Other (assumption failed, unfillable placeholder, goal not closed) | 3 |

64 outlines were written; 41 left at least one gap (mean 1.6 gaps).

## Post-hoc check: is the heartbeat budget the cause?

All 64 stored outlines, exactly as filled in the run, were re-checked with
5x the heartbeat budget (1,000,000; `llm_dsp_heartbeats_recheck.json`, no
API calls): **0 / 64 pass**; 20 still time out, at the same points (`whnf`,
`isDefEq`). The time-outs are not a budget artifact: the gaps the model left
are too large or too hard for the automatic tactics to close (or state
claims that do not follow).

## Reading

- The largest single failure class is time-outs while filling gaps, and
  the post-hoc check shows more budget does not help: the gaps are too
  coarse for `grind` / `solve_by_elim`.
- The second is the model: despite explicit instructions, it applies
  Lean-native reasoning to Megalodon's Church-encoded logic and opaque set
  primitives.
- Not comparable to the v1 direct-mode result (51/140), which targeted
  theorems where Vampire had already found a proof and supplied good
  premises; here 28 of 32 had no Vampire proof.
