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

## Next

1. Better Search: a learned ranker trained on which facts earlier proofs
   used (MaSh-style, strictly earlier theorems only), measured by recall
   and oracle-style Vampire checks. Embeddings only if that falls short.
2. Induction without the LLM: apply the principle, then prove the cases.
3. One full 999 rerun with everything combined.
4. One budgeted LLM pass on what remains, with token logging and a cap.
