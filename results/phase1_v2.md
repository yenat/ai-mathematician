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

## Next

1. Induction without the LLM: apply the principle, then prove the cases.
2. The 17 Vampire proofs Lean could not rebuild (`results/rebuild_nb.log`).
3. One full 999 rerun with everything combined.
4. One budgeted LLM pass on what remains, with token logging and a cap.
