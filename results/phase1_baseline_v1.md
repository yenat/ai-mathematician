# Phase 1 baseline v1 — deterministic pipeline, no LLM

Run: 2026-09-24, `phase1/experiment.py 1 6`, all 999 theorems of the
reference library (`100thms_12.mg`, via the Megalodon→Lean 4 translator).

Setting: each theorem is held out in turn. The prover sees only its
statement plus declarations that come *before* it in source order.
A theorem counts as proved only if Lean's kernel accepts the proof, the
proof's statement is identical to the original's (compared as elaborated
Lean expressions), and the leak guard confirms the proof term uses no
library constant at or after the target (`phase1/test_guard.py` checks
the guard itself in both directions).

## Result

**418 / 999 proved (41.8%)**, wall time 2h53m on 6 workers.

| Category | Proved | Rate |
|---|---|---|
| Propositional logic | 37 / 41 | 90% |
| Set theory | 96 / 185 | 52% |
| Natural numbers | 48 / 129 | 37% |
| Ordinals | 30 / 43 | 70% |
| Surreal numbers | 207 / 601 | 34% |

(Categories from the vocabulary heuristic shared with the translator;
approximate, as documented there.)

## Where it fails

- Vampire found a proof for 558 theorems; Lean reconstructed 418 of those
  (75%). The other 140 are reconstruction failures with known-good premise
  sets — the cheapest remaining target.
- Vampire found no proof for 441. On a 31-theorem sample, giving Vampire
  exactly the original proof's premises rescued 12 of 20 failures (so
  Search ranking is a real lever); the other 8 failed even then, mostly
  induction-style proofs needing an invented induction predicate.

## Strategy usage (a theorem can succeed under several)

prem-grind 226, prem-unfold-grind 193, solve_by_elim 117,
unfold-grind 80, intro-grind 33.

Per-theorem records: `phase1_full_v1.jsonl` (not committed; regenerate).
