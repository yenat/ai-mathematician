# AI Mathematician

A system for proving mathematical lemmas by combining automated search,
automated theorem proving, language models, and a proof checker, where
**nothing counts as proved unless Lean 4's kernel accepts it.**

Built phase by phase:

| Phase | Components | Status |
|---|---|---|
| 1 | Search + Download · ATP (Vampire) · ITP (Lean 4) · LLM proposer with Lean-error feedback | Deterministic pipeline done and benchmarked; LLM plug-in in progress |
| 2 | Inference controller (LLM + Hyperon) · Math Atomspace working memory / long-term memory · research papers → long-term memory | Not started |
| 3 | PLN (probabilistic logic networks) feeding the inference controller | Not started |

## Phase 1 result

On the 999-theorem reference library (Megalodon's `100thms_12.mg`,
translated to Lean 4 by the companion
[megalodon-lean4](https://github.com/yenat/megalodon-lean4) translator), with **no LLM**:

**418 / 999 theorems proved (41.8%)**, every one kernel-checked.

Full breakdown and failure analysis: `results/phase1_baseline_v1.md`.

### What "proved" means here

Each theorem is held out in turn. The prover sees only its statement plus
declarations that come *before* it in the library. A proof counts only if:

1. Lean 4's kernel accepts it;
2. its statement is identical to the original theorem's (compared as
   elaborated Lean expressions, not text);
3. the **leak guard** confirms the proof term uses no library fact at or
   after the target. The compiled library contains all 999 theorems, so
   without this a proof could quietly cite the answer.

The guard is itself tested in both directions (`phase1/test_guard.py`):
citing the target, or a later theorem with the same statement, must be
rejected; a genuine proof, or citing an earlier identical theorem, must be
accepted. The first version of the guard passed cheating proofs; these
tests caught it.

Vampire and the LLM are **untrusted**: they only propose. Lean decides.

## How it works (Phase 1)

```
goal ──> Search ──> ranked facts ──> Vampire (untrusted) ──> premises that worked
                                                                  │
                        LLM (untrusted, optional) ── proposes ────┤
                                  ▲                               ▼
                                  └── Lean's error ◄── Lean 4 (trusted) + statement check + leak guard
```

- `phase1/library.py`: loads every declaration from Megalodon's typed
  export, in order, with the symbols each mentions.
- `phase1/search.py`: ranks earlier facts for a goal (rare shared
  concepts, what similar earlier proofs used, recency). No LLM.
- `phase1/atp.py`: goal + facts → higher-order TPTP → Vampire, tried at
  several premise-slice sizes. Megalodon's encoded logic is mapped to
  native connectives for Vampire.
- `lib/Bridge.lean`: kernel-checked lemmas converting Megalodon's encoded
  logic (`and`, `or`, `ex`, Leibniz `eq`, …) to Lean's native logic, so
  Lean's `grind` automation can work on it.
- `phase1/itp.py`, `phase1/prover.py`: build Lean proof attempts, check
  them, apply the statement check and leak guard.
- `phase1/llm.py`: **experimental.** LLM proposes a Lean tactic script,
  sees Lean's error on failure, retries (the feedback loop from the design
  sketch).

## Setup

Requires Python 3.8+ (standard library only), Lean 4.34.0, and Vampire.

```bash
# 1. Vampire 5.1.0 (prebuilt binary)
mkdir -p tools data && cd tools
wget https://github.com/vprover/vampire/releases/download/v5.1.0/vampire-Linux-X64.zip
unzip vampire-Linux-X64.zip && chmod +x vampire && cd ..

# 2. Library data: Megalodon's typed export of the reference corpus,
#    produced by the patched Megalodon in megalodon-lean4's
#    sexprinfo-prototype/ (see its README):
#      megalodon -sexprinfo 100thms_12.mg > data/corpus.sexpr

# 3. Compile the Lean library once (a few minutes)
cd lib
lean --root=. -o MegLib.olean MegLib.lean
LEAN_PATH=. lean -o Bridge.olean Bridge.lean
cd ..
```

Set `LEAN_BIN` if `lean` isn't at the default path in `phase1/itp.py`.

For the LLM plug-in only: create `.env` in the repo root (git-ignored)
with `LLM_API_KEY=...` and `LLM_BASE_URL=...` (an OpenAI-compatible
endpoint).

## Running

```bash
cd phase1
python3 test_guard.py                 # leak-guard controls: must all pass
python3 search.py ../data/corpus.sexpr   # Search recall vs. real proofs
python3 experiment.py 33 6 out.jsonl  # sample: every 33rd theorem, 6 workers
python3 experiment.py 1 6 out.jsonl   # full benchmark (~3h on 6 workers)
python3 try_llm.py <thm1,thm2> openai/gpt-oss-120b 4   # LLM loop, experimental
```

## Known limits

- The library uses Megalodon's own foundations inside Lean (no Mathlib),
  so Lean's automation only works well after the bridge rewrite.
- 140 theorems have a Vampire proof that Lean did not rebuild; 441 have
  none. Induction-style proofs, which need an invented induction
  predicate, are the hardest remaining class.
- Category percentages use a vocabulary heuristic and are approximate.
