# AI Mathematician

A system for proving mathematical lemmas by combining automated search,
automated theorem proving, language models, and a proof checker, where
**nothing counts as proved unless Lean 4's kernel accepts it.**

Built phase by phase:

| Phase | Components | Status |
|---|---|---|
| 1 | Search + Download · ATP (Vampire) · ITP (Lean 4) · LLM proposer with Lean-error feedback · LLM informal proof → formal outline | Built and benchmarked; Download = retrieval from the library (external sources later) |
| 2 | Inference controller (LLM + Hyperon) · Math Atomspace working memory / long-term memory · research papers → long-term memory | Not started |
| 3 | PLN (probabilistic logic networks) feeding the inference controller | Not started |

## Phase 1 result

On the 999-theorem reference library (Megalodon's `100thms_12.mg`,
translated to Lean 4 by the companion
[megalodon-lean4](https://github.com/yenat/megalodon-lean4) translator):

| | Proved | Rate |
|---|---|---|
| v1 full run, no LLM | 418 / 999 | 41.8% |
| v1 + LLM feedback loop on reconstruction failures | 469 / 999 | 46.9% |
| v2 full run, no LLM (learned Search, distilled strategies, all Vampire proofs, automatic induction) | 514 / 999 | 51.5% |
| v3 full run, no LLM (+ Vampire 30 s with a 128-fact slice, second-line Lean strategies) | 563 / 999 | 56.4% |
| v3 + the v1 LLM proofs | 584 / 999 | 58.5% |
| **v4 full run, no LLM** (+ Duper as a fourth proof line, 256/512-fact slices, `apply` strategies) | **640 / 999** | **64.1%** |

Every one kernel-checked; **all 640 v4 proofs were re-verified independently
in fresh Lean runs (`recheck_v4.jsonl`: 640 / 640)**, as were the 563 v3
proofs and the 51 LLM-found proofs.

Where v4's +77 came from, by proof line (v4 vs v3):

| line | v4 | v3 | change |
|---|---:|---:|---:|
| `duper` (Lean-native superposition) | 44 | 0 | **+44** |
| `prem-grind` | 302 | 287 | +15 |
| `prem-unfold-grind` | 133 | 122 | +11 |
| `apply` | 7 | 0 | +7 |
| `solve_by_elim` | 40 | 37 | +3 |
| others | — | — | −3 net |

The single largest gain is Duper, a classical symbolic prover with no
machine learning in it. Across the five pipeline stages the LLM contributed
least: the informal→formal pass (`dsp.py`) returned 1 / 32 on the hardest
residual goals, and a zero-cost recheck at 1M heartbeats confirmed those
were not timeouts. The run cost 79 core-hours. Details: `results/phase1_baseline_v1.md` (baseline, failure
analysis), `results/phase1_llm_v1.md` (model comparison, cascade) 
`results/phase1_v2.md` (v2 and v3 runs), `results/phase1_llm_dsp.md` (LLM
informal→formal pass). Phase 1 report: `report/Phase1_Report_DRAFT.docx`.

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
- `phase1/llm.py`: LLM proposes a Lean tactic script, sees Lean's
  error on failure, retries (the feedback loop from the design sketch).
  `llm_experiment.py` runs it over a results file; `recheck.py`
  independently re-verifies every LLM-found proof.

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

```bash
# 4. Optional: Duper (Lean-native superposition prover used to rebuild
#    Vampire proofs that grind cannot; the prover uses it when present)
mkdir -p tools/duper-env && cd tools/duper-env
echo 'leanprover/lean4:v4.34.0' > lean-toolchain
printf 'name = "duperenv"\n\n[[require]]\nname = "Duper"\ngit = "https://github.com/leanprover-community/duper.git"\nrev = "v4.34.0"\n' > lakefile.toml
lake update && lake build Duper
# lean-auto downloads the zipperposition binary with curl during the build;
# without curl, place zipperposition.exe in .lake/packages/auto/.lake/build/
cd ../..
```

For the LLM plug-in only: create `.env` in the repo root (git-ignored)
with `LLM_API_KEY=...` and `LLM_BASE_URL=...` (an OpenAI-compatible
endpoint).

## Running

```bash
cd phase1
python3 test_guard.py                 # leak-guard controls: must all pass
python3 search.py ../data/corpus.sexpr   # Search recall vs. real proofs
python3 experiment.py 33 6 out.jsonl  # sample: every 33rd theorem, 6 workers
python3 experiment.py 1 6 out.jsonl   # full benchmark (~7h on 6 workers)
python3 try_llm.py <thm1,thm2> openai/gpt-oss-120b 4   # LLM loop, experimental
```

## Known limits

- The library uses Megalodon's own foundations inside Lean (no Mathlib),
  so Lean's automation only works well after the bridge rewrite.
- In the v3 run, 115 unproved theorems have a Vampire proof that Lean did
  not rebuild (mostly needing higher-order premise instances); 321 have
  none. Borderline goals vary between runs because of Vampire's time limit
  (8 v2 successes were not reproduced in v3).
- Category percentages use a vocabulary heuristic and are approximate.
