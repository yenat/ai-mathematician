# Phase 2: MeTTa drives Lean

Phase 1 proved theorems with a fixed pipeline: rank premises, call Vampire,
try tactics, ask a language model. Phase 2 turns the search itself into a
MeTTa program. **MeTTa decides every proof step; Lean checks every step;
only a fresh Lean check of the finished proof counts.**

The program runs on CeTTa, a C runtime for MeTTa, and no Python runs while
it searches.

```
              ┌──────────── controller.metta ─────────────┐
              │  depth-first search over Lean tactic steps │
   goal ────► │  which step to try, in which order,        │
              │  and when to give up on a branch            │
              └──────▲──────────────────────┬──────────────┘
                     │ goal as a MeTTa atom  │ one tactic
                     │                       ▼
   memory ──────►  host.metta ─── lean.metta ─── Lean REPL
   (every library           (13 operations)   (stream process:
    lemma as an atom)                          new goals or an error)

   finished script ──► proof guard: a fresh Lean run checks the
                       statement, no sorry, nothing cited from after
                       the theorem
```

## Design choices, and why

**MeTTa chooses, Lean judges.** A search program that also decided what
counts as proved could fool itself. Here MeTTa only proposes steps; Lean
runs each one and reports the new goals or an error. A wrong guess costs
one Lean call (about a millisecond), never a wrong theorem.

**Goals and lemmas are atoms in the same vocabulary.** Lean prints each
goal as an S-expression (`Sexpr.lean`), with constants named as in the
library and bound variables named by depth. A lemma's conclusion is stored
with its variables as MeTTa variables:

```
(Lemma Subq_tra 71 2 (Subq $V0 $V2))       ; A ⊆ B, B ⊆ C ⊢ A ⊆ C
```

so finding "every lemma that could close this goal" is a single MeTTa
`match`. Retrieval is the language's own unification, not a separate index.

**Only earlier lemmas.** Every lemma carries its position in the library,
and the search only uses lemmas that come before the theorem being proved.
The guard enforces the same rule again on the finished proof, so a leak in
the search cannot become an accepted proof.

**Cheap steps first.** For each goal the controller tries, in order:

| | Step | Why here |
|---|---|---|
| 0 | introduce `∀ x` / `A →` | never a wrong move, so it costs no choice |
| 1 | a hypothesis that matches the goal | closes it immediately when it applies |
| 2 | one finishing tactic (`grind`) | one call settles many easy goals |
| 3 | forward: a one-hypothesis lemma applied to a hypothesis | adds facts the goal may need |
| 4 | `apply L` for lemmas whose conclusion matches | the main backward step, best-ranked first |
| 5 | an equivalence `P ↔ Q` from the library | rewrites the goal into a provable form |
| 6 | unfold the definition at the head of the goal | when no lemma fits, look inside |
| 7 | stronger finishing tactics, with the top-ranked premises | expensive, so last |

Lemmas are ordered by the Phase 1 premise ranking, because Phase 1's main
lesson was that the right premises matter more than anything else.

**Bounded search.** A depth bound (choice steps per branch), a budget of
Lean steps and a time limit per theorem keep one hard theorem from eating
the run. A branch also stops when it returns to a goal it has already seen
on the same path, or derives the same fact twice: neither can make progress.
A Lean step that gives no answer in 30 s ends the theorem, and its Lean
process is killed rather than waited for, so one stuck tactic cannot hold
up the run.

**One Lean process per theorem.** Proof states are cheap to keep and branch
from inside one REPL, so backtracking is free; a fresh process per theorem
keeps one theorem's state from affecting the next.

## Why CeTTa

The controller was first built on Hyperon 0.2.6 (its Python package). The
same tasks were then run on CeTTa, on this machine and on this library:

| Task | Hyperon 0.2.6 | CeTTa | Same answers |
|---|---|---|---|
| Lemma retrieval: every lemma's conclusion as a goal (958 queries) | 33.6 s | 0.37 s | 958 / 958 |
| Checking proof terms in MeTTa (39 cases, 10 correct, 29 broken) | 20.7 s | 0.21 s | 39 / 39, both agree with Lean |
| Proving 19 sample theorems (300 Lean steps, 120 s each) | 6 proved, 1,825 s | 8 proved, 615 s | 19 / 19 identical step choices (unfolding off) |

Reasons for the choice:

- **Speed where the time goes.** On Hyperon, a profiled search spent nearly
  all its time in the interpreter, not in Lean: a Lean step takes
  milliseconds. A faster interpreter therefore means more steps inside the
  same time limit, which is what finds proofs.
- **Same results.** Retrieval and checking gave identical answers, so the
  speed is not bought with different behaviour.
- **It runs our memory.** Hyperon 0.2.8–0.2.10 crash when loading this
  memory; 0.2.6 works but is the slow one.
- **No Python layer.** CeTTa starts Lean as a stream process from MeTTa
  itself, so the search loop has nothing outside MeTTa and Lean.
- **Phase 1 already runs on it.** A MeTTa port of Phase 1 exists for CeTTa,
  and Phase 2 reuses two of its pieces instead of rewriting them: the
  premise ranking (same order as Phase 1's Python, checked on seven
  theorems) and the proof guard.

Not measured: Hyperon's standalone Rust runner without Python, and Hyperon
releases after 0.2.10.

**Is it the same search?** To check, the CeTTa version was run once with
unfolding switched off, as it effectively was on Hyperon (see below). On
all 19 theorems it tried exactly the same steps, in the same order, up to
the point where Hyperon stopped. The only difference is how far each gets
in the time allowed: Hyperon stopped after 29 to 99 steps on the hard
theorems; CeTTa usually reached the 300-step limit, and that extra reach
alone proved one more theorem (`add_nat_0R`, 197 steps in under 5 s).

With unfolding on, CeTTa proves 8 of the 19 (Hyperon: 6). Every one of the
8 was accepted by the proof guard. Many unproved theorems now stop at the
step limit, not the time limit, so the step budget is now the cheaper
setting to raise.

Porting exposed two differences in behaviour:

- On Hyperon, step 6 (unfolding) never fired: the goal is declared as an
  unevaluated `Atom`, so the head of the goal was never computed. On CeTTa
  the step works as written.
- Forward steps (step 3) use each lemma once, on the first hypothesis it
  matches, and the order of hypotheses was left to the runtime. It is now
  explicit: newest hypothesis first, because applying a lemma to an old
  hypothesis again mostly re-derives a fact already known.

## Files

| File | Role |
|---|---|
| `cetta/controller.metta` | the search and the order of candidate steps |
| `cetta/host.metta` | the 13 operations the controller calls: read the goal, try a tactic, build candidate tactics, rank lemmas, track the budget and the path |
| `cetta/lean.metta` | the Lean REPL as a CeTTa stream process: open, step, read replies |
| `cetta/prove.metta` | runs theorems, checks each finished proof with the guard, writes one JSON line per theorem |
| `cetta/prepare.py` | run once: writes the memory and statements as `cetta/data/library.metta` and the goal printer as `cetta/data/sexpr.lean` |
| `ltm.py` | builds the memory atoms (used by `prepare.py`) |
| `Sexpr.lean` | prints Lean goals and library statements as MeTTa atoms |

## Running

Needs:

- CeTTa (built at `~/cetta-demo/cetta2`, commit `2c6dc292`),
- the Phase 1 MeTTa port (`cetta` branch, checked out at
  `~/cetta-demo/repo`, with its Lean guard prepared:
  `make prepare-cetta-itp-native`),
- the Lean REPL built in `tools/repl`:

```bash
git clone https://github.com/leanprover-community/repl tools/repl
cd tools/repl && git checkout 193cf4b && lake build && cd ../..
```

Then, once:

```bash
cd phase2/cetta
python3 prepare.py        # writes data/
```

and to prove theorems:

```bash
export CETTA_ITP_RUNTIME=native PATH=$HOME/lean4-toolchain/lean-4.34.0-linux/bin:$PATH
~/cetta-demo/cetta2/cetta --lang petta@1.0.6 prove.metta andI,SingI,EmptyE results/out.jsonl
```

Optional arguments after the output file: depth (default 4), Lean steps
(300) and seconds (120) per theorem. Each output line has the script, the
guard's verdict and the full trace of steps tried.

## Next

The controller has no step yet for splitting a proof into cases or for
proposing a witness (a value for an `∃`). Theorems such as the division
theorem for integers (`quotient_remainder_int`) need both. After those, the
same search will take hints from an external proof graph at the points
where it gets stuck, and the result will be compared with the unguided
search on the same theorems.
