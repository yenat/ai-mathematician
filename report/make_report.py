"""Build the Phase 1 report (.docx). Numbers are read from the result files
where possible, so the document cannot drift from the data.

Usage: python3 make_report.py <out.docx> [categories.json]
  categories.json: theorem -> category, from the translator's per-category
  output files (see megalodon-lean4 sexprinfo-prototype).
"""
import json
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "phase1"))
from docx_writer import Doc  # noqa: E402

R = os.path.join(os.path.dirname(__file__), "..", "results")
out_path = sys.argv[1]
cat_path = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(__file__), "categories.json")


def rows(name):
    return [json.loads(l) for l in open(os.path.join(R, name))]


v1 = {r["goal"]: r for r in rows("phase1_full_v1.jsonl")}
v2 = {r["goal"]: r for r in rows("phase1_full_v2.jsonl")}
v3 = {r["goal"]: r for r in rows("phase1_full_v3.jsonl")}
P1 = {g for g, r in v1.items() if r["proved_by"]}
P2 = {g for g, r in v2.items() if r["proved_by"]}
P3 = {g for g, r in v3.items() if r["proved_by"]}
llm = {r["goal"] for f in ("llm140_gptoss.jsonl", "llm140_deepseek.jsonl")
       for r in rows(f) if r["proved_by"]}
cat = json.load(open(cat_path))
CATS = [("prop_logic", "Propositional logic"), ("set_theory", "Set theory"),
        ("nat_arith", "Natural numbers"), ("ordinals", "Ordinals"),
        ("surreals", "Surreal numbers")]
recheck = rows("recheck_v3.jsonl") if os.path.exists(os.path.join(R, "recheck_v3.jsonl")) else []
rc_ok = sum(r["ok"] for r in recheck)
dsp = rows("llm_dsp.jsonl") if os.path.exists(os.path.join(R, "llm_dsp.jsonl")) else []


def pct(a, b):
    return f"{a / b:.1%}"


first = Counter()
for r in v3.values():
    if r["proved_by"]:
        lbl = r["proved_by"]
        first["induction" if lbl.startswith("induction") else lbl.split("#")[0]] += 1
ind = Counter(r["proved_by"].split(":")[1] for r in v3.values()
              if r["proved_by"] and r["proved_by"].startswith("induction"))
unproved = [r for r in v3.values() if not r["proved_by"]]
secs_p = sorted(r["secs"] for r in v3.values() if r["proved_by"])
secs_f = sorted(r["secs"] for r in unproved)
unproved_vamp = sum(r["vampire"].startswith("Theorem") for r in unproved)

d = Doc("AI Mathematician: Phase 1 Report", "yenat")
d.heading("AI Mathematician — Phase 1 Report", 0)
d.para("Search · ATP (Vampire) · ITP (Lean 4) · LLM proposer, evaluated on the "
       "999-theorem Megalodon reference library. September 2026.")

# ------------------------------------------------------------------ summary
d.heading("1. Summary", 1)
d.bullets([
    f"**{len(P3)} / 999 theorems ({pct(len(P3), 999)}) proved with no LLM**, in "
    "a single run of the integrated pipeline, each theorem held out and proved "
    "only from facts that precede it in the library.",
    f"**{len(P3 | llm)} / 999 ({pct(len(P3 | llm), 999)})** when the "
    f"{len(llm)} proofs found earlier by the LLM feedback loop are included.",
    "Every proof is checked by Lean 4's kernel, with the proof's statement "
    "compared to the original as elaborated terms and a leak guard rejecting any "
    "use of the target or later facts."
    + (f" All {len(recheck)} no-LLM proofs were re-verified in fresh Lean "
       f"processes: {rc_ok} / {len(recheck)} passed." if recheck else ""),
    "Vampire and the LLM are untrusted proposers; only Lean decides.",
    "The LLM informal-proof → formal-outline path is built and runs end to end. "
    + (f"On a fixed sample of {len(dsp)} of the hardest remaining theorems it "
       f"proved {sum(bool(r['proved_by']) for r in dsp)} within a 100-call "
       "budget; Section 6.2 analyses why." if dsp else ""),
    f"Progression over three full runs: {len(P1)} → {len(P2)} → {len(P3)}, "
    "through learned premise selection, automatic induction, strategies "
    "distilled from LLM proofs, using every proof Vampire finds, and a larger "
    "Vampire budget.",
])

# ------------------------------------------------------------------ scope
d.heading("2. Phase 1 scope and status", 1)
d.para("Phase 1 of the design sketch: an LLM proves a lemma and formalizes the "
       "proof, guiding an ITP that checks it with the help of an ATP, fed by "
       "Search + Download. Mapping to what is built:")
d.table([
    ["Sketch component", "Implementation", "Status"],
    ["Search + Download", "Premise selection over the Megalodon library "
     "(symbol overlap, naive Bayes learned from earlier proofs, k-NN, recency)",
     "Done; Download = retrieval from the library (external sources: later)"],
    ["ATP", "Vampire 5.1.0, higher-order TPTP (THF)", "Done"],
    ["ITP", "Lean 4.34.0 over the verified Megalodon→Lean 4 translation "
     "(999/999 theorems)", "Done"],
    ["LLM guiding the ITP", "LLM writes Lean tactic scripts; Lean's errors fed "
     "back for up to 3 rounds", "Done, evaluated (Section 6)"],
    ["LLM proving lemma → formalizing", "Draft–Sketch–Prove: informal proof → "
     "Lean outline with gaps → ATP/ITP tactics fill gaps",
     "Done" + (", evaluated (Section 6)" if dsp else "; evaluation pending")],
], widths=[2200, 4600, 2200])

# ------------------------------------------------------------------ method
d.heading("3. Evaluation setting", 1)
d.para("**Library.** Megalodon's `100thms_12.mg` (1,158 declarations: 999 "
       "theorems, 139 definitions, 13 axioms, 6 primitives, 1 parameter), "
       "exported from Megalodon's checked proof terms and translated to Lean 4. "
       "The translation is verified: all 999 original proofs compile, using only "
       "Megalodon's 17 foundational axioms. No Mathlib; Megalodon's own "
       "higher-order set theory with Church-encoded logic.")
d.para("**Held-out protocol.** Each theorem is attempted in turn with its proof "
       "hidden. The prover may use only declarations with a smaller index "
       "(earlier in the library). Search, premise-selection training and "
       "induction principles are all restricted accordingly.")
d.para("**Acceptance.** A proof counts only if all of the following hold:")
d.numbered([
    "Lean's kernel accepts it.",
    "Its statement is identical to the original theorem's, compared as "
    "elaborated Lean expressions (not text).",
    "The leak guard passes: the transitive closure of constants used by the "
    "proof term (through auxiliary definitions, with theorem bodies unfolded) "
    "contains no library constant at or after the target's index.",
    "No `sorryAx`.",
])
d.para("The compiled library contains all 999 theorems, so without (3) a proof "
       "could cite its own answer or a later equivalent. The guard is tested "
       "both ways: citing the target, or a later theorem with an identical "
       "statement, must be rejected; a genuine proof, or citing an earlier "
       "identical theorem, must be accepted. The first guard version passed "
       "cheating proofs (Lean hides theorem bodies unless asked with "
       "`allowOpaque`); these tests caught it.")

# ------------------------------------------------------------------ pipeline
d.heading("4. Pipeline", 1)
d.code("goal ─► Search ─► earlier facts ─► Vampire (16–128 facts, 30 s)\n"
       "                                     │ proof            │ no proof\n"
       "                                     ▼                  ▼\n"
       "                          facts it used      induction split,\n"
       "                                     │       Vampire per case\n"
       "                                     ▼                  │\n"
       "                   Lean tactic battery ◄────────────────┘\n"
       "                   (kernel + statement check + leak guard)\n"
       "                                     │ all fail\n"
       "                                     ▼\n"
       "                   LLM proposes ─► Lean ─► error back to LLM")
d.heading("4.1 Search (premise selection)", 2)
d.para("Ranks the facts preceding the goal by a sum of: IDF-weighted symbol "
       "overlap (MePo-style); k-NN votes from the dependencies of the most "
       "similar earlier theorems; a recency term; and a naive Bayes score in the "
       "style of MaSh, trained on which facts earlier proofs used, over "
       "statement features that include shape (e.g. conclusion head, "
       "head–argument pairs, hypothesis heads), not only symbols. Name "
       "similarity is deliberately off: a newly conjectured lemma has no "
       "descriptive human name, so using it would inflate the benchmark.")
d.table([
    ["Recall: all facts the original proof cited are in the top k", "old @32",
     "new @32", "old @64", "new @64"],
    ["Second half of library (not used for tuning)", "31.9%", "36.2%", "46.4%", "51.8%"],
    ["327 non-induction theorems Vampire failed on (v1)", "12.2%", "19.6%", "22.6%", "33.0%"],
], widths=[4000, 1250, 1250, 1250, 1250])
d.heading("4.2 ATP: Vampire", 2)
d.para("Goal and ranked facts are rendered as THF; Megalodon's encoded "
       "connectives (`and`, `or`, `iff`, `ex`, Leibniz `eq`, …) map to native "
       "ones, and definitions are included transitively (depth 3). Vampire runs "
       "in portfolio mode for 30 s on the top 16, 32, 64 and 128 facts (v2 "
       "used 5 s on 16/32/64). Its proof is "
       "not reused directly: the facts it used become the premise hints for "
       "Lean. Vampire proofs are not unique, and the facts of one proof may suit "
       "Lean better than another's, so every distinct premise set is kept.")
d.heading("4.3 ITP: Lean reconstruction", 2)
d.para("Kernel-checked bridge lemmas (`b_and`, `b_or`, `b_ex`, `b_eq`, …) turn "
       "the encoded logic into Lean's native logic so `grind` applies. A "
       "deterministic battery of tactic scripts is built from the hints: intro/"
       "unfold then `grind`; premises introduced as hypotheses then `grind`; "
       "`solve_by_elim`; unfolding only the goal's own definitions; set "
       "extensionality. The last two were distilled from the proofs the LLM "
       "found in v1. If the whole battery fails, a slower second line runs "
       "(v3): premises as `grind` e-matching lemmas, higher `grind` effort, and "
       "`simp_all` with premises and definitions.")
d.table([["Strategy (first success)", "Theorems"]] +
        [[k, str(v)] for k, v in first.most_common()], widths=[4500, 2000])
d.heading("4.4 Automatic induction", 2)
d.para("Vampire does not invent induction predicates: given exactly the facts "
       "the original proof cited, it proved only 2 of 40 sampled induction "
       "theorems. When Vampire finds no proof, the pipeline reads the goal as "
       "P(x) for each variable x with a matching guard, instantiates each "
       "available principle (nat_ind, nat_complete_ind, ordinal_ind, "
       "SNoLev_ind, finite_ind, In_ind; only those proved before the goal), and "
       "sends each case to Vampire separately. In Lean: introduce, revert all "
       "but x and its guard, `apply` the principle (the motive is found by "
       "higher-order pattern unification), and prove each case with the "
       "battery. Each case is first tried as its own declaration, since Lean's "
       "heartbeat budget is per declaration.")
d.para(f"In the full run, induction proved {sum(ind.values())} theorems "
       f"({', '.join(f'{k} {v}' for k, v in ind.most_common())}), including "
       "commutativity of addition and of multiplication and associativity of "
       "addition on the naturals.")

# ------------------------------------------------------------------ results
d.heading("5. Results without an LLM", 1)
d.table([
    ["Run", "Proved", "Rate"],
    ["v1: Search (overlap, k-NN, recency) + Vampire + battery", str(len(P1)), pct(len(P1), 999)],
    ["v2: + learned Search, induction, distilled strategies, all Vampire proofs",
     str(len(P2)), pct(len(P2), 999)],
    ["**v3: + Vampire 30 s with a 128-fact slice, second-line Lean strategies**",
     f"**{len(P3)}**", f"**{pct(len(P3), 999)}**"],
], widths=[6000, 1500, 1500])
rows_c = [["Category", "Theorems", "v1", "v2", "v3"]]
for c, label in CATS:
    tot = sum(1 for g in cat if cat[g] == c)
    cells = [label, str(tot)]
    for P in (P1, P2, P3):
        a = sum(1 for g in cat if cat[g] == c and g in P)
        cells.append(f"{a} ({a / tot:.0%})")
    rows_c.append(cells)
d.table(rows_c, widths=[2600, 1300, 1700, 1700, 1700])
d.caption("Categories from the translator's vocabulary heuristic; approximate.")
d.para(f"v2 against v1: {len(P2 - P1)} theorems gained, {len(P1 - P2)} lost. "
       f"v3 against v2: {len(P3 - P2)} gained, {len(P2 - P3)} lost. The losses are "
       "borderline goals where Vampire found a different proof, or none within "
       "its time limit; the pipeline has run-to-run variation on such goals.")
d.para(f"Unproved: {len(unproved)}. For {unproved_vamp} of them Vampire found a "
       f"proof that the Lean battery could not rebuild; for "
       f"{len(unproved) - unproved_vamp} Vampire found none.")
d.para("**How v3 was chosen.** Two targeted experiments on the v2 failures, "
       "before the v3 run: (1) on the 395 goals with no Vampire proof, Vampire "
       "with 30 s and a 128-fact slice found 66 proofs (most only at 128 facts), "
       "of which Lean rebuilt 32; a larger budget for the induction cases helped "
       "little (1 of 42 sampled). (2) On the 90 goals with a Vampire proof but no "
       "reconstruction, the second-line strategies rebuilt 6. Both were then "
       "built into the pipeline and measured by the single v3 run above.")
d.para("The typical remaining reconstruction failure needs a higher-order "
       "instance of a premise (e.g. the choice axiom `Eps_i_ax` at a specific "
       "predicate), which Vampire finds and `grind` does not.")
d.para(f"**Time per goal** (one goal at a time, as in use): in v3, proved goals "
       f"take a median of {secs_p[len(secs_p) // 2]:.0f} s, 90% within "
       f"{secs_p[int(len(secs_p) * .9)]:.0f} s; unproved goals are abandoned after a "
       f"median of {secs_f[len(secs_f) // 2]:.0f} s. The larger Vampire budget is the "
       "price of v3's gain (v2: 25 s and 85 s).")

# ------------------------------------------------------------------ LLM
d.heading("6. LLM as an untrusted proposer", 1)
d.para("The LLM sees the goal, Lean's goal state, the definitions used and the "
       "selected earlier facts, never the original proof or anything after the "
       "goal. Everything it writes goes through the same acceptance checks. "
       "Models are served through an OpenAI-compatible endpoint.")
d.heading("6.1 Direct Lean with error feedback (v1)", 2)
d.para("Target: the 140 theorems where Vampire found a proof but the v1 battery "
       "could not rebuild it, with the same Vampire premise sets for every "
       "model. Up to 3 rounds, Lean's error returned each round.")
d.table([
    ["Model (28-theorem sample)", "Proved", "Avg time / theorem"],
    ["deepseek/deepseek-v4-flash", "11 / 28", "127 s"],
    ["openai/gpt-oss-120b", "9 / 28", "46 s"],
    ["minimax/minimax-m3", "7 / 28", "496 s (10 API timeouts)"],
    ["qwen/qwen3.8-27b", "2 / 28", "550 s (26 API timeouts; inconclusive)"],
], widths=[4000, 1800, 3200])
d.para(f"Cascade on all 140: gpt-oss-120b proved 41, then deepseek-v4-flash 10 "
       f"of the remaining 99: **51 / 140 (36%)**, all re-verified in fresh Lean "
       f"runs. {len(llm & P3)} of these 51 are now proved by v3 without an LLM, "
       "because the strategies distilled from them generalise.")
d.heading("6.2 Draft, sketch, prove", 2)
d.para("The sketch's \"LLM proving lemma → LLM formalizing proof\" path, in the "
       "style of Draft, Sketch, and Prove (Jiang et al., ICLR 2023):")
d.numbered([
    "**Draft** (1 call): the model writes an informal numbered proof, naming "
    "the facts each step uses and, for induction, the principle and predicate.",
    "**Sketch** (1 call): it formalizes that proof as a Lean outline of "
    "intermediate `have` steps, leaving any routine step as `sorry`.",
    "**Prove** (no LLM): each `sorry` is replaced by the automatic tactics "
    "(`grind`, `solve_by_elim` over the selected facts); Lean checks the whole.",
    "**Repair** (1 call): on failure, Lean's error goes back once; the model "
    "revises the outline. A script rejected only because it continues after "
    "the goal is closed is retried with trailing lines removed (no call).",
])
if dsp:
    from llm import usage_summary
    won = [r for r in dsp if r["proved_by"]]
    u = usage_summary(os.path.join(R, "llm_usage_dsp.jsonl"))
    d.para(f"**Budgeted run.** Hard cap of 100 calls on gpt-oss-120b. Sample: "
           f"every 15th of the {sum(1 for r in v2.values() if not r['proved_by'])} theorems the v2 pipeline did not "
           f"prove (33 theorems, not hand-picked). The first was a live test; "
           f"it failed on a script that continued after the proof was complete, "
           f"which motivated the trimming step. Its stored reply passes after "
           f"trimming but is **not counted**. The remaining {len(dsp)} were run "
           f"with the final code.")
    d.para(f"**Result: {len(won)} / {len(dsp)} proved** "
           f"({pct(len(won), len(dsp))}) under the same acceptance checks as "
           f"every other proof. API usage for the whole pass: {u['calls']} calls, "
           f"{u['prompt_tokens']:,} prompt and {u['completion_tokens']:,} "
           f"completion tokens.")
    d.table([["Final failure reason", "Theorems"],
             ["Lean heartbeat budget exhausted while filling gaps", "13"],
             ["Encoded logic / opaque sets treated as Lean-native", "11"],
             ["Type mismatch", "3"],
             ["Wrong number of intro steps", "2"],
             ["Other", "3"]], widths=[6000, 2000])
    d.para("**Post-hoc check (no API calls).** All 64 stored outlines were "
           "re-checked with 5× the heartbeat budget: 0 / 64 pass, and the same "
           "20 time out at the same points. The gaps the model leaves are too "
           "coarse for the automatic tactics, rather than cut short by the budget.")
    d.para("**Reading.** The path works end to end, but on this hard remainder "
           "(only 4 of the 32 had a Vampire proof) a general-purpose model with 3 "
           "calls does not produce usable outlines in Megalodon's encoding. The "
           "clearest levers: few-shot examples drawn from the 51 successful "
           f"direct-mode proofs and the {len(P3)} pipeline proofs, finer outlines (more, "
           "smaller `have` steps), and per-gap checking so that each gap is "
           "reported back to the model individually.")
    if won:
        d.table([["Theorem proved", "Round", "Gaps filled by automation"]] +
                [[f"`{r['goal']}`", r["proved_by"].replace("dsp-r", ""),
                  str(next(t.get("gaps", 0) for t in r["transcript"] if t.get("ok")))]
                 for r in won], widths=[4500, 1500, 3000])
else:
    d.para("[Results of the budgeted run to be added.]")

# ------------------------------------------------------------------ limits
d.heading("7. Limitations", 1)
d.bullets([
    "One library (999 theorems) in one foundation; results may not transfer "
    "unchanged to other libraries or to Mathlib-style Lean.",
    "Download is retrieval from this library only; no external sources yet.",
    "Run-to-run variation on borderline goals (Vampire's time limit): "
    f"{len(P2 - P3)} v2 successes were not reproduced in v3.",
    "Category figures use a vocabulary heuristic.",
    "LLM results come from a small budget and are estimates.",
    "Speed was not optimised: each Lean check starts a fresh process and "
    "reloads the library, and a batch finishes every candidate even after one "
    "succeeds.",
])

# ------------------------------------------------------------------ next
d.heading("8. Next steps", 1)
d.numbered([
    f"Phase 1 remainder: the {unproved_vamp} goals with a Vampire proof Lean "
    "still cannot rebuild, mostly needing higher-order instances: replay "
    "Vampire's instantiations from its proof, or give them to the LLM as a "
    "hint; richer induction (generalising the goal, "
    "strengthening the predicate).",
    "Speed: a persistent Lean server, stopping at the first success, and "
    "parallel candidates per goal.",
    "Phase 2: inference controller (LLM + Hyperon) and the Math Atomspace; "
    "proved lemmas enter long-term memory, so they are retrieved rather than "
    "re-proved, and research papers feed long-term memory.",
    "Phase 3: PLN feeding the inference controller.",
])

# ------------------------------------------------------------------ appendix
d.heading("Appendix: reproducing", 1)
d.code("cd phase1\n"
       "python3 test_guard.py                                 # leak-guard controls\n"
       "python3 experiment.py 1 6 ../results/phase1_full_v3.jsonl   # full run\n"
       "python3 recheck_full.py ../results/phase1_full_v3.jsonl 6 ../results/recheck_v3.jsonl")
d.para("Repositories: ai-mathematician (this system) and megalodon-lean4 (the "
       "verified Megalodon → Lean 4 translator).")

d.save(out_path)
print("wrote", out_path)
