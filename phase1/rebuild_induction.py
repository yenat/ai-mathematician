"""Lean reconstruction of induction splits found by try_induction.py:
apply the principle Vampire's split used, then prove each case with the
deterministic battery built from that case's Vampire premises. Same
checks as everything else (kernel, statement identity, leak guard).

Usage: python3 rebuild_induction.py <splits.jsonl> <workers> <out.jsonl> [--limit N]
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics
from induction import lean_script

CORPUS = "../data/corpus.sexpr"
src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
todo = [r for r in map(json.loads, open(src)) if r["principle"]][:limit]
print(f"{len(todo)} splits", flush=True)


def prefix_len(stmt):
    n = 0
    while isinstance(stmt, list) and stmt[0] in ("ALL", "IMP"):
        n += 1
        stmt = stmt[2]
    return n


def run(r):
    """Two passes. Lean's heartbeat budget is per declaration, so trying
    every tactic for every case inside ONE proof lets a slow failing
    attempt starve the rest. Pass 1 therefore tries each (case, tactic)
    as its own declaration, with the other cases left as `sorry`; an
    attempt whose only defect is sorryAx has closed its case. Pass 2
    assembles one winner per case into a single sorry-free proof, which
    gets the full check."""
    g = by[r["goal"]]
    gdefs = prover.goal_defs(g)
    n, args = prefix_len(g.stmt), (r["x"], r["guard"], r["principle"])
    case_tacs = [[s for _, s in candidate_tactics(p, gdefs, gdefs)]
                 for p in r["case_premises"]]
    t0 = time.time()
    probes = []
    for k, tacs in enumerate(case_tacs):
        for i, t in enumerate(tacs):
            per_case = [["sorry"]] * len(case_tacs)
            per_case = per_case[:k] + [[t]] + per_case[k + 1:]
            probes.append((f"{k}:{i}", lean_script(n, *args, per_case)))
    res = prover.attempt_batch(g, probes, timeout=600, single_timeout=120)
    closes = {lbl for lbl, ok, why in res if ok or why == "sorryAx"}
    winners = []
    for k, tacs in enumerate(case_tacs):
        i = next((i for i in range(len(tacs)) if f"{k}:{i}" in closes), None)
        if i is None:
            return {"goal": g.name, "principle": r["principle"],
                    "proved_by": None, "why": f"no tactic closes case {k}",
                    "secs": round(time.time() - t0, 1)}
        winners.append([tacs[i]])
    script = lean_script(n, *args, winners)
    (_, ok, why), = prover.attempt_batch(g, [("induction", script)],
                                         timeout=300, single_timeout=300)
    return {"goal": g.name, "principle": r["principle"],
            "proved_by": "induction" if ok else None, "why": why,
            "script": script, "secs": round(time.time() - t0, 1)}


won = 0
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += bool(r["proved_by"])
        fh.write(json.dumps(r) + "\n")
        print(f"{'PROVED' if r['proved_by'] else 'failed':7s} {r['goal'][:40]:40s} "
              f"{r['principle']} ({r['secs']}s)", flush=True)
        if not r["proved_by"]:
            print("   ", r["why"][:300].replace("\n", " | "), flush=True)
print(f"\nLean proved {won}/{len(todo)}")
