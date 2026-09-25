"""Measure the induction split with Vampire alone (no Lean, no LLM) on the
induction theorems where Vampire found no proof.

  --oracle : premises = facts the ORIGINAL proof cited (minus induction
             principles). A ceiling, not a result: tells whether the split
             itself is the right idea.
  default  : premises from Search, as the real pipeline would use.

Usage: python3 try_induction.py <baseline.jsonl> <workers> <out.jsonl> [--oracle]
"""
import json
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from atp import THF, attach_prim_indices, run_vampire, Unsupported
from search import Search
from induction import Inductor

CORPUS = "../data/corpus.sexpr"
IND = re.compile(r"_ind$|_ind_|induction")
base, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
oracle = "--oracle" in sys.argv
decls = load(CORPUS)
by = {d.name: d for d in decls}
thf = THF(decls)
attach_prim_indices(thf, CORPUS)
search = Search(decls)
ind = Inductor(decls)

rows = [json.loads(l) for l in open(base)]
todo = [by[r["goal"]] for r in rows
        if not r["proved_by"] and not r["vampire"].startswith("Theorem")
        and any(IND.search(p) for p in by[r["goal"]].proof_deps)]
print(f"{len(todo)} induction theorems, oracle={oracle}", flush=True)


def prove_case(case, ranked, slices, timeout=5):
    for k in slices:
        try:
            text, ids, _ = thf.problem(case, ranked[:k])
        except Unsupported:
            return None
        status, used = run_vampire(text, timeout=timeout)
        if status == "Theorem":
            return [ids[u] for u in used if u in ids]
    return None


def run(g):
    if oracle:
        ranked = sorted(p for p in g.proof_deps if not IND.search(p))
        slices = (len(ranked),)
    else:
        ranked = [n for n, _ in search.rank(g.index, limit=64)]
        slices = (16, 32, 64)
    t0 = time.time()
    tried = []
    for pname, xi, gi, cases in ind.splits(g):
        used = []
        for c in cases:
            u = prove_case(c, ranked, slices)
            if u is None:
                break
            used.append(u)
        tried.append(pname)
        if len(used) == len(cases):
            return {"goal": g.name, "principle": pname, "x": xi, "guard": gi,
                    "case_premises": used, "secs": round(time.time() - t0, 1)}
    return {"goal": g.name, "principle": None, "tried": tried,
            "secs": round(time.time() - t0, 1)}


won = 0
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for r in ex.map(run, todo):
        won += bool(r["principle"])
        fh.write(json.dumps(r) + "\n")
        print(f"{'SPLIT' if r['principle'] else 'failed':7s} {r['goal'][:40]:40s} "
              f"{r['principle'] or ''} ({r['secs']}s)", flush=True)
print(f"\nall cases proved by Vampire: {won}/{len(todo)}")
