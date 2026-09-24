"""Independently re-verify every LLM-found proof: take the winning script
from each result file, run it again in a fresh Lean process, and re-apply
the statement check and leak guard. A reported number should survive this."""
import json
import sys
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())

wins = []
for f in sys.argv[1:]:
    for l in open(f):
        r = json.loads(l)
        if r["proved_by"]:
            script = next(t["script"] for t in r["transcript"]
                          if t.get("ok"))
            wins.append((r["goal"], script, f))


def run(w):
    goal, script, f = w
    (label, ok, why), = prover.attempt_batch(by[goal], [("recheck", script)])
    return goal, ok, why, f


bad = []
with ThreadPoolExecutor(max_workers=4) as ex:
    for goal, ok, why, f in ex.map(run, wins):
        if not ok:
            bad.append((goal, why.splitlines()[0][:150], f))
print(f"re-verified {len(wins) - len(bad)}/{len(wins)}")
for b in bad:
    print("  FAILED RECHECK:", b)
