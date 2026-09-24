"""Measure the deterministic prover on a sample, reporting which tactic
strategies succeed. Everything reported as 'proved' here has passed Lean's
kernel, the statement-identity check, and the leak guard."""
import json
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor

from library import load
from itp import load_statements
from prover import Prover

CORPUS = "../data/corpus.sexpr"
_prover = None


def _init():
    global _prover
    decls = load(CORPUS)
    _prover = Prover(decls, CORPUS, load_statements())


def _run(idx):
    goal = _prover.decls[idx]
    t0 = time.time()
    r = _prover.prove(goal)
    r["secs"] = round(time.time() - t0, 1)
    return r


if __name__ == "__main__":
    step = int(sys.argv[1]) if len(sys.argv) > 1 else 33
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    out_path = sys.argv[3] if len(sys.argv) > 3 else "experiment.jsonl"
    decls = load(CORPUS)
    targets = [d.index for d in decls if d.kind == "THM"][::step]
    t0 = time.time()
    results = []
    with ProcessPoolExecutor(max_workers=workers, initializer=_init) as ex:
        for r in ex.map(_run, targets):
            results.append(r)
            print(f"{'PROVED' if r['proved_by'] else 'failed':7s} "
                  f"{r['goal'][:40]:40s} vampire={r['vampire']:9s} "
                  f"by={r['proved_by']} ({r['secs']}s)", flush=True)
    with open(out_path, "w") as fh:
        for r in results:
            fh.write(json.dumps(r) + "\n")
    proved = sum(1 for r in results if r["proved_by"])
    print(f"\nproved {proved}/{len(results)} ({proved/len(results):.0%}) "
          f"in {time.time()-t0:.0f}s")
    per = Counter()
    for r in results:
        for label, ok, _ in r["results"]:
            if ok:
                per[label] += 1
    print("successes per strategy (a theorem can count for several):")
    for label, c in per.most_common():
        print(f"  {label:20s} {c}")
