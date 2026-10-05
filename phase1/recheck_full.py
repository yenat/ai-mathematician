"""Independently re-verify every proof a full run reports.

A result row records WHICH strategy won and the premise sets / definitions
it was built from; the battery is deterministic, so this rebuilds exactly
that one script (induction proofs store theirs) and checks it alone, in a
fresh Lean process, with the full bar: kernel, statement identity, leak
guard, no sorryAx. A reported number should survive this.

Usage: python3 recheck_full.py <run.jsonl> <workers> <out.jsonl>
"""
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor

from library import load
from itp import load_statements
from prover import Prover, candidate_tactics, followup_tactics, apply_tactics, duper_tactics

CORPUS = "../data/corpus.sexpr"
src, workers, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
decls = load(CORPUS)
by = {d.name: d for d in decls}
prover = Prover(decls, CORPUS, load_statements())
wins = [r for r in map(json.loads, open(src)) if r["proved_by"]]
print(f"{len(wins)} proofs to re-check", flush=True)


def script_of(r):
    label = r["proved_by"]
    if label.startswith("induction"):
        return r["script"]
    base, _, j = label.partition("#")
    premises = r["premise_sets"][int(j) - 1] if j else r["premise_sets"][0]
    g = by[r["goal"]]
    gd = prover.goal_defs(g)
    table = dict(candidate_tactics(premises, r["defs"], gd))
    table.update(followup_tactics(premises, r["defs"], gd))
    table.update(apply_tactics(premises, r["defs"]))
    table.update(duper_tactics(premises, r["defs"]))
    return table[base]


def run(r):
    t0 = time.time()
    script = script_of(r)
    duper = r["proved_by"].startswith("duper")
    (_, ok, why), = prover.attempt_batch(by[r["goal"]], [("recheck", script)],
                                         timeout=600 if duper else 300,
                                         single_timeout=600 if duper else 300,
                                         heartbeats=1000000 if duper else 200000,
                                         duper=duper)
    return {"goal": r["goal"], "proved_by": r["proved_by"], "ok": ok,
            "why": why if not ok else "", "secs": round(time.time() - t0, 1)}


good, bad = 0, []
with ThreadPoolExecutor(max_workers=workers) as ex, open(out, "w") as fh:
    for i, r in enumerate(ex.map(run, wins), 1):
        fh.write(json.dumps(r) + "\n")
        fh.flush()
        if r["ok"]:
            good += 1
        else:
            bad.append(r)
            print(f"FAILED RECHECK {r['goal']} ({r['proved_by']}): "
                  f"{r['why'].splitlines()[0][:150] if r['why'] else ''}", flush=True)
        if i % 50 == 0:
            print(f"  {i}/{len(wins)} checked, {len(bad)} failed", flush=True)
print(f"\nre-verified {good}/{len(wins)}")
