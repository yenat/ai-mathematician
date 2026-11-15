"""A Lean tactic script written by the CeTTa prover, as MeTTa tactic atoms.

The prover's tactics come from a handful of templates (../cetta/host.metta);
each maps to one tactic of tactics.metta:

  intro x1                                         (Intro x1)
  have f13 := @Megalodon.«omega_nat_p» _ h4        (Have f13 (omega_nat_p _ h4))
  (apply f29; try clear f29)                       (Apply f29)
  (intro q601 hq601; apply hq601 x33)              (Witness x33)
  apply Megalodon.«andI» / apply h35               (Apply andI) / (Apply h35)
  (have e := @Megalodon.«L»; simp only [b_eq] at e; rw [e] at h)
                                                   (Rewrite L h)

Anything else (the grind closers) has no MeTTa tactic yet and is reported.

    python3 from_lean_script.py results.jsonl goal >> scripts.metta
"""
import json
import re
import sys

CLASH = {"Empty", "Error", "False", "True", "Type", "and", "case", "collapse", "empty",
         "if", "let", "match", "not", "or", "quote", "superpose", "unify"}


def name(lean):
    n = lean.replace("@", "").replace("Megalodon.", "").strip("«»")
    return "meg_" + n if n in CLASH else n


def tactic(line):
    s = line.strip()
    if m := re.fullmatch(r"intro (\S+)", s):
        return f"(Intro {m.group(1)})"
    if m := re.fullmatch(r"have (\S+) := (\S+)((?: \S+)*)", s):
        args = " ".join(name(a) for a in m.group(3).split())
        return f"(Have {m.group(1)} ({name(m.group(2))}{' ' + args if args else ''}))"
    if m := re.fullmatch(r"\(apply (\S+); try clear \1\)", s):
        return f"(Apply {m.group(1)})"
    if m := re.fullmatch(r"\(intro (\S+) (\S+); apply \2 (\S+)\)", s):
        return f"(Witness {m.group(3)})"
    if m := re.fullmatch(r"apply (\S+)", s):
        return f"(Apply {name(m.group(1))})"
    if m := re.fullmatch(r"\(have (\S+) := (\S+); simp only \[b_eq\] at \1; rw \[\1\](?: at (\S+))?\)", s):
        return f"(Rewrite {name(m.group(2))} {m.group(3) or 'goal'})"
    raise ValueError(f"no MeTTa tactic for: {s}")


def main():
    path, goal = sys.argv[1], sys.argv[2]
    for line in open(path, encoding="utf-8"):
        row = json.loads(line)
        # a found script, whatever Lean's guard said (cases of a theorem are
        # not library entries, so the Phase 1 guard cannot accept them)
        if row["goal"] == goal and row["script"]:
            tacs = [tactic(t) for t in row["script"]]
            print(f"(Script {goal} (\n  " + "\n  ".join(tacs) + "))")
            return
    sys.exit(f"no script for {goal} in {path}")


if __name__ == "__main__":
    main()
