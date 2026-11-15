"""Do broken tactic scripts fail in MeTTa?

Replays the case-1 script of scripts.metta and broken copies of it through
tactics.metta (mk:prove-and-check); only the original may be PROVED.

    python3 test_tactics.py
"""
import os
import re
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CETTA = "/home/yenat/cetta-demo/cetta2/cetta"
GOAL = "quotient_remainder_int_nat"

script = open(os.path.join(HERE, "scripts.metta"), encoding="utf-8").read()


def balanced(t):
    """The tactic itself: the last line also closes the Script atom."""
    while t.count(")") > t.count("("):
        t = t[:-1]
    return t


tactics = [balanced(t) for t in re.findall(r"^  (\(.*\))$", script, re.M)]

CASES = {
    "original script": (tactics, True),
    "wrong lemma in Have": ([t.replace("(Have f13 (omega_nat_p _ h4))", "(Have f13 (nat_p_omega _ h4))")
                             for t in tactics], False),
    "wrong hypothesis in Apply": ([t if t != "(Apply h39)" else "(Apply h35)" for t in tactics], False),
    "last tactic dropped": (tactics[:-1], False),
    "wrong rewrite": ([t.replace("(Rewrite mul_nat_mul_SNo h40)", "(Rewrite add_nat_add_SNo h40)")
                       for t in tactics], False),
    "witness for the wrong variable": ([t.replace("(Witness x37)", "(Witness x33)") for t in tactics], False),
}


def main():
    calls = "\n".join(
        f'!(let (Goal $n $i $T) (match &goals (Goal {GOAL} $i $t) (Goal {GOAL} $i $t))\n'
        f'   (case (mk:prove-and-check (mk:db $T 0) ({" ".join(tacs)}))\n'
        f'     (((Proved $x) (RESULT {k} PROVED)) ((Failed $w) (RESULT {k} FAILED)))))'
        for k, (tacs, _) in enumerate(CASES.values()))
    prog = (f'!(import! &self "{HERE}/tactics.metta")\n!(bind! &goals (new-space))\n'
            f'!(import! &lib "{HERE}/meglib.metta")\n!(import! &goals "{HERE}/goals.metta")\n'
            f'!(mk:load-kb 912)\n' + calls + "\n")
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "t.metta")
        open(path, "w", encoding="utf-8").write(prog)
        out = subprocess.run([CETTA, "--lang", "petta@1.0.6", path], capture_output=True, text=True).stdout
    got = dict(re.findall(r"\(RESULT (\d+) (PROVED|FAILED)\)", out))
    passed = 0
    for k, (label, (_, should)) in enumerate(CASES.items()):
        res = got.get(str(k), "NO RESULT")
        ok = res == ("PROVED" if should else "FAILED")
        passed += ok
        print(f"{'ok' if ok else 'WRONG':>5}  {label:32} {res}")
    print(f"{passed}/{len(CASES)} as expected")


if __name__ == "__main__":
    main()
