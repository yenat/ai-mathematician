"""Does the MeTTa checker reject broken proofs?

Each case changes one record of meglib.metta and runs check.metta over the
library up to that record.  The changed record must be the first failure.

    python3 test_check.py
"""
import os
import re
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CETTA = "/home/yenat/cetta-demo/cetta2/cetta"
LIB = open(os.path.join(HERE, "meglib.metta"), encoding="utf-8").read().splitlines()


def record(name):
    for i, l in enumerate(LIB):
        if re.match(rf"\(MkIndexed \d+ \(Mk\w+ {re.escape(name)} ", l):
            return i
    raise KeyError(name)


def proof_of(name):
    """The proof field of a theorem record, as text."""
    l = LIB[record(name)]
    body = l[l.index(f" {name} ") + len(name) + 2:]
    depth = 0
    for k, c in enumerate(body):
        depth += c == "("
        depth -= c == ")"
        if depth == 0:
            return body[:k + 1]


def case_replace(name, old, new):
    return name, lambda l: l.replace(old, new, 1) if old in l else None


def case_proof_from(name, other):
    return name, lambda l: l.replace(proof_of(name), proof_of(other), 1)


CASES = {
    "wrong argument": case_replace("omega_nat_p", "nat_p _b0 _b1)", "nat_p _b0 _b0)"),
    "wrong binder type": case_replace("andI", "(λ (_b2 _b0) (λ (_b3 _b1)", "(λ (_b2 _b1) (λ (_b3 _b1)"),
    "statement changed": case_replace("andI", "(meg_and _b0 _b1)))))", "(meg_and _b1 _b0)))))"),
    "another theorem's proof": case_proof_from("orIR", "orIL"),
    "lemma cited before it is proved": case_replace("omega_nat_p", "(SepE2 ", "(sqrt_2_irrational "),
    "proof cites itself": case_replace("Pi_nat_0", "(nat_primrec_0 ", "(Pi_nat_0 "),
}


def run(lines, last):
    with tempfile.TemporaryDirectory() as d:
        stem = os.path.join(d, "lib")
        with open(stem + ".metta", "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
        r = subprocess.run([CETTA, "--lang", "petta@1.0.6", os.path.join(HERE, "check.metta"),
                            "0", str(last), stem], capture_output=True, text=True, cwd=HERE)
    return r.stdout


def main():
    passed = 0
    for label, (name, change) in CASES.items():
        i = record(name)
        new = change(LIB[i])
        assert new and new != LIB[i], f"{label}: change did not apply"
        lines = LIB[:i] + [new]
        out = run(lines, int(re.match(r"\(MkIndexed (\d+)", LIB[i]).group(1)))
        fails = [l for l in out.splitlines() if l.startswith("(FAILED")]
        ok = len(fails) == 1 and f" {name} " in fails[0]
        passed += ok
        print(f"{'rejected' if ok else 'NOT REJECTED':>12}  {label:32} {fails[0][:110] if fails else out[-200:]}")
    print(f"{passed}/{len(CASES)} broken proofs rejected")


if __name__ == "__main__":
    main()
