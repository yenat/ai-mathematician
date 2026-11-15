"""Write the Lean library as MeTTa: every type, definition body and proof term,
then read the file back into Lean and check that nothing was lost.

Lean (lib/MegLib.lean) is read once, here; nothing after this needs Lean.
The format follows the Metamath port in trueagi-io/chaining
(experimental/metamath), one record per declaration in library order:

  (MkIndexed i (MkAxiom      name type))
  (MkIndexed i (MkDefinition name body type))
  (MkIndexed i (MkTheorem    name proof type))

The writer is ../Sexpr.lean in strict mode (#export_metta), with the meg_
renaming the prover uses (../cetta/prepare.py), so a goal and a library
statement are the same atom:

  forall x : set, P x     ~>  (∀ (_b0 set) (P _b0))
  A -> B                  ~>  (→ A B)
  fun x : set => t        ~>  (λ (_b0 set) t)

Bound variables are named by binder depth, so the library has no MeTTa
variables and nothing can be captured.  #metta_roundtrip then parses every
record back into a Lean term and compares it with the original declaration.

    python3 export.py            # writes meglib.metta, prints the round trip
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(HERE, "..", "cetta"))
from prepare import CASES, CLASH, patched_sexpr  # noqa: E402

LEAN = "/home/yenat/lean4-toolchain/lean-4.34.0-linux/bin/lean"
OUT = os.path.join(HERE, "meglib.metta")
GOALS = os.path.join(HERE, "goals.metta")
DECL = re.compile(r"(?:@\[\w+\] )?(?:noncomputable )?(?:theorem|axiom|def|opaque) (\S+)")


def lean(command):
    """Run Sexpr.lean (patched) with MegLib imported, then `command`."""
    tmp = os.path.join(HERE, "_export.lean")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write("import Lean\nimport MegLib\n" + patched_sexpr() + "\n" + command + "\n")
    env = dict(os.environ, LEAN_PATH=os.path.join(ROOT, "lib"))
    try:
        r = subprocess.run([LEAN, tmp], capture_output=True, text=True, env=env)
    finally:
        os.remove(tmp)
    if r.returncode != 0:
        sys.exit(f"lean failed ({r.returncode}):\n{r.stdout[-3000:]}\n{r.stderr[-2000:]}")
    return r.stdout


def in_source_order(lines):
    """Lean's environment does not keep declaration order; MegLib.lean does,
    and checking in order needs every lemma after the lemmas it uses."""
    pos = {}
    for line in open(os.path.join(ROOT, "lib", "MegLib.lean"), encoding="utf-8"):
        m = DECL.match(line)
        if m:
            n = m.group(1).strip("«»")
            pos["meg_" + n if n in CLASH else n] = len(pos)
    body = {}
    for l in lines:
        _, _, rest = l[len("(MkIndexed "):].partition(" ")
        name = rest.split(" ", 2)[1]
        if name not in pos:
            sys.exit(f"{name} not found in MegLib.lean")
        body[name] = rest
    if len(body) != len(pos):
        sys.exit(f"{len(body)} exported, {len(pos)} declared")
    return [f"(MkIndexed {i} {body[n]}" for i, n in enumerate(sorted(body, key=pos.get))]


def export_goals():
    """The test goals of ../cetta/prepare.py (cases of library theorems), as
    (Goal name index type): index is the theorem's position, so a proof may
    use only the declarations before it."""
    order = {}
    for i, l in enumerate(open(OUT, encoding="utf-8")):
        m = re.match(r"\(MkIndexed (\d+) \(Mk\w+ (\S+) ", l)
        if m:
            order[m.group(2)] = int(m.group(1))
    stated = "".join(f"namespace Megalodon\ntheorem {n}{sig} := sorry\nend Megalodon\n"
                     f"#export_type Megalodon.{n}\n" for n, (_, sig) in CASES.items())
    out = lean("set_option linter.all false\n" + stated)
    rows = []
    for l in out.splitlines():
        if l.startswith("TYPE "):
            _, name, ty = l.split(" ", 2)
            rows.append(f"(Goal {name} {order[CASES[name][0]]} {ty})")
    assert len(rows) == len(CASES), out[-2000:]
    with open(GOALS, "w", encoding="utf-8") as f:
        f.write(";; Test goals as MeTTa, written by export.py: (Goal name index type)\n"
                + "\n".join(rows) + "\n")
    print(f"{len(rows)} goals -> {GOALS}")


def main():
    out = lean("#export_metta")
    lines = in_source_order([l for l in out.splitlines() if l.startswith("(MkIndexed ")])
    header = (";; MegLib (lib/MegLib.lean) as MeTTa, written by export.py.\n"
              ";; (MkIndexed i (MkAxiom name type))\n"
              ";; (MkIndexed i (MkDefinition name body type))\n"
              ";; (MkIndexed i (MkTheorem name proof type))\n")
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(header + "\n".join(lines) + "\n")
    kinds = {k: sum(f"({k} " in l for l in lines) for k in ("MkAxiom", "MkDefinition", "MkTheorem")}
    print(f"{len(lines)} declarations -> {OUT}: {kinds}")
    report = lean(f'#metta_roundtrip "{OUT}"')
    print("\n".join(l for l in report.splitlines() if l.startswith(("ROUNDTRIP", "  "))))
    m = re.search(r"ROUNDTRIP (\d+) exact, (\d+) failed, (\d+) declarations not in file", report)
    if not m or m.group(2) != "0" or m.group(3) != "0" or int(m.group(1)) != len(lines):
        sys.exit("round trip is not exact")
    export_goals()


if __name__ == "__main__":
    main()
