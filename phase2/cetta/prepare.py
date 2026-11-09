"""Write the data the MeTTa prover reads, once, before any search.

  data/library.metta   long-term memory (the atoms of ../ltm.py) and, per
                       library entry, (Index name i), (Def name), and per
                       theorem (Statement name "<Lean signature>") and
                       (Binders name (_ ?_ ...)) for explicit applications
  data/sexpr.lean      ../Sexpr.lean without its import, sent to the REPL

Nothing here runs during proof search.

    python3 prepare.py
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "..", "..", "phase1"))

from itp import load_statements  # noqa: E402
from library import load  # noqa: E402
from ltm import CLASH, CORPUS, atoms, facts, to_metta  # noqa: E402


def text(s):
    return json.dumps(s, ensure_ascii=False)


def main():
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    decls = load(CORPUS)
    lines = atoms()
    for d in decls:
        lines.append(f"(Index {to_metta(d.name)} {d.index})")
    for name, (_, _, _, _, binders) in facts().items():
        lines.append(f"(Binders {name} ({' '.join(binders)}))")
    statements = load_statements()
    for name, sig in statements.items():
        lines.append(f"(Statement {name} {text(sig)})")
    with open(os.path.join(HERE, "data/library.metta"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    # Lean prints names MeTTa would evaluate (and, if, True, ...) with the
    # meg_ prefix, as ltm.to_metta does, so goals parse straight into atoms.
    src = open(os.path.join(HERE, "../Sexpr.lean"), encoding="utf-8").read()
    clash = ", ".join(f'"{c}"' for c in sorted(CLASH))
    old_sym = '  if s.startsWith "$" then "_" ++ s else s\n'
    new_sym = ('  let s := if s.startsWith "$" then "_" ++ s else s\n'
               f'  if [{clash}].contains s then "meg_" ++ s else s\n')
    old_sort = 'return if l.isZero then "Prop" else "Type"'
    assert src.count(old_sym) == 1 and src.count(old_sort) == 1
    src = src.replace("import Lean\n", "").replace(old_sym, new_sym)
    src = src.replace(old_sort, 'return if l.isZero then "Prop" else "meg_Type"')
    with open(os.path.join(HERE, "data/sexpr.lean"), "w", encoding="utf-8") as f:
        f.write(src)
    print(f"{len(lines)} atoms, {len(statements)} statements")


if __name__ == "__main__":
    main()
