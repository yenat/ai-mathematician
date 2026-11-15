"""Write the data the MeTTa prover reads, once, before any search.

  data/library.metta   long-term memory (the atoms of ../ltm.py) and, per
                       library entry, (Index name i), (Def name), and per
                       theorem (Statement name "<Lean signature>") and
                       (Binders name (_ ?_ ...)) for explicit applications,
                       (Hyps name i (P1 P2 ...)) for lemmas with hypotheses,
                       and the test goals in CASES
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
from ltm import CLASH, CORPUS, as_pattern, atoms, facts, show, to_metta  # noqa: E402


# quotient_remainder_int for n a natural number (its first case).
CASES = {
    "quotient_remainder_int_nat": ("quotient_remainder_int",
        " : (forall x1 : set, (((In x1) ((setminus omega) (Sing Empty))) -> "
        "(forall x2 : set, (((In x2) omega) -> ((ex set) (fun x3 : set => "
        "((and ((In x3) int)) ((ex set) (fun x4 : set => ((and ((In x4) x1)) "
        "(((eq set) x2) ((add_SNo ((mul_SNo x3) x1)) x4))))))))))))"),
}


def text(s):
    return json.dumps(s, ensure_ascii=False)


def patched_sexpr():
    """../Sexpr.lean without its import, printing names MeTTa would evaluate
    (and, if, True, ...) with the meg_ prefix, as ltm.to_metta does, so goals
    parse straight into atoms."""
    src = open(os.path.join(HERE, "../Sexpr.lean"), encoding="utf-8").read()
    clash = ", ".join(f'"{c}"' for c in sorted(CLASH))
    old_sym = '  if s.startsWith "$" then "_" ++ s else s\n'
    new_sym = ('  let s := if s.startsWith "$" then "_" ++ s else s\n'
               f'  if [{clash}].contains s then "meg_" ++ s else s\n')
    old_sort = 'return if l.isZero then "Prop" else "Type"'
    assert src.count(old_sym) == 1 and src.count(old_sort) == 1
    src = src.replace("import Lean\n", "").replace(old_sym, new_sym)
    return src.replace(old_sort, 'return if l.isZero then "Prop" else "meg_Type"')


def main():
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    decls = load(CORPUS)
    lines = atoms()
    for d in decls:
        lines.append(f"(Index {to_metta(d.name)} {d.index})")
    for name, (i, vs, hyps, _, binders) in facts().items():
        lines.append(f"(Binders {name} ({' '.join(binders)}))")
        # Hypothesis patterns, in order, for forward use of a hinted lemma
        # (each matched against a fact in context).
        if len(hyps) >= 1:
            pats = " ".join(show(as_pattern(h, vs)) for h in hyps)
            lines.append(f"(Hyps {name} {i} ({pats}))")
    statements = load_statements()
    for name, sig in statements.items():
        lines.append(f"(Statement {name} {text(sig)})")
    # Test goals: one case of a library theorem, stated on its own and placed
    # at the theorem's position (so only earlier lemmas may be used).
    for name, (theorem, sig) in CASES.items():
        index = next(d.index for d in decls if d.name == theorem)
        lines.append(f"(Index {name} {index})")
        lines.append(f"(Statement {name} {text(sig)})")
    with open(os.path.join(HERE, "data/library.metta"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    src = patched_sexpr()
    with open(os.path.join(HERE, "data/sexpr.lean"), "w", encoding="utf-8") as f:
        f.write(src)
    print(f"{len(lines)} atoms, {len(statements)} statements")


if __name__ == "__main__":
    main()
