"""Long-term memory: the library as MeTTa atoms.

Every library theorem and axiom becomes

  (Lemma <name> <index> <number of hypotheses> <conclusion pattern>)

where the conclusion's universally quantified variables are MeTTa
variables, as in the Metamath-in-MeTTa encoding, so MeTTa's unification answers
"which lemmas can close this goal?". Definitions become (Def <name>).

Statements come from Lean itself (Sexpr.lean `#export_library`), so they are
written exactly like the goals Lean reports during search. The export is
cached in phase2/data/library_sexpr.txt.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
sys.path.insert(0, os.path.join(ROOT, "phase1"))

from itp import LEAN, LIB  # noqa: E402
from library import load  # noqa: E402

CORPUS = os.path.join(ROOT, "data/corpus.sexpr")
CACHE = os.path.join(HERE, "data/library_sexpr.txt")


def parse(text):
    """S-expression text -> nested lists of strings."""
    toks = text.replace("(", " ( ").replace(")", " ) ").split()
    stack = [[]]
    for t in toks:
        if t == "(":
            stack.append([])
        elif t == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(t)
    return stack[0][0]


def show(t):
    return t if isinstance(t, str) else "(" + " ".join(show(x) for x in t) + ")"


def split(stmt):
    """Peel leading ∀ and →: (variables, hypotheses, conclusion)."""
    vs, hyps = [], []
    while isinstance(stmt, list) and stmt and stmt[0] in ("∀", "→"):
        if stmt[0] == "∀":
            vs.append(stmt[1][0])
        else:
            hyps.append(stmt[1])
        stmt = stmt[2]
    return vs, hyps, stmt


def binders(stmt):
    """'_' for each leading variable and '?_' for each hypothesis, in order:
    the arguments of an explicit application `@L _ ?_ ...`."""
    out = []
    while isinstance(stmt, list) and stmt and stmt[0] in ("∀", "→"):
        out.append("_" if stmt[0] == "∀" else "?_")
        stmt = stmt[2]
    return out


def canon(t, depth=0, ren=None):
    """Rename bound variables by their depth inside `t` itself, so a
    statement is written the same wherever it occurs (in a goal, a
    hypothesis or the conclusion of a lemma)."""
    ren = ren or {}
    if isinstance(t, str):
        return ren.get(t, t)
    if t and t[0] in ("∀", "λ") and len(t) == 3 and isinstance(t[1], list):
        v = f"_b{depth}"
        return [t[0], [v, canon(t[1][1], depth, ren)], canon(t[2], depth + 1, {**ren, t[1][0]: v})]
    if t and t[0] == "→" and len(t) == 3:
        return ["→", canon(t[1], depth, ren), canon(t[2], depth + 1, ren)]
    return [canon(x, depth, ren) for x in t]


# library constants whose names MeTTa already uses (and would evaluate)
CLASH = {"and", "or", "not", "if", "True", "False", "Empty", "Error", "Type",
         "quote", "case", "let", "match", "unify", "empty", "superpose", "collapse"}


def to_metta(t):
    if isinstance(t, str):
        return "meg_" + t if t in CLASH else t
    return [to_metta(x) for x in t]


def from_metta(sym):
    return sym[4:] if sym.startswith("meg_") and sym[4:] in CLASH else sym


def as_pattern(t, vs):
    """Replace the given variables by MeTTa variables."""
    if isinstance(t, str):
        return "$" + t if t in vs else t
    return [as_pattern(x, vs) for x in t]


def export_library():
    if os.path.exists(CACHE):
        return open(CACHE).read()
    os.makedirs(os.path.dirname(CACHE), exist_ok=True)
    src = "import Bridge\n" + open(os.path.join(HERE, "Sexpr.lean")).read() + "\n#export_library\n"
    path = os.path.join(HERE, "data/export.lean")
    open(path, "w").write(src)
    r = subprocess.run([LEAN, path], capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": LIB})
    os.unlink(path)
    if r.returncode:
        raise RuntimeError(r.stdout[-2000:] + r.stderr[-2000:])
    open(CACHE, "w").write(r.stdout)
    return r.stdout


def facts():
    """name -> (index, variables, hypotheses, conclusion, binders) for every library
    theorem and axiom, the conclusion with variables renamed V0, V1, ..."""
    decls = load(CORPUS)
    index = {d.name: d.index for d in decls if d.kind in ("THM", "AXIOM")}
    out = {}
    for line in export_library().splitlines():
        if not line.startswith("THM "):
            continue
        name, stmt = line[4:].split(" ", 1)
        if name not in index:  # bridge lemmas and Lean-generated names
            continue
        vs, hyps, concl = split(parse(stmt))
        top = {v: f"V{i}" for i, v in enumerate(vs)}  # distinct from inner _b names
        hyps = [to_metta(canon(canon(h, ren=top))) for h in hyps]
        out[name] = (index[name], list(top.values()), hyps,
                     to_metta(canon(canon(concl, ren=top))), binders(parse(stmt)))
    return out


def conclusions(concl, nh):
    """The ways a fact can close a goal: its conclusion, and False when it
    concludes a negation (not P is P -> False), with one more hypothesis."""
    yield concl, nh
    if isinstance(concl, list) and len(concl) == 2 and concl[0] == "meg_not":
        yield "meg_False", nh + 1


def atoms():
    """MeTTa source lines of the long-term memory:
      (Lemma <name> <index> <hypotheses> <conclusion pattern>)
      (IffR <name> <index> Q), (IffL <name> <index> P)     for P <-> Q facts
      (HOLemma ...)  like Lemma, for conclusions (P x) with P a variable
      (Elim <name> <index> <hypothesis pattern>)          one-hypothesis facts
      (Def <name>)"""
    decls = load(CORPUS)
    out = [f"(Def {to_metta(d.name)})" for d in decls if d.kind == "DEF"]
    def flexible(t):  # a variable, or a variable applied to arguments
        return t in vs if isinstance(t, str) else bool(t) and isinstance(t[0], str) and t[0] in vs

    for name, (i, vs, hyps, concl, _) in facts().items():
        for c, nh in conclusions(concl, len(hyps)):
            if isinstance(c, str) and c in vs:  # concludes anything: too general
                continue
            kind = "HOLemma" if flexible(c) else "Lemma"
            out.append(f"({kind} {name} {i} {nh} {show(as_pattern(c, vs))})")
        if len(hyps) == 1:  # forward use: a fact matching the hypothesis gives the conclusion
            h = hyps[0]
            if not flexible(h):
                out.append(f"(Elim {name} {i} {show(as_pattern(h, vs))})")
        if isinstance(concl, list) and len(concl) == 3 and concl[0] == "iff" and concl[1] != concl[2]:
            p, q = concl[1:]
            if not flexible(q):
                out.append(f"(IffR {name} {i} {show(as_pattern(q, vs))})")
            if not flexible(p):
                out.append(f"(IffL {name} {i} {show(as_pattern(p, vs))})")
    return out


if __name__ == "__main__":
    lines = atoms()
    print(len(lines), "atoms")
    print("\n".join(l for l in lines if " Subq_tra " in l or " UnionE " in l or " andI " in l))
