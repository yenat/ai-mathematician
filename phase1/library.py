"""Phase 1 library: every declaration from Megalodon's typed export, in
source order, with the symbols it mentions and (for theorems) the facts its
original proof actually used.

This is the ground everything else stands on:
  - Search ranks earlier facts against a goal using `stmt_syms`.
  - The evaluation holds a theorem out and only lets the prover see
    declarations that come BEFORE it (`index`), so nothing can leak forward.
  - `proof_deps` records what the original Megalodon proof cited. It is used
    to (a) train premise selection on EARLIER theorems only, and (b) score
    how well Search recalls the premises a real proof needed. It is never
    shown to the prover for the theorem being proved.
"""
from dataclasses import dataclass, field
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from sexpr_translate import parse_toplevel_forms  # noqa: E402

# Megalodon's own logical vocabulary. Every statement mentions some of these,
# so they carry almost no signal about relevance; Search down-weights them.
LOGICAL = {"True", "False", "not", "and", "or", "iff", "ex", "eq", "neq"}


@dataclass
class Decl:
    index: int                 # position in source order
    kind: str                  # PARAM / AXIOM / DEF / PRIM / THM
    name: str
    hash: str
    stmt: object               # typed s-expression of the statement / type
    body: object = None        # DEF body, or THM proof term
    stmt_syms: set = field(default_factory=set)   # constants in the statement
    proof_deps: set = field(default_factory=set)  # facts the original proof cited


def _collect(node, hash_to_name, prim_to_name, out, known_only=False):
    """Walk an s-expression, adding every referenced constant's name to out.
    With known_only, collect only KNOWN (cited facts) -- i.e. proof premises."""
    if isinstance(node, str) or not node:
        return
    tag = node[0]
    if tag == "TMH" and not known_only:
        name = hash_to_name.get(node[1])
        if name:
            out.add(name)
        return
    if tag == "PRIM" and not known_only and len(node) == 2:
        name = prim_to_name.get(int(node[1]))
        if name:
            out.add(name)
        return
    if tag == "KNOWN":
        name = hash_to_name.get(node[1])
        if name:
            out.add(name)
        return
    for child in node[1:]:
        if isinstance(child, list):
            _collect(child, hash_to_name, prim_to_name, out, known_only)


def load(path):
    """Return the library as a list of Decl in source order."""
    forms = parse_toplevel_forms(open(path, encoding="utf-8").read())
    hash_to_name, prim_to_name = {}, {}
    decls, by_name, pending = [], {}, {}

    def add(d):
        d.index = len(decls)
        decls.append(d)
        by_name[d.name] = d

    for f in forms:
        tag = f[0]
        if tag in ("PARAM", "AXIOM"):
            _, name, h, _i, ty = f
            d = Decl(0, tag, name, h, ty)
            _collect(ty, hash_to_name, prim_to_name, d.stmt_syms)
            add(d)
            hash_to_name[h] = name
        elif tag == "DEF":
            _, name, h, _i, ty, tm = f
            d = Decl(0, tag, name, h, ty, tm)
            _collect(tm, hash_to_name, prim_to_name, d.stmt_syms)
            add(d)
            hash_to_name[h] = name
        elif tag == "PRIM":
            _, idx, name, h, ty = f
            add(Decl(0, tag, name, h, ty))
            hash_to_name[h] = name
            prim_to_name[int(idx)] = name
        elif tag == "THM":
            _, name, ahv, _pfg, _i, ty = f
            d = Decl(0, "THM", name, ahv, ty)
            _collect(ty, hash_to_name, prim_to_name, d.stmt_syms)
            pending[name] = d
        elif tag == "PROOF":
            _, name, pf = f
            d = pending.pop(name, None)
            if d is None:
                continue
            d.body = pf
            _collect(pf, hash_to_name, prim_to_name, d.proof_deps, known_only=True)
            add(d)
            hash_to_name[d.hash] = name
    return decls


if __name__ == "__main__":
    decls = load(sys.argv[1] if len(sys.argv) > 1 else "data/corpus.sexpr")
    kinds = {}
    for d in decls:
        kinds[d.kind] = kinds.get(d.kind, 0) + 1
    print("declarations:", len(decls), kinds)
    thms = [d for d in decls if d.kind == "THM"]
    avg = sum(len(d.proof_deps) for d in thms) / len(thms)
    print(f"theorems: {len(thms)}  avg facts cited per original proof: {avg:.1f}")
    for name in ("andI", "Subq_ref", "set_ext"):
        for d in decls:
            if d.name == name:
                print(f"  {d.kind} {d.name}: syms={sorted(d.stmt_syms)} "
                      f"proof_deps={sorted(d.proof_deps)}")
