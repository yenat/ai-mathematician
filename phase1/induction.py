"""Induction without an LLM: split a goal into the cases of an induction
principle, so Vampire only has to do ordinary reasoning on each case.

Why this is needed: an induction proof hinges on the induction PREDICATE
("the statement P(n) we induct on"). Vampire does not invent predicates,
so even given the exact facts the original proof cited it proves only 5%
of the induction theorems. But the predicate is usually just the goal
itself, read as a statement about one variable. We build it here.

All the library's principles share one shape:

    forall P, CASES(P) -> forall x, GUARD x -> P x

e.g. nat_ind: P Empty -> (forall n, nat_p n -> P n -> P (ordsucc n))
              -> forall x, nat_p x -> P x.

For a goal  forall ... x ..., ... -> GUARD x -> ... -> C  we pick the
induction variable x, let P(t) be the goal with x := t and GUARD x removed
(the remaining binders and hypotheses kept in their order), and read off
each case of the principle as a stand-alone statement.

The Lean side mirrors this exactly: introduce everything, `revert` all but
x and its guard, `revert` those two, `apply` the principle, and prove each
resulting case (Lean fixes P by higher-order pattern unification).
Nothing here is trusted: Lean checks the final proof as usual.
"""
import itertools

from library import Decl

_fresh = itertools.count()


# ---- named <-> de Bruijn --------------------------------------------------

def to_named(node, env=()):
    """Replace De Bruijn indices by ('VAR', name); binders become
    [tag, type, body, name]."""
    if not isinstance(node, list) or not node:
        return node
    tag = node[0]
    if tag == "DB":
        return ["VAR", env[-(int(node[1]) + 1)]]
    if tag in ("ALL", "LAM"):
        v = f"v{next(_fresh)}"
        return [tag, node[1], to_named(node[2], env + (v,)), v]
    if tag in ("AP", "IMP", "TPAP"):
        return [tag] + [to_named(c, env) for c in node[1:]]
    return node


def to_db(node, env=()):
    if not isinstance(node, list) or not node:
        return node
    tag = node[0]
    if tag == "VAR":
        return ["DB", str(len(env) - 1 - env.index(node[1]))]
    if tag in ("ALL", "LAM"):
        return [tag, node[1], to_db(node[2], env + (node[3],))]
    if tag in ("AP", "IMP", "TPAP"):
        return [tag] + [to_db(c, env) for c in node[1:]]
    return node


def subst(node, name, term):
    """Capture-free: every binder name is fresh, `term` is closed apart
    from names bound outside the whole statement."""
    if not isinstance(node, list) or not node:
        return node
    if node[0] == "VAR":
        return term if node[1] == name else node
    if node[0] in ("ALL", "LAM"):
        return [node[0], node[1], subst(node[2], name, term), node[3]]
    return [node[0]] + [subst(c, name, term) for c in node[1:]]


def mentions(node, name):
    if not isinstance(node, list) or not node:
        return False
    if node[0] == "VAR":
        return node[1] == name
    return any(mentions(c, name) for c in node[1:])


# ---- principles -----------------------------------------------------------

def _principles(C, forall, imp, In, V):
    """Each entry: guard constant (None = any set), and a function from
    the motive P (a Python function term -> statement) to the list of
    case statements, in the order the principle takes them."""
    return {
        "nat_ind": ("nat_p", lambda P: [
            P(C("Empty")),
            forall(lambda n: imp(C("nat_p", n), imp(P(n), P(C("ordsucc", n)))))]),
        "nat_complete_ind": ("nat_p", lambda P: [
            forall(lambda n: imp(C("nat_p", n),
                   imp(forall(lambda m: imp(In(m, n), P(m))), P(n))))]),
        "ordinal_ind": ("ordinal", lambda P: [
            forall(lambda n: imp(C("ordinal", n),
                   imp(forall(lambda m: imp(In(m, n), P(m))), P(n))))]),
        "SNoLev_ind": ("SNo", lambda P: [
            forall(lambda n: imp(C("SNo", n),
                   imp(forall(lambda m: imp(In(m, C("SNoS_", C("SNoLev", n))),
                                            P(m))), P(n))))]),
        "finite_ind": ("finite", lambda P: [
            P(C("Empty")),
            forall(lambda X: forall(lambda y: imp(
                C("finite", X), imp(C("nIn", y, X),
                                    imp(P(X), P(C("binunion", X, C("Sing", y))))))))]),
        "In_ind": (None, lambda P: [
            forall(lambda n: imp(forall(lambda m: imp(In(m, n), P(m))), P(n)))]),
    }


class Inductor:
    def __init__(self, decls):
        self.by_name = {d.name: d for d in decls}
        self.hash_to_name = {d.hash: d.name for d in decls}

        def C(name, *args):
            t = ["TMH", self.by_name[name].hash]
            for a in args:
                t = ["AP", t, a]
            return t

        def forall(body_fn):
            v = f"v{next(_fresh)}"
            return ["ALL", ["SET"], body_fn(["VAR", v]), v]

        def imp(a, b):
            return ["IMP", a, b]

        self.C = C
        self.principles = _principles(
            C, forall, imp, lambda a, b: C("In", a, b), None)

    def _guard_of(self, hyp):
        """'nat_p' if hyp is  nat_p (VAR x), with x's name; else None."""
        if (isinstance(hyp, list) and hyp[0] == "AP" and hyp[1][0] == "TMH"
                and hyp[2][0] == "VAR"):
            return self.hash_to_name.get(hyp[1][1]), hyp[2][1]
        return None, None

    def splits(self, goal):
        """Yield (principle, x_pos, guard_pos, [case Decl]) for every way of
        doing induction on this goal with a principle proved BEFORE it.
        x_pos / guard_pos index the goal's prefix of binders/hypotheses."""
        stmt = to_named(goal.stmt)
        prefix, node = [], stmt
        while isinstance(node, list) and node[0] in ("ALL", "IMP"):
            if node[0] == "ALL":
                prefix.append(("ALL", node[1], node[3]))
            else:
                prefix.append(("IMP", node[1]))
            node = node[2]
        concl = node

        for pname, (guard, cases_fn) in self.principles.items():
            pd = self.by_name.get(pname)
            if pd is None or pd.index >= goal.index:
                continue      # principle not yet available: would leak
            for i, item in enumerate(prefix):
                if item[0] != "ALL" or item[1] != ["SET"]:
                    continue
                x = item[2]
                gpos = None
                if guard is not None:
                    gpos = next((j for j, it in enumerate(prefix)
                                 if it[0] == "IMP"
                                 and self._guard_of(it[1]) == (guard, x)), None)
                    if gpos is None:
                        continue
                rest = [it for j, it in enumerate(prefix) if j not in (i, gpos)]

                def P(t, rest=rest, x=x):
                    out = subst(concl, x, t)
                    for it in reversed(rest):
                        if it[0] == "ALL":
                            v = f"v{next(_fresh)}"
                            out = ["ALL", it[1], subst(out, it[2], ["VAR", v]), v]
                        else:
                            out = ["IMP", subst(it[1], x, t), out]
                    return out

                # the rest must be a closed-up statement once x is replaced
                cases = []
                for k, c in enumerate(cases_fn(P)):
                    db = to_db(c)
                    d = Decl(goal.index, "THM", f"{goal.name}__{pname}_{k}",
                             "", db)
                    d.stmt_syms = set(goal.stmt_syms) | {
                        n for n in _consts(db, self.hash_to_name)}
                    d.feats = goal.feats
                    cases.append(d)
                yield pname, i, gpos, cases


def _consts(node, h2n):
    if not isinstance(node, list) or not node:
        return
    if node[0] == "TMH":
        n = h2n.get(node[1])
        if n:
            yield n
        return
    for c in node[1:]:
        yield from _consts(c, h2n)


def _steps(script):
    """Split a tactic script into top-level steps, folding indented
    continuation lines into the step they belong to."""
    steps = []
    for ln in script.strip().splitlines():
        if ln.startswith(" ") and steps:
            steps[-1] += "; " + ln.strip()
        else:
            steps.append(ln.strip())
    return steps


def lean_script(goal_prefix_len, x_pos, g_pos, principle, case_tactics):
    """Lean tactic script: intro every binder/hypothesis by position,
    revert all but x and its guard (so they become P's binders, in their
    original order), revert x and guard, apply the principle, then prove
    each case with `first` over that case's candidate tactics."""
    names = [f"i{k}" for k in range(goal_prefix_len)]
    keep = {x_pos} | ({g_pos} if g_pos is not None else set())
    others = [n for k, n in enumerate(names) if k not in keep]
    lines = [f"intro {' '.join(names)}"]
    if others:
        lines.append(f"revert {' '.join(others)}")
    if g_pos is not None:
        lines.append(f"revert {names[g_pos]}")
    lines.append(f"revert {names[x_pos]}")
    lines.append(f"apply «{principle}»")
    for tacs in case_tactics:
        # one line per alternative. Each step is parenthesised: in Lean,
        # `try a; b` means `try (a; b)`, which would swallow b's failure and
        # let an alternative "succeed" without closing the case.
        alts = "\n".join(
            "    | (" + "; ".join(f"({ln.strip()})" for ln in _steps(t))
            + "; done)" for t in tacs)
        lines.append(f"· first\n{alts}")
    return "\n".join(lines)
