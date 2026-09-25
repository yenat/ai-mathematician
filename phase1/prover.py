"""Phase 1 prover: Search -> ATP (Vampire) -> ITP (Lean), no LLM required.

For one goal:
  1. Search ranks the facts available before the goal.
  2. Vampire (untrusted) tries to prove the goal from those facts; if it
     succeeds, the facts its proof used become the premise hint set.
  3. A deterministic battery of Lean tactic scripts is built from the hints
     and checked by Lean (trusted) with the statement-identity check and
     the leak guard. First script that passes wins.

An optional LLM (see llm.py, added later) plugs in between 2 and 3 as one
more source of candidate tactic scripts -- also untrusted, also checked by
Lean and the leak guard in exactly the same way.
"""
import os
import re
import subprocess
import tempfile

from atp import THF, attach_prim_indices, run_vampire, Unsupported, ident
from itp import LEAN, LIB, BRIDGE, _GUARD, leak_free
from search import Search


def _lean_name(name):
    """Megalodon names are valid Lean identifiers except primes-only
    edge cases; wrap everything in «» to be safe."""
    return f"«{name}»"


def candidate_tactics(premises, defs, goal_defs=None):
    """Deterministic battery, cheapest first. Each entry: (label, script).

    The `goal-*` and `ext-*` strategies were distilled from the 51 proofs
    the LLM found for theorems this battery originally missed. They encode
    the three mechanical patterns those proofs kept using:
      * unfold the GOAL's own definitions -- only in the goal, not in the
        premises -- then introduce what that reveals (e.g. `Subq A B`
        unfolds to `forall z, In z A -> In z B`, so intro z and z ∈ A);
      * turn encoded or/and/ex from elimination lemmas native and let
        grind case-split on them;
      * prove set equality through extensionality (`set_ext`).
    Unfolding everything everywhere, as `prem-unfold-grind` does, rewrites
    the premises too, which is what broke these cases before."""
    P = [_lean_name(p) for p in premises]
    D = [_lean_name(d) for d in defs]
    G = [_lean_name(d) for d in (goal_defs if goal_defs is not None else defs)]
    haves = "".join(f"have hp{i} := @{p}\n" for i, p in enumerate(P))
    unfold = ", ".join([BRIDGE] + D) if D else BRIDGE
    goal_unfold = (f"try simp only [{', '.join(G)}]\ntry intros\n"
                   f"try simp only [{BRIDGE}] at *\n") if G else ""
    cands = [
        ("intro-grind", f"intros\ntry simp only [{BRIDGE}] at *\ngrind"),
        ("unfold-grind", f"intros\ntry simp only [{unfold}] at *\ngrind"),
    ]
    if P:
        cands += [
            ("prem-grind",
             f"intros\n{haves}try simp only [{BRIDGE}] at *\ngrind"),
            ("prem-unfold-grind",
             f"intros\n{haves}try simp only [{unfold}] at *\ngrind"),
            ("solve_by_elim",
             f"intros\nsolve_by_elim (maxDepth := 8) [{', '.join(P)}]"),
        ]
        if G:
            cands += [
                ("goal-unfold-grind",
                 f"intros\n{haves}try simp only [{BRIDGE}] at *\n{goal_unfold}grind"),
                ("goal-unfold-sbe",
                 f"intros\n{goal_unfold}solve_by_elim (maxDepth := 10) [{', '.join(P)}]"),
            ]
    # set equality by extensionality: eq set X Y  <-  Subq X Y, Subq Y X
    cands.append(
        ("ext-grind",
         f"intros\n{haves}try simp only [{BRIDGE}] at *\n"
         f"refine (b_eq set _ _).mp (set_ext _ _ ?_ ?_)\n"
         f"all_goals (try simp only [Subq]\n  intros\n  try simp only [{BRIDGE}] at *\n  grind)"))
    return cands


class Prover:
    def __init__(self, decls, corpus_path, statements):
        self.decls = decls
        self.index_of = {d.name: d.index for d in decls}
        self.by_name = {d.name: d for d in decls}
        self.search = Search(decls)
        self.thf = THF(decls)
        attach_prim_indices(self.thf, corpus_path)
        self.sigs = statements

    def hints(self, goal, slices=(16, 32, 64), vampire_timeout=5):
        """Return (premises, defs, vampire_status).

        Tries Vampire on several premise-slice sizes, smallest first: the
        failure diagnosis showed Vampire often fails from too MANY
        irrelevant premises rather than missing ones, so a small slice is
        tried before larger, safer ones. First proof found wins."""
        ranked = [n for n, _ in self.search.rank(goal.index, limit=max(slices))]
        facts = [n for n in ranked if self.by_name[n].kind in ("THM", "AXIOM")]
        goal_defs = sorted(s for s in goal.stmt_syms
                           if s in self.by_name and self.by_name[s].kind == "DEF"
                           and s not in ("True", "False", "not", "and", "or",
                                         "iff", "eq", "neq", "ex"))
        status = "skipped"
        for k in slices:
            try:
                text, ids, _ = self.thf.problem(goal, ranked[:k])
            except Unsupported:
                status = "unsupported"
                break
            status, used = run_vampire(text, timeout=vampire_timeout)
            if status == "Theorem":
                vf = [ids[u] for u in used if u in ids]
                vdefs = sorted({self._def_of(u) for u in used} - {None})
                return vf, sorted(set(goal_defs) | set(vdefs)), f"Theorem@{k}"
        return facts[:8], goal_defs, status

    def goal_defs(self, goal):
        """Definitions the goal statement itself mentions (not the logical
        connectives, which the bridge lemmas handle)."""
        return sorted(s for s in goal.stmt_syms
                      if s in self.by_name and self.by_name[s].kind == "DEF"
                      and s not in ("True", "False", "not", "and", "or",
                                    "iff", "eq", "neq", "ex"))

    def _def_of(self, vampire_id):
        if not vampire_id.endswith("_def"):
            return None
        for d in self.decls:
            if d.kind == "DEF" and ident(d.name) + "_def" == vampire_id:
                return d.name
        return None

    def attempt_batch(self, goal, cands, timeout=120, single_timeout=60):
        """Check every candidate for one goal in a single Lean process.
        Returns list of (label, ok, reason)."""
        sig = self.sigs[goal.name]
        parts = ["import Lean", "import Bridge",
                 "set_option Elab.async false",
                 "set_option maxRecDepth 8000",
                 "set_option maxHeartbeats 200000",
                 "set_option linter.unusedVariables false"]
        att_names = []
        for i, (label, script) in enumerate(cands):
            att = f"attempt__{i}"
            att_names.append((att, label))
            body = "".join(f"  {ln}\n" for ln in script.strip().splitlines())
            parts.append(f"namespace Megalodon\ntheorem {att}{sig} := by\n"
                         f"{body}end Megalodon")
            parts.append(_GUARD.replace("{att}", att)
                         .replace("{orig}", _lean_name(goal.name))
                         .replace("GUARD ", f"GUARD[{att}] "))
        src = "\n".join(parts) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                         dir="/tmp") as fh:
            fh.write(src)
            path = fh.name
        try:
            r = subprocess.run([LEAN, path], capture_output=True, text=True,
                               timeout=timeout,
                               env={**os.environ, "LEAN_PATH": LIB})
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            os.unlink(path)
            # One slow candidate used up the whole batch's time, taking the
            # others down with it (43 of 140 baseline reconstruction failures
            # were exactly this). Retry each candidate alone, with its own
            # budget, so a fast proof is never killed by a slow neighbour.
            if len(cands) == 1:
                return [(cands[0][0], False, "timeout")]
            results = []
            for c in cands:
                r1 = self.attempt_batch(goal, [c], timeout=single_timeout)
                results += r1
                if r1[0][1]:
                    results += [(c2[0], False, "skipped: already proved")
                                for c2 in cands[len(results):]]
                    break
            return results
        else:
            os.unlink(path)

        # map error lines back to the attempt that contains them
        src_lines = src.splitlines()
        owner = {}
        cur = None
        for ln_no, ln in enumerate(src_lines, start=1):
            m = re.match(r"theorem (attempt__\d+)", ln)
            if m:
                cur = m.group(1)
            if ln.startswith("end Megalodon"):
                owner[ln_no] = cur
                cur = None
            elif cur:
                owner[ln_no] = cur
        # collect each attempt's error messages (message + continuation
        # lines), so an LLM can be shown exactly what Lean objected to
        errors = {}
        out_lines = out.splitlines()
        i = 0
        while i < len(out_lines):
            m = re.match(r".*?:(\d+):(\d+): error(?:\([^)]*\))?: ?(.*)", out_lines[i])
            if m:
                a = owner.get(int(m.group(1)))
                block = [m.group(3)]
                j = i + 1
                while j < len(out_lines) and not re.match(r".*?:\d+:\d+: ", out_lines[j]):
                    block.append(out_lines[j])
                    j += 1
                if a:
                    errors.setdefault(a, []).append("\n".join(block).strip())
                i = j
            else:
                i += 1

        results = []
        for att, label in att_names:
            if att in errors:
                results.append((label, False,
                                "lean error: " + "\n---\n".join(errors[att])[:1200]))
                continue
            m = re.search(rf"GUARD\[{att}\] samestmt (\w+)", out)
            if not m or m.group(1) != "true":
                results.append((label, False, "statement mismatch/missing"))
                continue
            m = re.search(rf"GUARD\[{att}\] used ?(.*)", out)
            used = m.group(1).split() if m else []
            if "sorryAx" in used:
                results.append((label, False, "sorryAx"))
                continue
            ok, leak = leak_free(used, goal.index, self.index_of)
            results.append((label, ok, "ok" if ok else f"leak {leak}"))
        return results

    def prove(self, goal, extra_candidates=()):
        premises, defs, vstatus = self.hints(goal)
        cands = candidate_tactics(premises, defs, self.goal_defs(goal))
        if not vstatus.startswith("Theorem"):
            # Without a Vampire proof, premise-heavy grind attempts succeeded
            # 0/19 times on the sample while costing ~30s each; keep only
            # the cheap, fast-failing strategies.
            cands = [c for c in cands
                     if c[0] in ("intro-grind", "unfold-grind", "solve_by_elim",
                                 "goal-unfold-sbe", "ext-grind")]
        cands += list(extra_candidates)
        results = self.attempt_batch(goal, cands)
        winner = next((lbl for lbl, ok, _ in results if ok), None)
        return {"goal": goal.name, "index": goal.index, "vampire": vstatus,
                "premises": premises, "defs": defs,
                "results": results, "proved_by": winner}
