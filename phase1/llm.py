"""Phase 1 LLM plug-in: an UNTRUSTED proposer of Lean tactic scripts.

Implements the sketch's feedback arrow: propose -> Lean checks -> on
failure, Lean's actual error goes back to the model for another round.

What the model sees (and nothing else):
  * the goal statement, exactly as the library states it
  * the Megalodon definitions the goal uses
  * the facts Search/Vampire selected -- all strictly BEFORE the goal,
    statements only
  * the bridge lemmas to native logic
  * on later rounds, its own previous attempt and Lean's error
It never sees the goal's original proof or anything after the goal.

Whatever it writes is checked exactly like every other candidate: Lean
kernel + statement-identity check + leak guard (see itp.py).

Credentials come from ../.env (LLM_API_KEY, LLM_BASE_URL); the key is never
logged or written anywhere else.
"""
import json
import os
import re
import time
import urllib.error
import urllib.request

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
DEFAULT_MODEL = "openai/gpt-oss-120b"


def _env():
    path = os.path.join(ROOT, ".env")
    env = {}
    if os.path.exists(path):
        for line in open(path):
            if "=" in line:
                k, v = line.strip().split("=", 1)
                env[k] = v
    env.update({k: v for k, v in os.environ.items() if k.startswith("LLM_")})
    if "LLM_API_KEY" not in env or "LLM_BASE_URL" not in env:
        raise RuntimeError("LLM_API_KEY / LLM_BASE_URL missing (see README)")
    return env


def chat(messages, model=DEFAULT_MODEL, max_tokens=16000, temperature=0.2,
         retries=3):
    env = _env()
    body = json.dumps({"model": model, "messages": messages,
                       "max_tokens": max_tokens,
                       "temperature": temperature}).encode()
    for attempt in range(retries):
        req = urllib.request.Request(
            env["LLM_BASE_URL"].rstrip("/") + "/chat/completions", data=body,
            headers={"Authorization": f"Bearer {env['LLM_API_KEY']}",
                     "Content-Type": "application/json"})
        try:
            r = json.load(urllib.request.urlopen(req, timeout=180))
            return r["choices"][0]["message"].get("content") or ""
        except (urllib.error.URLError, TimeoutError, KeyError) as e:
            if attempt == retries - 1:
                raise
            time.sleep(2 * (attempt + 1))
    return ""


# ------------------------------------------------------------ Lean context
class LeanContext:
    """Declaration texts from the verified library, for building prompts.
    Theorems are shown as statements only -- never with their proofs."""

    def __init__(self, meglib_path=os.path.join(ROOT, "lib", "MegLib.lean")):
        self.text = {}
        for line in open(meglib_path, encoding="utf-8"):
            m = re.match(r"(axiom|noncomputable def|theorem) (\S+)", line)
            if not m:
                continue
            kind, name = m.group(1), m.group(2)
            line = line.rstrip()
            if kind == "theorem":
                line = line.split(" := ", 1)[0]
            self.text[name] = line

    def show(self, names, limit_chars=12000):
        out, total = [], 0
        for n in names:
            t = self.text.get(n)
            if not t:
                continue
            if total + len(t) > limit_chars:
                break
            out.append(t)
            total += len(t)
        return "\n".join(out)


SYSTEM = """You write Lean 4 tactic proofs (Lean 4 core only, NO Mathlib).

The library encodes Megalodon's higher-order set theory inside `namespace
Megalodon`. Its logic is ENCODED, not Lean's native logic:
  Megalodon.and P Q, Megalodon.or P Q, Megalodon.not P, Megalodon.iff P Q,
  Megalodon.ex T P, Megalodon.eq T x y, Megalodon.neq T x y,
  Megalodon.True, Megalodon.False
are definitions. These proved bridge lemmas convert them to native logic:
  b_True, b_False, b_not, b_and, b_or, b_iff, b_eq, b_neq, b_ex
e.g. `simp only [b_and, b_or, b_ex, b_eq, b_not, b_iff, b_True, b_False, b_neq] at *`
turns encoded goals/hypotheses into ∧ ∨ ∃ = ¬ ↔ True False.
Other definitions (Subq, Sing, ordsucc, ...) can be unfolded with
`simp only [Name] at *` or `unfold Name`, or used definitionally.
Useful tactics: intro, intros, exact, apply, refine, constructor, cases,
rcases, obtain, have, simp only, rw, grind, solve_by_elim, assumption.
`grind` is available and strong once the logic is native.

IMPORTANT about sets: `set`, `In`, `Empty`, `Union`, `Power`, `Repl`, `Eps_i`
are OPAQUE axioms, not inductive types. `cases`/`rcases`/`constructor`/
`⟨...⟩` do NOT work on `In x (Union X)` etc. Membership facts can only be
introduced or eliminated by applying the listed facts (e.g. a lemma like
UnionE / UPairE / ReplE / SepE turns membership into an encoded `ex`/`or`/
`and`, which the bridge lemmas then make native, after which rcases works).
Induction is not a tactic here: apply an induction principle from the
available facts (e.g. `apply nat_ind` / `apply In_ind`) with a suitable
predicate, e.g. `refine nat_ind (fun n => ...) ?_ ?_`.
The goal state after `intros` is shown to you; work from it. Names in the
statement like `x1445` are BOUND variables, NOT in scope: start your script
with `intro` and choose your own names for every binder/hypothesis, and
only refer to names you introduced.

Rules:
- Use ONLY the facts listed as available, plus the bridge lemmas and
  definitions shown. Do NOT use the theorem being proved.
- Reply with exactly one ```lean code block containing ONLY the tactic
  script (the lines after `:= by`), no `theorem` header.
"""


def _extract(reply):
    m = re.findall(r"```(?:lean4?|)\s*\n(.*?)```", reply, re.S)
    if m:
        script = m[-1]
    elif "```" in reply:
        # unclosed fence (reply cut off): take everything after the last opener
        script = re.split(r"```(?:lean4?|)\s*\n?", reply)[-1]
    else:
        script = reply
    script = script.strip()
    # tolerate the model repeating the header anyway
    script = re.sub(r"^\s*(theorem|lemma|example)\b.*?:=\s*by\s*\n", "",
                    script, flags=re.S)
    if script.startswith("by\n"):
        script = script[3:]
    lines = script.splitlines()
    if lines:
        pad = min((len(l) - len(l.lstrip()) for l in lines if l.strip()),
                  default=0)
        lines = [l[pad:] for l in lines]
    return "\n".join(lines).strip()


def build_prompt(ctx, goal_name, goal_sig, defs, premises, state=None):
    return (
        f"Prove this theorem (the statement is fixed; write only the tactic script):\n\n"
        f"theorem {goal_name}{goal_sig} := by\n  ...\n\n"
        + (f"Lean's goal state after `intros` and converting encoded logic to native "
           f"(`intros; simp only [b_*] at *`):\n{state}\n\n" if state else "")
        + f"Definitions it uses:\n{ctx.show(defs) or '(none)'}\n\n"
        f"Available facts (you may use these, by name):\n"
        f"{ctx.show(premises) or '(none)'}\n"
    )


def goal_state(prover, goal):
    """Ask Lean for the goal state after intros + bridging, by deliberately
    leaving it unsolved and reading the 'unsolved goals' error."""
    from itp import BRIDGE
    res = prover.attempt_batch(
        goal, [("probe", f"intros\ntry simp only [{BRIDGE}] at *\ndone")])
    why = res[0][2]
    m = re.search(r"unsolved goals\s*\n(.*)", why, re.S)
    return m.group(1).strip()[:3000] if m else None


def llm_rounds(prover, goal, premises, defs, rounds=3, model=DEFAULT_MODEL,
               log=None):
    """Feedback loop: propose, check, feed the Lean error back. Returns
    (proved_label or None, transcript list)."""
    ctx = getattr(prover, "_lean_ctx", None) or LeanContext()
    prover._lean_ctx = ctx
    sig = prover.sigs[goal.name]
    state = goal_state(prover, goal)
    msgs = [{"role": "system", "content": SYSTEM},
            {"role": "user", "content": build_prompt(ctx, goal.name, sig, defs,
                                                     premises, state)}]
    transcript = []
    for r in range(1, rounds + 1):
        try:
            reply = chat(msgs, model=model)
        except Exception as e:
            transcript.append({"round": r, "error": f"api: {type(e).__name__}"})
            break
        script = _extract(reply)
        label = f"llm-r{r}"
        res = prover.attempt_batch(goal, [(label, script)])
        _, ok, why = res[0]
        transcript.append({"round": r, "script": script, "ok": ok, "why": why})
        if log:
            head = " | ".join(script.splitlines()[:4])
            log(f"    round {r}: script: {head[:200]}")
            log(f"             -> {'OK' if ok else why.splitlines()[0][:160]}")
        if ok:
            return label, transcript
        msgs += [{"role": "assistant", "content": f"```lean\n{script}\n```"},
                 {"role": "user", "content":
                  f"Lean rejected that proof:\n{why}\n\n"
                  f"Fix it. Reply with one ```lean block, tactic script only."}]
    return None, transcript
