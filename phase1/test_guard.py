"""Controls for the leak guard. Every benchmark number depends on this
guard being right, so it is tested in both directions. Run before trusting
any result:

    cd phase1 && python3 test_guard.py

History: the first version of the guard read only the proof's statement,
not its body (Lean 4.34's ConstantInfo.value? hides theorem proofs unless
called with allowOpaque := true). Both cheating controls below PASSED it.
Caught by these controls, fixed, and kept here so it cannot regress.
"""
import sys

from library import load
from itp import load_statements, check, leak_free

decls = load("../data/corpus.sexpr")
index_of = {d.name: d.index for d in decls}
sigs = load_statements()
thms = {d.name: d for d in decls if d.kind == "THM"}
failures = 0


def expect(label, target, tactic, want_accept):
    global failures
    t = thms[target]
    ok, why, used = check(t.name, sigs[t.name], tactic)
    accepted = ok and leak_free(used, t.index, index_of)[0]
    good = accepted == want_accept
    failures += not good
    print(f"{'PASS' if good else 'FAIL'}  {label}: accepted={accepted} "
          f"(expected {want_accept})  [{why}; used={used}]")


# 1. citing the target itself must be rejected
expect("cite target itself", "orIL", "exact orIL", False)
# 2. citing a LATER theorem with the identical statement must be rejected
#    (pair_Sigma and lamI share a content hash; lamI comes later)
a, b = thms["pair_Sigma"], thms["lamI"]
early, late = (a, b) if a.index < b.index else (b, a)
expect("cite later identical theorem", early.name, f"exact {late.name}", False)
# 3. a genuine proof must be accepted
expect("genuine proof", "orIL", "intro P Q hp r f g\nexact f hp", True)
# 4. an EARLIER theorem may be cited: prove a later one of the identical
#    pair by citing the earlier one -- legitimate reuse, must be accepted
expect("cite earlier identical theorem", late.name, f"exact {early.name}", True)

print("ALL GUARD CONTROLS PASS" if not failures else f"{failures} CONTROL(S) FAILED")
sys.exit(1 if failures else 0)
