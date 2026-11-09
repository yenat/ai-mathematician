/-
Lean goals and library statements as MeTTa expressions.

  ⊢ eq set (add_nat x y) z     ~>   (eq set (add_nat x y) z)
  ∀ x : set, P x → Q x          ~>   (∀ (x set) (→ (P x) (Q x)))

Constants lose the `Megalodon.` prefix, so a goal and the library lemma
that closes it are written in the same vocabulary and MeTTa can unify them.
Bound variables are named by depth (`_b0`, `_b1`, ...), so statements that
differ only in the names of bound variables are written identically.
`goal_sexpr` is a tactic that changes nothing and reports the main goal and
its hypotheses; `#export_library` prints every library theorem.
-/
import Lean
open Lean Meta Elab Tactic

namespace Sexpr

def sym (n : Name) : String :=
  let s := n.eraseMacroScopes.toString (escape := false)
  let s := if s.startsWith "Megalodon." then (s.drop 10).toString else s
  let s := s.map fun c => if c == '(' || c == ')' || c == ' ' || c == '"' || c == ';' then '_' else c
  if s.startsWith "$" then "_" ++ s else s

partial def go (e : Expr) (bs : Array String) : MetaM String := do
  match e with
  | .bvar i => return bs[bs.size - 1 - i]!
  | .fvar id => return sym (← id.getDecl).userName
  | .const c _ => return sym c
  | .sort l => return if l.isZero then "Prop" else "Type"
  | .lit (.natVal n) => return toString n
  | .lit (.strVal s) => return s!"\"{s}\""
  | .mdata _ b => go b bs
  | .mvar _ => return "?"
  | .proj s i b => return s!"(proj {sym s} {i} {← go b bs})"
  | .letE _ _ v b _ => go (b.instantiate1 v) bs
  | .app .. =>
    let args ← e.getAppArgs.mapM (go · bs)
    return s!"({← go e.getAppFn bs} {" ".intercalate args.toList})"
  | .forallE n t b _ =>
    if b.hasLooseBVar 0 then
      let v := s!"_b{bs.size}"
      return s!"(∀ ({v} {← go t bs}) {← go b (bs.push v)})"
    else
      return s!"(→ {← go t bs} {← go b (bs.push "_")})"
  | .lam n t b _ =>
    let v := s!"_b{bs.size}"
    return s!"(λ ({v} {← go t bs}) {← go b (bs.push v)})"

def ofExpr (e : Expr) : MetaM String := do go (← instantiateMVars e) #[]

end Sexpr

/-- Report the main goal and its hypotheses as MeTTa expressions. -/
elab "goal_sexpr" : tactic => withMainContext do
  let mut out := s!"GOAL {← Sexpr.ofExpr (← getMainTarget)}"
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    out := out ++ s!"\nHYP {Sexpr.sym d.userName} {← Sexpr.ofExpr d.type}"
  logInfo out

/-- Print every theorem and axiom of the library: `THM <name> <statement>`. -/
elab "#export_library" : command => do
  let env ← getEnv
  for (n, ci) in env.constants.map₁.toList do
    if ci matches .thmInfo _ || ci matches .axiomInfo _ then
      if (`Megalodon).isPrefixOf n && !n.isInternal && (env.getModuleIdxFor? n).isSome then
        let s ← Elab.Command.liftTermElabM (Sexpr.ofExpr ci.type)
        IO.println s!"THM {Sexpr.sym n} {s}"
