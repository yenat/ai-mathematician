/-
Lean goals, library statements, definitions and proofs as MeTTa expressions.

  ⊢ eq set (add_nat x y) z     ~>   (eq set (add_nat x y) z)
  ∀ x : set, P x → Q x          ~>   (∀ (x set) (→ (P x) (Q x)))
  fun x : set => t              ~>   (λ (x set) t)

Constants lose the `Megalodon.` prefix, so a goal and the library lemma
that closes it are written in the same vocabulary and MeTTa can unify them.
Bound variables are named by depth (`_b0`, `_b1`, ...), so statements that
differ only in the names of bound variables are written identically.

  goal_sexpr          tactic: reports the main goal and its typed hypotheses
  #export_library     every library theorem's statement: THM <name> <type>
  #export_metta       every declaration, with types, bodies and proofs, as
                      (MkIndexed i (MkAxiom name type))
                      (MkIndexed i (MkDefinition name body type))
                      (MkIndexed i (MkTheorem name proof type))
  #metta_roundtrip "file"
                      reads an #export_metta file back into Lean terms and
                      compares each with the declaration it came from

#export_metta is strict: it fails instead of writing something it cannot read
back (metavariables, free variables, universe levels, implicit binders,
names that would collide), and keeps `let` as (let (x T v) body).
goal_sexpr and #export_library keep their earlier, lenient output.
-/
import Lean
open Lean Meta Elab Tactic

namespace Sexpr

def sym (n : Name) : String :=
  let s := n.eraseMacroScopes.toString (escape := false)
  let s := if s.startsWith "Megalodon." then (s.drop 10).toString else s
  let s := s.map fun c => if c == '(' || c == ')' || c == ' ' || c == '"' || c == ';' then '_' else c
  if s.startsWith "$" then "_" ++ s else s

/-- Words the writer itself uses; a constant with one of these names could
not be read back. -/
def reserved (s : String) : Bool :=
  ["λ", "∀", "→", "let", "proj", "Prop", "Type", "meg_Type", "_"].contains s
    || (s.startsWith "_b" && (s.drop 2).toString.all Char.isDigit)
    || s.all Char.isDigit

/-- A constant written in strict mode must keep its name exactly. -/
def strictSym (n : Name) : MetaM String := do
  let s := sym n
  let plain := n.toString (escape := false)
  let plain := if plain.startsWith "Megalodon." then (plain.drop 10).toString else plain
  if n.hasMacroScopes || plain.any (fun c => c == '(' || c == ')' || c == ' ' || c == '"' || c == ';')
      || plain.startsWith "$" || reserved plain then
    throwError "Sexpr: constant {n} cannot be written without loss"
  -- Names lose `Megalodon.`, so a constant outside it must not share a name
  -- with one inside it (Lean's own True, Empty, Union ...).
  if !(`Megalodon).isPrefixOf n && (← getEnv).contains (`Megalodon ++ n) then
    throwError "Sexpr: {n} would be read back as Megalodon.{n}"
  return s

partial def go (e : Expr) (bs : Array String) (strict : Bool := false) : MetaM String := do
  match e with
  | .bvar i => return bs[bs.size - 1 - i]!
  | .fvar id =>
    if strict then throwError "Sexpr: free variable in a closed term"
    return sym (← id.getDecl).userName
  | .const c us =>
    if strict && !us.isEmpty then throwError "Sexpr: universe levels on {c}"
    if strict then strictSym c else return sym c
  | .sort l =>
    if strict && !(l.isZero || l == Level.one) then throwError "Sexpr: universe {l}"
    return if l.isZero then "Prop" else "Type"
  | .lit (.natVal n) => return toString n
  | .lit (.strVal s) =>
    if strict && (s.any fun c => c == '"' || c == '\\') then throwError "Sexpr: string {s}"
    return s!"\"{s}\""
  | .mdata _ b => go b bs strict
  | .mvar _ =>
    if strict then throwError "Sexpr: metavariable"
    return "?"
  | .proj s i b => return s!"(proj {← if strict then strictSym s else pure (sym s)} {i} {← go b bs strict})"
  | .letE _ t v b _ =>
    if strict then
      let x := s!"_b{bs.size}"
      return s!"(let ({x} {← go t bs strict} {← go v bs strict}) {← go b (bs.push x) strict})"
    go (b.instantiate1 v) bs
  | .app .. =>
    let args ← e.getAppArgs.mapM (go · bs strict)
    return s!"({← go e.getAppFn bs strict} {" ".intercalate args.toList})"
  | .forallE n t b bi =>
    if strict && bi != .default then throwError "Sexpr: implicit binder {n}"
    if b.hasLooseBVar 0 then
      let v := s!"_b{bs.size}"
      return s!"(∀ ({v} {← go t bs strict}) {← go b (bs.push v) strict})"
    else
      return s!"(→ {← go t bs strict} {← go b (bs.push "_") strict})"
  | .lam n t b bi =>
    if strict && bi != .default then throwError "Sexpr: implicit binder {n}"
    let v := s!"_b{bs.size}"
    return s!"(λ ({v} {← go t bs strict}) {← go b (bs.push v) strict})"

def ofExpr (e : Expr) : MetaM String := do go (← instantiateMVars e) #[]
def ofExprStrict (e : Expr) : MetaM String := do go (← instantiateMVars e) #[] true

/-! Reading back. -/

inductive S where
  | atom : String → S
  | str : String → S
  | list : List S → S
  deriving Inhabited

partial def parseList (cs : List Char) (acc : Array S) : Except String (List S × List Char) :=
  match cs with
  | [] => .error "unclosed ("
  | c :: rest =>
    if c.isWhitespace then parseList rest acc
    else if c == ')' then .ok (acc.toList, rest)
    else do
      let (s, rest) ← parseOne cs
      parseList rest (acc.push s)
where
  parseOne (cs : List Char) : Except String (S × List Char) :=
    match cs with
    | '(' :: rest => do
      let (xs, rest) ← parseList rest #[]
      .ok (.list xs, rest)
    | '"' :: rest =>
      let body := rest.takeWhile (· != '"')
      .ok (.str (String.ofList body), (rest.drop (body.length + 1)))
    | _ =>
      let tok := cs.takeWhile fun c => !(c.isWhitespace || c == '(' || c == ')')
      if tok.isEmpty then .error "unexpected )" else
      .ok (.atom (String.ofList tok), cs.drop tok.length)

def parse (s : String) : Except String S := do
  let cs := s.toList.dropWhile Char.isWhitespace
  let (e, rest) ← parseList.parseOne cs
  unless rest.all Char.isWhitespace do .error "trailing text"
  .ok e

def clash : List String :=
  ["Empty", "Error", "False", "True", "Type", "and", "case", "collapse", "empty", "if",
   "let", "match", "not", "or", "quote", "superpose", "unify"]

/-- The constant a written name stands for; fails if none or more than one. -/
def constOf (env : Environment) (s : String) : Except String Name :=
  let bases := [s] ++ (if s.startsWith "meg_" && clash.contains (s.drop 4).toString
                        then [(s.drop 4).toString] else [])
  let cands := bases.flatMap fun b =>
    let n := b.toName
    [`Megalodon ++ n, n].filter fun c => env.contains c && sym c == s
  -- strict writing never emits a non-Megalodon constant that shares its
  -- name with a Megalodon one, so a Megalodon reading wins
  let cands := match cands.filter (`Megalodon).isPrefixOf with
    | [] => cands
    | ms => ms
  match cands.eraseDups with
  | [c] => .ok c
  | [] => .error s!"unknown constant {s}"
  | cs => .error s!"{s} names {cs.length} constants: {cs}"

partial def decode (env : Environment) (e : S) (ctx : Array String) : Except String Expr :=
  match e with
  | .str s => .ok (.lit (.strVal s))
  | .atom a =>
    -- the innermost binder of that name: its distance from the end is the index
    match ctx.toList.reverse.findIdx? (· == a) with
    | some i => .ok (.bvar i)
    | none =>
      if a == "Prop" then .ok (.sort .zero)
      else if a == "Type" || a == "meg_Type" then .ok (.sort Level.one)
      else if a.all Char.isDigit && !a.isEmpty then .ok (.lit (.natVal a.toNat!))
      else return .const (← constOf env a) []
  | .list [.atom "λ", .list [.atom x, t], b] => do
    .ok (.lam x.toName (← decode env t ctx) (← decode env b (ctx.push x)) .default)
  | .list [.atom "∀", .list [.atom x, t], b] => do
    .ok (.forallE x.toName (← decode env t ctx) (← decode env b (ctx.push x)) .default)
  | .list [.atom "→", a, b] => do
    .ok (.forallE `_ (← decode env a ctx) (← decode env b (ctx.push "_")) .default)
  | .list [.atom "let", .list [.atom x, t, v], b] => do
    .ok (.letE x.toName (← decode env t ctx) (← decode env v ctx) (← decode env b (ctx.push x)) false)
  | .list [.atom "proj", .atom s, .atom i, b] => do
    .ok (.proj (← constOf env s) i.toNat! (← decode env b ctx))
  | .list (f :: args@(_ :: _)) => do
    let f ← decode env f ctx
    .ok (mkAppN f (← args.toArray.mapM (decode env · ctx)))
  | .list _ => .error "bad expression"

partial def stripMData : Expr → Expr
  | .mdata _ b => stripMData b
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i b => .proj s i (stripMData b)
  | e => e

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

/-- Every Megalodon declaration of the imported library, with its type and
its body or proof. Order is Lean's; callers sort by source position. -/
elab "#export_metta" : command => do
  let env ← getEnv
  let mut i := 0
  for (n, ci) in env.constants.map₁.toList do
    unless (`Megalodon).isPrefixOf n && !n.isInternal && (env.getModuleIdxFor? n).isSome do continue
    unless ci.levelParams.isEmpty do throwError "Sexpr: universe parameters on {n}"
    let name ← Elab.Command.liftTermElabM (Sexpr.strictSym n)
    let ty ← Elab.Command.liftTermElabM (Sexpr.ofExprStrict ci.type)
    let rec_ ← match ci with
      | .axiomInfo _ => pure s!"(MkAxiom {name} {ty})"
      | .defnInfo d => pure s!"(MkDefinition {name} {← Elab.Command.liftTermElabM (Sexpr.ofExprStrict d.value)} {ty})"
      | .thmInfo t => pure s!"(MkTheorem {name} {← Elab.Command.liftTermElabM (Sexpr.ofExprStrict t.value)} {ty})"
      | .opaqueInfo _ => throwError "Sexpr: opaque {n}"
      | _ => pure ""
    if rec_ != "" then
      IO.println s!"(MkIndexed {i} {rec_})"
      i := i + 1

/-- Read an #export_metta file back and compare every type, body and proof
with the declaration it names (up to binder names). -/
elab "#metta_roundtrip " path:str : command => do
  let env ← getEnv
  let text ← IO.FS.readFile path.getString
  let mut ok := 0
  let mut bad : Array String := #[]
  let mut seen : NameSet := {}
  for line in text.splitOn "\n" do
    unless line.startsWith "(MkIndexed " do continue
    let res : Except String Name := do
      let e ← Sexpr.parse line
      let .list [_, _, .list rec_] := e | .error "not an MkIndexed record"
      let (kind, nm, parts) ← match rec_ with
        | [.atom k, .atom nm, t] => pure (k, nm, [t])
        | [.atom k, .atom nm, v, t] => pure (k, nm, [v, t])
        | _ => .error "bad record"
      let c ← Sexpr.constOf env nm
      let some ci := env.find? c | .error s!"{c} missing"
      let orig ← match kind, ci, parts with
        | "MkAxiom", .axiomInfo _, [t] => pure [(t, ci.type)]
        | "MkDefinition", .defnInfo d, [v, t] => pure [(v, d.value), (t, ci.type)]
        | "MkTheorem", .thmInfo d, [v, t] => pure [(v, d.value), (t, ci.type)]
        | _, _, _ => .error s!"{nm}: kind {kind} does not match Lean's"
      for (s, o) in orig do
        let d ← Sexpr.decode env s #[]
        unless d.eqv (Sexpr.stripMData o) do .error s!"{nm}: differs from Lean"
      pure c
    match res with
    | .ok c => ok := ok + 1; seen := seen.insert c
    | .error msg => bad := bad.push msg
  let mut missing := 0
  for (n, ci) in env.constants.map₁.toList do
    if (`Megalodon).isPrefixOf n && !n.isInternal && (env.getModuleIdxFor? n).isSome
        && (ci matches .axiomInfo _ || ci matches .defnInfo _ || ci matches .thmInfo _)
        && !seen.contains n then missing := missing + 1
  IO.println s!"ROUNDTRIP {ok} exact, {bad.size} failed, {missing} declarations not in file"
  for b in bad.toList.take 10 do IO.println s!"  {b}"

/-- One declaration's statement, strictly: `TYPE <name> <type>`. Used for the
test goals, which are stated (with `sorry`) but are not library entries. -/
elab "#export_type " id:ident : command => do
  let some ci := (← getEnv).find? id.getId | throwError "unknown {id.getId}"
  let s ← Elab.Command.liftTermElabM (Sexpr.ofExprStrict ci.type)
  IO.println s!"TYPE {Sexpr.sym id.getId} {s}"

/-- Audit, outside the MeTTa pipeline: read `(: proof statement)` lines (MeTTa
proofs written by ../metta/replay.metta) back into Lean terms and add each as a
theorem, so Lean's own kernel checks what the MeTTa kernel accepted. -/
elab "#check_metta_proof " path:str : command => do
  let env ← getEnv
  let text ← IO.FS.readFile path.getString
  let mut k := 0
  for line in text.splitOn "\n" do
    unless line.startsWith "(: " do continue
    k := k + 1
    match (do
        let .list [_, p, t] ← Sexpr.parse line | .error "not (: proof statement)"
        pure (← Sexpr.decode env p #[], ← Sexpr.decode env t #[]) : Except String (Expr × Expr)) with
    | .error e => IO.println s!"AUDIT {k} unreadable: {e}"
    | .ok (p, t) =>
      let n := Name.mkSimple s!"metta_audit_{k}"
      -- the kernel itself, synchronously: addDecl would report errors later
      match Kernel.Environment.addDecl env.toKernelEnv (← getOptions)
          (.thmDecl { name := n, levelParams := [], type := t, value := p }) with
      | .ok _ => IO.println s!"AUDIT {k} accepted by Lean's kernel"
      | .error _ => IO.println s!"AUDIT {k} rejected by Lean's kernel"
