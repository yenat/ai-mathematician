/-
Bridge between Megalodon's in-theory (Church-encoded) logic and Lean's
native connectives. Megalodon defines `and`, `or`, `not`, `iff`, `ex`,
Leibniz `eq` etc. as ordinary definitions; Lean's automation (`grind`,
`simp`, `solve_by_elim`) works far better on the native forms. Each lemma
below is proved here and checked by Lean's kernel, so rewriting with them
is sound -- nothing is assumed.
-/
import MegLib

namespace Megalodon

theorem b_True : Megalodon.True ↔ _root_.True :=
  ⟨fun _ => trivial, fun _ _ hp => hp⟩

theorem b_False : Megalodon.False ↔ _root_.False :=
  ⟨fun h => h _root_.False, fun h => h.elim⟩

theorem b_not (P : Prop) : Megalodon.not P ↔ ¬ P :=
  ⟨fun h hp => b_False.mp (h hp), fun h hp => (h hp).elim⟩

theorem b_and (P Q : Prop) : Megalodon.and P Q ↔ (P ∧ Q) :=
  ⟨fun h => h _ (fun a b => ⟨a, b⟩), fun ⟨a, b⟩ _ f => f a b⟩

theorem b_or (P Q : Prop) : Megalodon.or P Q ↔ (P ∨ Q) :=
  ⟨fun h => h _ Or.inl Or.inr,
   fun h _ f g => h.elim f g⟩

theorem b_iff (P Q : Prop) : Megalodon.iff P Q ↔ (P ↔ Q) :=
  ⟨fun h => let ⟨a, b⟩ := (b_and _ _).mp h; ⟨a, b⟩,
   fun ⟨a, b⟩ => (b_and _ _).mpr ⟨a, b⟩⟩

theorem b_eq (T : Type) (x y : T) : Megalodon.eq T x y ↔ x = y :=
  ⟨fun h => (h (fun a _ => a = x) rfl).symm,
   fun h => by subst h; exact fun _ hq => hq⟩

theorem b_neq (T : Type) (x y : T) : Megalodon.neq T x y ↔ x ≠ y :=
  ⟨fun h e => (b_not _).mp h ((b_eq T x y).mpr e),
   fun h => (b_not _).mpr (fun e => h ((b_eq T x y).mp e))⟩

theorem b_ex (T : Type) (P : T → Prop) : Megalodon.ex T P ↔ ∃ z, P z :=
  ⟨fun h => h _ (fun z hz => ⟨z, hz⟩), fun ⟨z, hz⟩ _ f => f z hz⟩

end Megalodon
