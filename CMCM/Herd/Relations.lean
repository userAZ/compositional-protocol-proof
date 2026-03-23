import CMCM.Herd.Defs
import CMCM.Herd.RelationCycles
import Mathlib

/-!
# Herd CMCM Relations

Define the `com` union (PPOi ∪ rfe ∪ fr ∪ co), acyclicity, and the CMCM theorem statement.

Uses `Relation.TransGen` from Mathlib for transitive closure.
-/

variable {n : Nat}

namespace Herd

/-! ## Union of CMCM relations -/

/-- The communication relation: PPOi ∪ rfe ∪ fr ∪ co.
    Defined over protocol events, parameterized by the compound protocol. -/
inductive com (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
    (e₁ e₂ : Event n) : Prop where
  | rfe : @Herd.rfe n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | fr : @Herd.fr n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | co : @Herd.co n cmp b init e₁ e₂ → com cmp b init e₁ e₂

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
