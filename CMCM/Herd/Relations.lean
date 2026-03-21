import CMCM.Herd.Defs
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
  | ppoi : PPOi e₁ e₂ → com cmp b init e₁ e₂
  | rfe : @Herd.rfe n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | fr : @Herd.fr n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | co : @Herd.co n cmp b init e₁ e₂ → com cmp b init e₁ e₂

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x

/-- A relation is acyclic if no element is reachable from itself
    via the transitive closure. -/
def acyclic (rel : α → α → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen rel x x

theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ acyclic rel := by
  simp [cyclic, acyclic]

/-! ## CMCM theorem statement -/

/-- The Compositional Memory Consistency Model (CMCM):
    `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`

    States that for any compound protocol, behaviour, and initial state,
    the communication relation has no cycles. -/
def CMCM (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  acyclic (com cmp b init)

end Herd
