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

/-- The communication relation: rfe ∪ fr ∪ co.
    Defined over protocol events, parameterized by the compound protocol. -/
inductive com (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
    (e₁ e₂ : Event n) : Prop where
  | rfe : @Herd.rfe n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | fr : @Herd.fr n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | co : @Herd.co n cmp b init e₁ e₂ → com cmp b init e₁ e₂

/-- The hierarchical ordering: PPOi ∪ com, carrying communication evidence.

    Like RF's `readsFrom.cases`, each constructor is descriptive — it shows
    WHAT communication happened. The ordering IS the communication.

    - `ppoi`: local cache/thread ordering — CompoundMCM proves compound
      linearization events are ordered
    - `com`: communication ordering — rfe/co/fr each carry their specific
      downgrade/communication structure at a common level

    The PartialOrder is the transitive closure of this relation.
    Acyclicity is proven directly from the communication evidence. -/
inductive hierarchicallyOrdered
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e₁ e₂ : Event n) : Prop where
  /-- PPOi: local cache ordering via CompoundMCM (compound linearization events ordered) -/
  | ppoi (h : @PPOi n b e₁ e₂)
  /-- COM: communication ordering (rfe/co/fr, each with communication evidence) -/
  | com (h : com cmp b init e₁ e₂)

/-- hierarchicallyOrdered = PPOi ∪ com -/
theorem hierarchicallyOrdered_iff_ppoi_union_com
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    : @hierarchicallyOrdered n cmp b init e₁ e₂ ↔ (@PPOi n b ∪ com cmp b init) e₁ e₂ := by
  constructor
  · intro h; cases h with
    | ppoi h => exact Or.inl h
    | com h => exact Or.inr h
  · intro h; cases h with
    | inl h => exact .ppoi h
    | inr h => exact .com h

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
