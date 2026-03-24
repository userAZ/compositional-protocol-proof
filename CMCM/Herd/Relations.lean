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

/-- The hierarchical ordering: PPOi ∪ com, carrying BOTH communication evidence
    AND the compound linearization ordering consequence.

    Like RF's `readsFrom.cases`, each constructor is descriptive — it shows
    WHAT communication happened AND WHAT ordering it establishes.

    - `ppoi`: local cache/thread ordering — CompoundMCM proves compound
      linearization events are ordered
    - `com`: communication ordering — rfe/co/fr each carry their specific
      downgrade/communication structure at a common level

    Each constructor also carries `hlin`: compoundLinEvent e₁ OB compoundLinEvent e₂.
    This makes the acyclicity proof trivial (compose hlin via OB transitivity,
    contradict OB irreflexivity).

    The real proof work is in constructing `hierarchicallyOrdered` instances —
    showing each edge type advances compound linearization events. -/
inductive hierarchicallyOrdered
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e₁ e₂ : Event n) : Prop where
  /-- PPOi: local cache ordering + compound lin events ordered -/
  | ppoi (comm : @PPOi n b e₁ e₂)
         (hlin : (@Herd.compoundLinEvent n cmp b init e₁).OrderedBefore n
                 (@Herd.compoundLinEvent n cmp b init e₂))
  /-- COM: communication ordering + compound lin events ordered -/
  | com (comm : com cmp b init e₁ e₂)
        (hlin : (@Herd.compoundLinEvent n cmp b init e₁).OrderedBefore n
                (@Herd.compoundLinEvent n cmp b init e₂))

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
