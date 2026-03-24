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

/-- The hierarchical ordering: PPOi ∪ com, with each constructor carrying
    BOTH the communication evidence (the protocol mechanism) AND the ordering
    consequence (eventLt ranking decrease).

    Like RF's `readsFrom.cases`, each constructor is descriptive — it shows
    WHAT communication happened and WHAT ordering it establishes.

    - `ppoi`: local cache/thread ordering via CompoundMCM + eventLt consequence
    - `com`: communication ordering (rfe/co/fr) + eventLt consequence

    The PartialOrder is built from these communication events, with
    irreflexivity and transitivity proven via the eventLt component. -/
inductive hierarchicallyOrdered
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e₁ e₂ : Event n) : Prop where
  /-- PPOi: local cache ordering, CompoundMCM gives linearization + ranking decrease -/
  | ppoi (comm : @PPOi n b e₁ e₂)
         (h₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
         (h₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
         (hlt : eventLt h₁ h₂)
  /-- COM: communication ordering (rfe/co/fr) + ranking decrease -/
  | com (comm : com cmp b init e₁ e₂)
        (h₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
        (h₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
        (hlt : eventLt h₁ h₂)

/-- hierarchicallyOrdered implies eventLt (extract the ranking consequence). -/
theorem hierarchicallyOrdered_eventLt
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    (h : @hierarchicallyOrdered n cmp b init e₁ e₂)
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : eventLt h₁ h₂ := by
  cases h with
  | ppoi _ h₁' h₂' hlt =>
    have : h₁' = h₁ := Subsingleton.elim _ _; subst this
    have : h₂' = h₂ := Subsingleton.elim _ _; subst this
    exact hlt
  | com _ h₁' h₂' hlt =>
    have : h₁' = h₁ := Subsingleton.elim _ _; subst this
    have : h₂' = h₂ := Subsingleton.elim _ _; subst this
    exact hlt

/-- PPOi ∪ com → hierarchicallyOrdered (given eventLt proofs). -/
theorem hierarchicallyOrdered_of_ppoi_union_com
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : (@PPOi n b ∪ com cmp b init) e₁ e₂)
    (hlt : eventLt (hknow cmp b init e₁) (hknow cmp b init e₂))
    : @hierarchicallyOrdered n cmp b init e₁ e₂ := by
  cases h with
  | inl h => exact .ppoi h _ _ hlt
  | inr h => exact .com h _ _ hlt

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
