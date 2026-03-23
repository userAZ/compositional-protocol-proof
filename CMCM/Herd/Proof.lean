import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` via a well-founded (GLE, CLE) lexicographic order.

## Proof strategy

Since `globalLinearizationEventOfRequest` is `Prop`, the GLE and CLE of each event are
uniquely determined (all witnesses are propositionally equal). The `wrapper` axiom provides
canonical witnesses for every event.

Every `com` edge implies `hierarchicallyOrdered` on canonical witnesses:
- `co`: directly from definition (witnesses are propositionally equal to canonical)
- `rfe`: from `readsFrom.cases` (GLE/CLE ordering)
- `fr`: from the fr structure (w co-before e₂ gives hierarchicallyOrdered)
- `ppoi`: link lemma — bridges `CompoundLinearizationOrder` to (GLE, CLE) ordering

Since `hierarchicallyOrdered` is irreflexive and transitive, a cycle in `com` would give
`hierarchicallyOrdered he he` for some event e, contradicting irreflexivity.
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Properties of `hierarchicallyOrdered` -/

/-- The hierarchical order is irreflexive. -/
theorem hierarchicallyOrdered_irrefl
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : ¬ hierarchicallyOrdered h h := by
  intro hord
  unfold hierarchicallyOrdered gleOrderedBefore sameGleCleOrderedBefore at hord
  rcases hord with hgle | ⟨_, hcle⟩
  · exact Event.contradiction_of_reflexive_ordered_before n hgle
  · exact Event.contradiction_of_reflexive_ordered_before n hcle

/-- The hierarchical order is transitive. -/
theorem hierarchicallyOrdered_trans
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    {h₃ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₃}
    (h12 : hierarchicallyOrdered h₁ h₂)
    (h23 : hierarchicallyOrdered h₂ h₃)
    : hierarchicallyOrdered h₁ h₃ := by
  unfold hierarchicallyOrdered gleOrderedBefore sameGleCleOrderedBefore at *
  rcases h12 with hgle12 | ⟨hgle_eq12, hcle12⟩
  · rcases h23 with hgle23 | ⟨hgle_eq23, _⟩
    · exact Or.inl (Trans.trans hgle12 hgle23)
    · rw [← hgle_eq23]; exact Or.inl hgle12
  · rcases h23 with hgle23 | ⟨hgle_eq23, hcle23⟩
    · rw [hgle_eq12]; exact Or.inl hgle23
    · exact Or.inr ⟨hgle_eq12.trans hgle_eq23, Trans.trans hcle12 hcle23⟩

/-! ## Witness canonicalization

Since `globalLinearizationEventOfRequest` is `Prop`, any two witnesses for the same event
are propositionally equal. This lets us freely substitute between witnesses carried in
edge structures and canonical witnesses from `wrapper`. -/

/-- Any two linearization witnesses for the same event give the same GLE. -/
theorem gle_canonical
    (h₁ h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : gle h₁ = gle h₂ := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this; rfl

/-- Any two linearization witnesses for the same event give the same CLE. -/
theorem cle_canonical
    (h₁ h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : cle h₁ = cle h₂ := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this; rfl

/-- Hierarchical ordering is invariant under witness substitution. -/
theorem hierarchicallyOrdered_subst
    {ha₁ hb₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {ha₂ hb₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : hierarchicallyOrdered ha₁ ha₂)
    : hierarchicallyOrdered hb₁ hb₂ := by
  have heq₁ : ha₁ = hb₁ := Subsingleton.elim ha₁ hb₁
  have heq₂ : ha₂ = hb₂ := Subsingleton.elim ha₂ hb₂
  subst heq₁; subst heq₂; exact h

/-! ## Each `com` edge preserves hierarchical order (canonical witnesses) -/

/-- rfe edges imply hierarchical ordering.
    From `readsFrom.cases`: wObRGle gives GLE ordering, wEqRGle gives same GLE + CLE ordering. -/
theorem rfe_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.rfe n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w_lin h.r_lin := by
  unfold hierarchicallyOrdered gleOrderedBefore
  cases h.readsFrom with
  | wEqRGle _ hwr_same_cluster _ =>
    -- rfe requires diffProtocol (e₁.protocol ≠ e₂.protocol)
    -- but wEqRGle requires same cluster (e₁.protocol = e₂.protocol) — contradiction
    exact absurd hwr_same_cluster h.diffProtocol
  | wObRGle hw_r_gle_ob _ =>
    -- GLE(w).OrderedBefore GLE(r) → gleOrderedBefore → hierarchicallyOrdered
    exact Or.inl hw_r_gle_ob

/-- co edges give hierarchical ordering (directly by definition). -/
theorem co_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.co n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w₁_lin h.w₂_lin :=
  h.ordering

/-- fr edges give hierarchical ordering (directly from the fr structure). -/
theorem fr_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.fr n compound b init e₁ e₂)
    : hierarchicallyOrdered h.e₁_lin h.e₂_lin :=
  h.ordering

/-- Link lemma: PPOi edges preserve the hierarchical order.

    The proof requires bridging from `CompoundLinearizationOrder` (ordering on compound
    linearization events) to `hierarchicallyOrdered` (ordering on GLE/CLE pairs).

    In the non-lazy case, `e_lin₁.OrderedBefore e_lin₂` implies GLE/CLE ordering.
    In the lazy case (nc.weak → c.release in orderAfterDir), the weaker `finishesBefore`
    still gives hierarchical ordering because the lazy case is restricted to single PPOi
    pairs and cannot accumulate. -/
theorem ppoi_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (hppoi : PPOi e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : hierarchicallyOrdered h₁_lin h₂_lin := by
  sorry

/-! ## Composing edges into the acyclicity proof -/

/-- Every single `com` step preserves hierarchical ordering (using canonical witnesses). -/
theorem com_step_hierarchicallyOrdered
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (hunion : (PPOi ∪ com compound b init) e₁ e₂)
    : hierarchicallyOrdered (hknow compound b init e₁) (hknow compound b init e₂) := by
  cases hunion with
  | inl h =>
    exact ppoi_hierarchicallyOrdered h _ _
  | inr hcom => cases hcom with
    | rfe h =>
      exact hierarchicallyOrdered_subst (rfe_hierarchicallyOrdered h)
    | co h =>
      exact hierarchicallyOrdered_subst (co_hierarchicallyOrdered h)
    | fr h =>
      exact hierarchicallyOrdered_subst (fr_hierarchicallyOrdered h)

/-- A `TransGen com` path from e₁ to e₂ gives hierarchical ordering between them. -/
theorem transGen_com_hierarchicallyOrdered
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (hpath : Relation.TransGen (PPOi ∪ com compound b init) e₁ e₂)
    : hierarchicallyOrdered (hknow compound b init e₁) (hknow compound b init e₂) := by
  induction hpath with
  | single hstep =>
    exact com_step_hierarchicallyOrdered hknow hstep
  | tail _ hstep ih =>
    exact hierarchicallyOrdered_trans ih (com_step_hierarchicallyOrdered hknow hstep)

/-! ## Main theorem -/

/-- The CMCM theorem: `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

    Assumes `wrapper`: every event has a `globalLinearizationEventOfRequest`.
    A cycle in `com` would give `hierarchicallyOrdered he he` (by transitivity),
    contradicting irreflexivity. -/
theorem cmcm_acyclic
    (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (PPOi ∪ com compound b init) := by
  intro e hcycle
  exact hierarchicallyOrdered_irrefl _
    (transGen_com_hierarchicallyOrdered hknow_dir_access hcycle)

instance : PartialOrder (Event n) := sorry

theorem cmcm (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) :
  Relation.Acyclic (PPOi ∪ com cmp b init) := by
  apply CMCM.suffices_inclusion
  · case hppo => sorry -- This should be the original main theorem
  · case hcom => sorry -- This should be the Rf stuff.

end Herd
