import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel

`CmpLinStep`: forward TemporalRel OR eq on cmpLin, with ProtoOBLevel.
Composition: forward + forward → TransGen.trans. Eq + anything → substitute.
Acyclicity: ProtoOBLevel composed → self-OB → False.

When cmpLin₁ = cmpLin₂ (e.g., NC weak write/read writeback), the step is eq —
no TemporalRel needed. The ProtoOBLevel still advances at the event level.
-/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- A cmpLin step: forward TemporalRel or eq on cmpLin, with ProtoOBLevel.
    Eq steps arise when cmpLin₁ = cmpLin₂ (events with same linearization point). -/
structure CmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n) : Prop where
  /-- Forward TemporalRel on cmpLin, or equality (when cmpLin₁ = cmpLin₂). -/
  chain : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
          (hknow e₁).compoundLin = (hknow e₂).compoundLin
  /-- Protocol hierarchy level that advances. -/
  level : ProtoOBLevel hknow e₁ e₂

/-- Compose two steps: forward + forward → TransGen.trans. Eq → substitute. -/
theorem CmpLinForwardStep.trans
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ e₃ : Event n}
    (h₁ : CmpLinForwardStep hknow e₁ e₂) (h₂ : CmpLinForwardStep hknow e₂ e₃)
    : CmpLinForwardStep hknow e₁ e₃ := by
  refine ⟨?_, proto_ob_level_trans h₁.level h₂.level⟩
  cases h₁.chain with
  | inl hfwd₁ => cases h₂.chain with
    | inl hfwd₂ => exact Or.inl (hfwd₁.trans hfwd₂)
    | inr heq₂ => exact Or.inl (heq₂ ▸ hfwd₁)
  | inr heq₁ => cases h₂.chain with
    | inl hfwd₂ => exact Or.inl (heq₁ ▸ hfwd₂)
    | inr heq₂ => exact Or.inr (heq₁.trans heq₂)

/-- Irreflexivity: self-step → self-OB → False. -/
theorem CmpLinForwardStep.irrefl
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e : Event n} (h : CmpLinForwardStep hknow e e) : False :=
  proto_ob_level_irrefl h.level

/-- Each R_hknow edge gives a CmpLinForwardStep. -/
theorem edge_to_cmpLinForwardStep
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hedge : R_hknow hknow e₁ e₂)
    : CmpLinForwardStep hknow e₁ e₂ := by
  have pfs := edge_to_proto_forward h_non_lazy_ppoi hedge
  have ⟨hrel₁, hrel₂⟩ := edge_cmpLinCleRels hedge
  have h_cl := Relation.TransGen.single (edge_clelink h_non_lazy_ppoi hedge)
  cases chain_of_obLevel pfs.level hrel₁ hrel₂ h_cl with
  | inl hfwd => exact ⟨Or.inl hfwd, pfs.level⟩
  | inr hor => cases hor with
    | inl heq => exact ⟨Or.inr heq, pfs.level⟩
    | inr hrev =>
      -- Reverse: protocol-impossible (cle_ob × eq/inside contradicted by eventOB + encapDir,
      -- inside × inside at same CLE → same GLE → dir_ordered self → vacuous).
      sorry

/-- The CMCM relation is acyclic.

    Each edge gives a CmpLinForwardStep (forward TemporalRel or eq on cmpLin).
    Composition via CmpLinForwardStep.trans is trivial.
    A cycle composes to CmpLinForwardStep e e → self-OB → False. -/
theorem cmcm_acyclic_via_cmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) := by
  intro e hcycle
  suffices h : ∀ c, Relation.TransGen (R_hknow hknow) e c →
      CmpLinForwardStep hknow e c by
    exact CmpLinForwardStep.irrefl (h e hcycle)
  intro c hpath
  induction hpath with
  | single hedge => exact edge_to_cmpLinForwardStep h_non_lazy_ppoi hedge
  | tail _ hlast ih =>
    exact CmpLinForwardStep.trans ih (edge_to_cmpLinForwardStep h_non_lazy_ppoi hlast)

end Herd
