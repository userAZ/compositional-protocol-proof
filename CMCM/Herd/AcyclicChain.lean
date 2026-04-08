import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel

`CmpLinForwardStep`: forward TemporalRel OR eq on cmpLin, with ProtoOBLevel.
Composition is trivial (TransGen.trans or substitution).
Acyclicity via ProtoOBLevel composition → self-OB → False.
-/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- A cmpLin step: forward TemporalRel or eq, with ProtoOBLevel. -/
structure CmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n) : Prop where
  chain : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
          (hknow e₁).compoundLin = (hknow e₂).compoundLin
  level : ProtoOBLevel hknow e₁ e₂

/-- Trivial composition. -/
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

/-- Irreflexivity. -/
theorem CmpLinForwardStep.irrefl
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e : Event n} (h : CmpLinForwardStep hknow e e) : False :=
  proto_ob_level_irrefl h.level

/-- Each edge gives a CmpLinForwardStep (forward or eq, never reverse). -/
theorem edge_to_cmpLinForwardStep
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hedge : R_hknow hknow e₁ e₂)
    : CmpLinForwardStep hknow e₁ e₂ := by
  -- Use the existing cmpLinLinLink_acyclic invariant computation.
  -- The main proof's invariant carries TemporalRel/eq/reverse from chain_of_obLevel.
  -- For forward/eq: direct. For reverse: the main proof carries it in the invariant
  -- (it doesn't need forward-only). But we need forward-only here.
  -- The reverse is protocol-impossible — derive from edge evidence.
  have pfs := edge_to_proto_forward h_non_lazy_ppoi hedge
  have ⟨hrel₁, hrel₂⟩ := edge_cmpLinCleRels hedge
  have h_cl := Relation.TransGen.single (edge_clelink h_non_lazy_ppoi hedge)
  -- chain_of_obLevel gives 3-way. Forward and eq are direct.
  -- Reverse: only from eventOB case of chain_of_sameCLE.
  -- Contradict reverse using eventOB evidence + CmpLinCleRel case analysis.
  cases chain_of_obLevel pfs.level hrel₁ hrel₂ h_cl with
  | inl hfwd => exact ⟨Or.inl hfwd, pfs.level⟩
  | inr hor => cases hor with
    | inl heq => exact ⟨Or.inr heq, pfs.level⟩
    | inr hrev =>
      -- Reverse only from eventOB + chain_of_sameCLE.
      -- gleOB/cleOB always give forward (from temporalRel_of_gleOB/cleOB).
      -- eventOB reverse cases:
      --   cle_ob × eq: CLE OB e₁ + e₁ OB e₂ + CLE encaps e₂ → CLE.oEnd < CLE.oEnd → False
      --   cle_ob × inside: same argument
      --   inside × inside: same GLE (same_cle→same_gle) → same cmpLin → dir_ordered self → False
      -- All contradictory. Use the forward-or-eq from the main proof's existing computation.
      -- The main proof's cmpLinLinLink_acyclic carries TemporalRel/eq/reverse in its invariant.
      -- Its acyclicity is already proven (zero sorry's). So R_hknow IS acyclic.
      -- Use: acyclicity of R_hknow → this specific edge can't be part of a cycle → derive forward.
      -- Actually simpler: just use exfalso from the protocol analysis.
      -- The TemporalRel reverse hrev carries vacuous evidence (self-OB from dir_ordered
      -- on identical directory events, which is uninhabitable).
      -- Show: hrev implies False because it carries BasicTemporalRel.ob with self-OB.
      -- For cle_ob × eq/inside: the OB chain gives CLE.oEnd < CLE.oEnd.
      -- For inside × inside: dir_ordered on same event gives de OB de → de.oEnd < de.oStart → False.
      -- In all cases: the TemporalRel was constructed from a False hypothesis.
      -- We can extract False from the ProtoOBLevel + CmpLinCleRel evidence directly.
      -- Since pfs.level is eventOB for this case:
      cases pfs.level with
      | gleOB h_gle_ob =>
        -- gleOB always gives forward in chain_of_obLevel. Reverse impossible.
        -- The chain_of_obLevel for gleOB calls temporalRel_of_gleOB which always returns forward.
        -- So this branch is unreachable.
        exact ⟨Or.inl (temporalRel_of_gleOB_and_cmpLinCleRels h_gle_ob hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered h_cl), .gleOB h_gle_ob⟩
      | cleOB h_gle_eq h_cle_ob =>
        -- cleOB always gives forward. Reverse impossible.
        exact ⟨Or.inl (temporalRel_of_cleOB_and_cmpLinCleRels h_cle_ob hrel₁ hrel₂),
               .cleOB h_gle_eq h_cle_ob⟩
      | eventOB h_gle_eq h_cle_eq h_ob =>
        -- eventOB + same CLE. chain_of_sameCLE returned reverse.
        -- Contradict: case-split on rel₁ and (h_cle_eq ▸ rel₂).
        exfalso
        have hrel₂' := h_cle_eq ▸ hrel₂
        -- The reverse-producing cases from chain_of_sameCLE:
        -- cle_ob × eq: CLE OB cmpLin₁ (= e₁). cmpLin₂ = CLE. e₁ OB e₂.
        --   eq means dirLin → encapDir → e₂.Encapsulates CLE.
        --   CLE.oEnd < e₁.oStart (CLE OB e₁). e₁.oEnd < e₂.oStart (e₁ OB e₂).
        --   CLE.oEnd < e₂.oStart. But e₂.Encapsulates CLE → CLE.oEnd < e₂.oEnd.
        --   Wait: encapDir gives e₂.Encapsulates CLE → e₂.oStart < CLE.oStart ∧ CLE.oEnd < e₂.oEnd.
        --   So e₂.oStart < CLE.oStart. But CLE.oEnd < e₁.oStart ≤ e₁.oEnd < e₂.oStart.
        --   e₂.oStart < CLE.oStart ≤ CLE.oEnd < e₂.oStart → e₂.oStart < e₂.oStart → False.
        -- cle_ob × inside: similar (inside also from encapDir → e₂.Encapsulates CLE).
        -- inside × inside: same GLE → cmpLin₁ = cmpLin₂ → dir_ordered self → False.
        -- Extract the CLE's dirAccessOfRequest for the encapDir evidence.
        -- For the CmpLinCleRel.eq case: cmpLin = CLE comes from dirLin which forces encapDir.
        -- encapDir gives e.Encapsulates CLE (from cacheEncapsulatesCorrespondingDirEvent.reqEncapDir).
        sorry

/-- Acyclicity via CmpLinForwardStep. -/
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
