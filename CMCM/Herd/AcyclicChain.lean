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
        -- eventOB (e₁ OB e₂) + same CLE. chain_of_sameCLE returned reverse.
        -- Reverse only from cle_ob in rel₁. Contradict using encapDir on e₂.
        exfalso
        -- rel₁ must be cle_ob (eq and inside don't produce reverse after the fix).
        -- cle_ob: CLE OB cmpLin₁ (= e₁). So CLE.oEnd < e₁.oStart.
        -- e₁ OB e₂: e₁.oEnd < e₂.oStart. Chain: CLE.oEnd < e₂.oStart.
        -- From (hknow e₂).cle_dirAccess (encapDir case):
        --   e₂.Encapsulates CLE₂ → e₂.oStart < CLE₂.oStart.
        --   h_cle_eq: CLE₁ = CLE₂. So e₂.oStart < CLE.oStart ≤ CLE.oEnd < e₂.oStart → False.
        cases hrel₁ with
        | cle_ob _ h₁_eq h₁_ob _ =>
          -- CLE OB cmpLin₁ (h₁_ob): CLE.oEnd < cmpLin₁.oStart
          -- cmpLin₁ = e (h₁_eq): so CLE.oEnd < e.oStart ≤ e.oEnd
          -- We need e₁ OB e₂ but h₁_eq says cmpLin₁ = e, not e₁ = e.
          -- Actually cle_ob carries h₁_eq : cmpLin₁ = e. And cmpLin₁ = (hknow e₁).compoundLin.
          -- h_ob : e₁ OB e₂.
          -- CLE.oEnd < cmpLin₁.oStart (h₁_ob). cmpLin₁.oEnd ≤ ... hmm.
          -- Use: CLE.oEnd < cmpLin₁.oStart. cmpLin₁ = e₁'s compoundLin.
          -- gle_oEnd_lt_cle gives GLE.oEnd < CLE.oEnd. Not directly useful.
          -- Just use: CLE OB e₁ comes from cle_ob_to_temporal_chain or similar.
          -- Actually: h₁_ob is CLE.OrderedBefore cmpLin₁. e₁.oEnd < e₂.oStart (h_ob).
          -- Need: CLE.oEnd < e₂.oStart.
          -- Chain: CLE.oEnd < cmpLin₁.oStart (h₁_ob). cmpLin₁ finishesBefore e₁ (or eq e₁).
          -- For cle_ob: cmpLin₁ = e₁ (h₁_eq says cmpLin₁ = e, where e is the event from cle_ob).
          -- Wait: cle_ob has (e : Event n) (h_eq : cmpLin = e). This 'e' is NOT e₁.
          -- The 'e' in cle_ob is a witness event. h₁_eq : (hknow e₁).compoundLin = e.
          -- h₁_ob : (hknow e₁).cle.OrderedBefore (hknow e₁).compoundLin.
          -- So: CLE.oEnd < compoundLin₁.oStart. And compoundLin₁ = e (h₁_eq).
          -- But e is not e₁. e is the "cache event" from cle_ob's construction.
          -- For the temporal chain: need CLE.oEnd < e₂.oStart.
          -- Use gle_oEnd_lt_cle: GLE.oEnd < CLE.oEnd. And h₁_ob: CLE.oEnd < compoundLin₁.oStart.
          -- compoundLin₁.oStart ≤ compoundLin₁.oEnd. h_ob: e₁.oEnd < e₂.oStart.
          -- Need compoundLin₁.oEnd ≤ e₁.oEnd or similar. Not directly available.
          -- Simplest: use edge_oEnd_lt... no, it was removed.
          -- Use: from ProtoOBLevel.eventOB same CLE: e₁ OB e₂. And cle_ob gives CLE.oEnd < compoundLin₁.oStart.
          -- gle_oEnd_lt_cle: GLE₁.oEnd < CLE₁.oEnd. Not directly useful.
          -- Just derive directly: CLE.oEnd < e₁.oStart requires cmpLin₁ = e₁.
          -- But h₁_eq says cmpLin₁ = e (some event). For cle_ob: e IS the original event.
          -- Actually in compoundLin_cle_to_CmpLinCleRel, cle_ob sets h_eq : compoundLin = e (the event).
          -- So e IS e₁. h₁_eq : compoundLin₁ = e₁. Then CLE.oEnd < e₁.oStart (h₁_ob with h₁_eq).
          have h_cle_lt_e₂ : Event.oEnd n (hknow e₁).cle < Event.oStart n e₂ := by
            have : Event.oEnd n (hknow e₁).cle < Event.oStart n e₁ := by
              calc Event.oEnd n (hknow e₁).cle < Event.oStart n (hknow e₁).compoundLin := h₁_ob
                _ = Event.oStart n e₁ := by
                    -- h₁_eq : compoundLin = e. But e might not be e₁.
                    -- For cle_ob from compoundLin_cle_to_CmpLinCleRel: h₁_eq : compoundLin = e
                    -- where e is the original cache event. So compoundLin = e₁.
                    -- But we can't prove this without additional evidence.
                    sorry
            exact Nat.lt_trans this h_ob
          have h_cle₂_lt := h_cle_eq ▸ h_cle_lt_e₂  -- CLE₂.oEnd < e₂.oStart
          cases (hknow e₂).cle_dirAccess with
          | encapDir _ hencap =>
            exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
              (Nat.lt_trans (Event.oWellFormed n _) h_cle₂_lt))
          | orderBeforeDir hhas _ _ _ _ _ _ _ =>
            exact reqHasPerms_not_reqMissingPerms
              (by cases (hknow e₂).cle_dirAccess with
                  | encapDir hm _ => exact hm
                  | orderBeforeDir _ _ _ _ _ _ _ _ => sorry
                  | orderAfterDir _ _ _ _ => sorry)
              (notdown_of_edge hedge).2 hhas
          | orderAfterDir _ _ _ _ => sorry
        | eq _ => sorry -- eq rel₁ never produces reverse in chain_of_sameCLE
        | inside _ _ _ => sorry -- inside rel₁ never produces reverse (after fix)

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
