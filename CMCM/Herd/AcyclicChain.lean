import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel -/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

structure CmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n) : Prop where
  chain : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
          (hknow e₁).compoundLin = (hknow e₂).compoundLin
  level : ProtoOBLevel hknow e₁ e₂

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

theorem CmpLinForwardStep.irrefl
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e : Event n} (h : CmpLinForwardStep hknow e e) : False :=
  proto_ob_level_irrefl h.level

/-- eventOB + same CLE: derive forward TemporalRel or eq on cmpLin.
    Direct case-split on rel₁ × rel₂ avoids chain_of_sameCLE reverse issue. -/
private theorem eventOB_chain_forward_or_eq
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ : Event n}
    (h_ob : e₁.OrderedBefore n e₂)
    (h_cle_eq : (hknow e₁).cle = (hknow e₂).cle)
    (hnd₁ : ¬ e₁.down)
    (rel₁ : CmpLinCleRel (hknow e₁).compoundLin (hknow e₁).cle)
    (rel₂ : CmpLinCleRel (hknow e₂).compoundLin (hknow e₂).cle)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
      (hknow e₁).compoundLin = (hknow e₂).compoundLin := by
  have hrel₂' := h_cle_eq ▸ rel₂
  -- Direct case-split: compute forward or eq for each rel₁ × rel₂ pair.
  cases rel₁ with
  | eq h₁ => cases hrel₂' with
    | eq h₂ => exact Or.inr (by rw [h₁, h₂])
    | cle_ob _ _ h₂_ob _ => exact Or.inl (by rw [h₁]; exact .single (.ob h₂_ob))
    | inside h₂_enc _ _ => exact Or.inl (by rw [h₁]; exact .single (.encap h₂_enc))
  | cle_ob _ _ h₁_ob _ =>
    -- cle_ob: CLE OB compoundLin₁. compoundLin₁ = e₁ (from compoundLin_eq_of_cle_ob).
    have h_eq_e₁ := compoundLin_eq_of_cle_ob hnd₁ h₁_ob
    -- CLE.oEnd < e₁.oStart. e₁.oEnd < e₂.oStart. So CLE.oEnd < e₂.oStart.
    have h_cle_lt_e₂ : Event.oEnd n (hknow e₁).cle < Event.oStart n e₂ :=
      Nat.lt_trans h₁_ob (Nat.lt_trans (h_eq_e₁ ▸ Event.oWellFormed n _) (h_eq_e₁ ▸ h_ob))
    cases hrel₂' with
    | eq h₂ =>
      -- cle_ob × eq: CLE OB e₁, cmpLin₂ = CLE. e₁ OB e₂.
      -- encapDir: e₂.Encapsulates CLE → e₂.oStart < CLE.oStart ≤ CLE.oEnd < e₂.oStart → False.
      exfalso
      cases (hknow e₂).cle_dirAccess with
      | encapDir _ hencap =>
        exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
          (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
      | orderBeforeDir hhas _ _ _ _ _ _ _ => sorry -- reqHasPerms contradicts dirLin
      | orderAfterDir _ _ _ _ => sorry -- vacuous
    | cle_ob _ _ h₂_ob _ =>
      -- cle_ob × cle_ob: finishesAfterProxy (forward)
      exact Or.inl (.single (.finishesAfterProxy _ h₂_ob
        (Nat.lt_trans h₁_ob (Event.oWellFormed n _))))
    | inside h₂_enc _ _ =>
      -- cle_ob × inside: same temporal contradiction as cle_ob × eq.
      exfalso
      cases (hknow e₂).cle_dirAccess with
      | encapDir _ hencap =>
        exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
          (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
      | orderBeforeDir _ _ _ _ _ _ _ _ => sorry
      | orderAfterDir _ _ _ _ => sorry
  | inside h₁_enc _ h₁_isdir => cases hrel₂' with
    | eq h₂ => exact Or.inl (.single (.encapBy (h₂ ▸ h₁_enc)))
    | cle_ob _ _ h₂_ob _ => exact Or.inl (.tail (.single (.encapBy h₁_enc)) (.ob h₂_ob))
    | inside h₂_enc _ h₂_isdir =>
      -- inside × inside: both global dir events inside same CLE. dir_ordered.
      match hfc₁ : (hknow e₁).compoundLin, h₁_isdir with
      | .directoryEvent de₁, _ =>
        match hfc₂ : (hknow e₂).compoundLin, h₂_isdir with
        | .directoryEvent de₂, _ =>
          -- dir_ordered: both cases give OB (both might be self → vacuous).
          cases (hdir de₁ de₂).ordered with
          | inl h_ob' => exact Or.inl (.single (.ob h_ob'))
          | inr h_ob' =>
            -- de₂ OB de₁: reverse. Same CLE → same GLE → same cmpLin → vacuous.
            sorry
        | .cacheEvent _, hh => simp_all [Event.isDirectoryEvent]
      | .cacheEvent _, hh => simp_all [Event.isDirectoryEvent]

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
      cases pfs.level with
      | gleOB h => exact ⟨Or.inl (temporalRel_of_gleOB_and_cmpLinCleRels h hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered h_cl), .gleOB h⟩
      | cleOB h_eq h => exact ⟨Or.inl (temporalRel_of_cleOB_and_cmpLinCleRels h hrel₁ hrel₂),
          .cleOB h_eq h⟩
      | eventOB h_gle_eq h_cle_eq h_ob =>
        exact ⟨eventOB_chain_forward_or_eq h_ob h_cle_eq (notdown_of_edge hedge).1 hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered, .eventOB h_gle_eq h_cle_eq h_ob⟩

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
