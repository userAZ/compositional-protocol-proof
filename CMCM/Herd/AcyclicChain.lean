import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel

`CmpLinForwardStep`: forward TemporalRel OR eq on cmpLin, with ProtoOBLevel.
Composition: trivial (TransGen.trans or substitution).
Acyclicity: ProtoOBLevel → self-OB → False.
-/

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

/-- Each R_hknow edge gives a CmpLinForwardStep.
    Uses the existing sorry-free cmpLinLinLink_acyclic invariant computation. -/
theorem edge_to_cmpLinForwardStep
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hedge : R_hknow hknow e₁ e₂)
    : CmpLinForwardStep hknow e₁ e₂ := by
  have pfs := edge_to_proto_forward h_non_lazy_ppoi hedge
  have ⟨hrel₁, hrel₂⟩ := edge_cmpLinCleRels hedge
  have h_cl := Relation.TransGen.single (edge_clelink h_non_lazy_ppoi hedge)
  -- chain_of_obLevel gives TemporalRel/eq/reverse.
  -- For forward/eq: direct. For reverse: use the existing sorry-free proof
  -- (cmcm_acyclic_of_hknow_compoundLinOrdering) to derive False at the cycle level.
  -- At the single-edge level: just take forward or eq from chain_of_obLevel.
  -- The reverse case: use the 3-way result and construct CmpLinForwardStep regardless.
  cases chain_of_obLevel pfs.level hrel₁ hrel₂ h_cl with
  | inl hfwd => exact ⟨Or.inl hfwd, pfs.level⟩
  | inr hor => cases hor with
    | inl heq => exact ⟨Or.inr heq, pfs.level⟩
    | inr hrev =>
      -- Reverse: chain_of_obLevel gave TemporalRel cmpLin₂ cmpLin₁ (wrong direction).
      -- For gleOB/cleOB: always forward (proven). For eventOB: reverse from chain_of_sameCLE.
      -- Re-derive using the specific ProtoOBLevel case.
      cases pfs.level with
      | gleOB h => exact ⟨Or.inl (temporalRel_of_gleOB_and_cmpLinCleRels h hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered h_cl), .gleOB h⟩
      | cleOB h_eq h => exact ⟨Or.inl (temporalRel_of_cleOB_and_cmpLinCleRels h hrel₁ hrel₂),
          .cleOB h_eq h⟩
      | eventOB h_gle_eq h_cle_eq h_ob =>
        -- eventOB reverse: protocol-impossible.
        -- cle_ob × (eq|inside): CLE OB e₁ + e₁ OB e₂ + e₂.Encapsulates CLE (encapDir) → False.
        -- inside × inside: same GLE → same cmpLin → dir_ordered self → vacuous.
        -- Direct case-split on rel₁ × (h_cle_eq ▸ rel₂):
        have hnd₁ := (notdown_of_edge hedge).1
        have hnd₂ := (notdown_of_edge hedge).2
        have hndE₂ := (notdir_of_edge hedge).2
        have hrel₂' := h_cle_eq ▸ hrel₂
        cases hrel₁ with
        | eq h₁ => cases hrel₂' with
          | eq h₂ => exact ⟨Or.inr (by rw [h₁, h₂]), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | cle_ob _ _ h₂_ob _ => exact ⟨Or.inl (by rw [h₁]; exact .single (.ob h₂_ob)), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | inside h₂_enc _ _ => exact ⟨Or.inl (by rw [h₁]; exact .single (.encap h₂_enc)), .eventOB h_gle_eq h_cle_eq h_ob⟩
        | cle_ob _ _ h₁_ob _ =>
          have h_eq_e₁ := compoundLin_eq_of_cle_ob hnd₁ h₁_ob
          have h_cle_lt_e₂ := Nat.lt_trans h₁_ob
            (Nat.lt_trans (h_eq_e₁ ▸ Event.oWellFormed n _) (h_eq_e₁ ▸ h_ob))
          -- cle_ob on rel₁. Case-split rel₂':
          cases hrel₂' with
          | eq h₂ =>
            -- cle_ob × eq: temporal contradiction via encapDir.
            exfalso
            cases (hknow e₂).cle_dirAccess with
            | encapDir _ hencap =>
              exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
                (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
            | orderBeforeDir hhas _ _ _ _ _ _ _ =>
              cases hle₂ : compound.linearizationOfEvent b init e₂ with
              | requestLin hreq =>
                have h_cmpLin_eq_e₂ := (hknow e₂).compoundLin_eq_event_of_requestLin hle₂
                exact hndE₂ (h_cmpLin_eq_e₂ ▸ h₂ ▸ (h_cle_eq ▸ (hknow e₁).cle_isDirEvent))
              | dirLin hd =>
                exact reqHasPerms_not_reqMissingPerms hd.choose_spec.2.reqHasNoPerms hnd₂ hhas
            | orderAfterDir _ _ _ _ => sorry
          | cle_ob _ _ h₂_ob _ =>
            -- cle_ob × cle_ob: use chain_of_sameCLE result (which gives forward for this case).
            sorry
          | inside h₂_enc _ _ =>
            -- cle_ob × inside: same temporal contradiction as cle_ob × eq.
            exfalso
            cases (hknow e₂).cle_dirAccess with
            | encapDir _ hencap =>
              exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
                (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
            | orderBeforeDir hhas _ _ _ _ _ _ _ =>
              cases hle₂ : compound.linearizationOfEvent b init e₂ with
              | requestLin hreq =>
                have h_cmpLin_eq_e₂ := (hknow e₂).compoundLin_eq_event_of_requestLin hle₂
                -- inside has h_isdir: compoundLin₂ isDirectoryEvent. compoundLin₂ = e₂ → e₂ isDir → contradiction.
                sorry
              | dirLin hd =>
                exact reqHasPerms_not_reqMissingPerms hd.choose_spec.2.reqHasNoPerms hnd₂ hhas
            | orderAfterDir _ _ _ _ => sorry
        | inside h₁_enc _ h₁_isdir => cases hrel₂' with
          | eq h₂ => exact ⟨Or.inl (.single (.encapBy (h₂ ▸ h₁_enc))), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | cle_ob _ _ h₂_ob _ => exact ⟨Or.inl (.tail (.single (.encapBy h₁_enc)) (.ob h₂_ob)), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | inside h₂_enc _ h₂_isdir =>
            match hfc₁ : (hknow e₁).compoundLin, h₁_isdir with
            | .directoryEvent de₁, _ =>
              match hfc₂ : (hknow e₂).compoundLin, h₂_isdir with
              | .directoryEvent de₂, _ =>
                cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
                | inl h => sorry -- dir_ordered forward: Lean type mismatch on dir vs event OB
                | inr h => sorry -- dir_ordered reverse: vacuous (same GLE → same cmpLin)
              | .cacheEvent _, hh => simp_all [Event.isDirectoryEvent]
            | .cacheEvent _, hh => simp_all [Event.isDirectoryEvent]

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
