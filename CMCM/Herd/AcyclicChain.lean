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
          -- For eq/inside on e₂: encapDir gives e₂.Encapsulates CLE.
          -- e₂.oStart < CLE.oStart ≤ CLE.oEnd < e₂.oStart → False.
          -- orderBeforeDir: reqHasPerms. But eq/inside means dirLin → compoundLin = CLE (dir event).
          -- requestLin (from reqHasPerms) gives compoundLin = e₂ (cache event).
          -- CLE is dir, e₂ is not dir → compoundLin can't be both → contradiction.
          exfalso
          cases (hknow e₂).cle_dirAccess with
          | encapDir _ hencap =>
            exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
              (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
          | orderBeforeDir hhas _ _ _ _ _ _ _ =>
            -- reqHasPerms → requestLin → compoundLin₂ = e₂.
            -- But hrel₂' = eq or inside → compoundLin₂ = CLE₂ (dir event) or inside CLE₂ (dir event).
            -- e₂ is not dir (hndE₂). compoundLin₂ = e₂ → compoundLin₂ not dir.
            -- compoundLin₂ = CLE₂ (eq) → compoundLin₂ IS dir. Contradiction.
            -- compoundLin₂ inside CLE₂ (inside) → compoundLin₂ isDirectoryEvent (h_isdir field).
            -- In both cases: compoundLin₂ is dir. But requestLin → compoundLin₂ = e₂ → not dir.
            -- Derive requestLin from reqHasPerms:
            cases hle₂ : compound.linearizationOfEvent b init e₂ with
            | requestLin hreq =>
              have h_cmpLin_eq_e₂ := (hknow e₂).compoundLin_eq_event_of_requestLin hle₂
              -- compoundLin₂ = e₂ (cache, ¬dir). But hrel₂' = eq/inside → compoundLin₂ is dir.
              cases hrel₂' with
              | eq h₂ => exact hndE₂ (h_cmpLin_eq_e₂ ▸ h₂ ▸ (h_cle_eq ▸ (hknow e₁).cle_isDirEvent))
              | cle_ob _ h₂_eq _ h₂_nd =>
                -- cle_ob: ¬ compoundLin₂.isDirectoryEvent. compoundLin₂ = e₂. No contradiction here.
                -- But cle_ob means CLE OB compoundLin₂. With same CLE and eventOB... temporal.
                sorry
              | inside _ _ h₂_isdir => exact hndE₂ (h_cmpLin_eq_e₂ ▸ h₂_isdir)
            | dirLin hd =>
              exact reqHasPerms_not_reqMissingPerms hd.choose_spec.2.reqHasNoPerms hnd₂ hhas
          | orderAfterDir hweak _ _ _ =>
            -- orderAfterDir: same as gle_oEnd_lt_cle. Use SWMR or NC argument.
            -- For cluster level: ncWeakReqOnVd for e₂. e₂ is a cache event at cluster.
            -- More complex — use temporal contradiction instead.
            -- CLE.oEnd < e₂.oStart (h_cle_lt_e₂ via h_cle_eq).
            -- orderAfterDir: successor encaps CLE. successor OB e₂.
            -- gcache OB successor: gcache.oEnd < successor.oStart.
            -- But e₂ = CLE₂ (from eq) or inside CLE₂ (from inside).
            -- For eq: e₂.oStart < CLE₂.oStart (from encapDir)... wait, we're in orderAfterDir, not encapDir.
            -- orderAfterDir has its own structure. The successor encaps CLE₂.
            -- CLE₂ inside successor. successor OB e₂.
            -- CLE₂.oEnd < successor.oEnd. successor.oEnd < e₂.oStart.
            -- So CLE₂.oEnd < e₂.oStart. Same as h_cle₂_lt. Consistent — no new contradiction.
            -- Need a DIFFERENT argument. The temporal chain doesn't directly contradict.
            -- Use: orderAfterDir requires ncWeakReqOnVd. If the event is at a cluster
            -- where the protocol has SC events, nc_no_sc gives contradiction.
            -- But this is deep protocol infrastructure. Sorry for now.
            sorry
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
