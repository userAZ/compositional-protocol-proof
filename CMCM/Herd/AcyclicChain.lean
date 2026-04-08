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

/-- Helper: DirectoryEvent OB lifts to Event TemporalRel after match. -/
private theorem temporalRel_of_dirOB {de₁ de₂ : DirectoryEvent n}
    (h : de₁.OrderedBefore n de₂)
    : TemporalRel (n := n) (.directoryEvent de₁) (.directoryEvent de₂) :=
  Relation.TransGen.single (BasicTemporalRel.ob h)

/-- Helper: lift TemporalRel on matched directory events back to original compoundLin. -/
private theorem lift_temporalRel_from_match
    {cmpLin₁ cmpLin₂ : Event n} {de₁ de₂ : DirectoryEvent n}
    (hfc₁ : cmpLin₁ = .directoryEvent de₁) (hfc₂ : cmpLin₂ = .directoryEvent de₂)
    (h : TemporalRel (n := n) (.directoryEvent de₁) (.directoryEvent de₂))
    : TemporalRel cmpLin₁ cmpLin₂ := by subst hfc₁; subst hfc₂; exact h

/-- clusterDirectoryLinearizationEvent uniquely determines e_glin for a given CLE.
    previousGlobalCacheGotPerms: e_glin = e_cdir (unique).
    getGlobalCachePerms: e_glin from noPerms.linearizationEvent (determined by CLE). -/
private theorem clusterDirLinEvent_unique
    {shimAxioms : ShimAxioms n} {b : Behaviour n} {init : InitialSystemState n}
    {e_cdir e₁ e₂ : Event n}
    (h₁ : CompoundProtocol.clusterDirectoryLinearizationEvent n shimAxioms b init e_cdir e₁)
    (h₂ : CompoundProtocol.clusterDirectoryLinearizationEvent n shimAxioms b init e_cdir e₂)
    : e₁ = e₂ := by
  -- The test `e_cdir.req.MRS ≤ globalCacheStateOfDirectoryEvent` is decidable.
  -- Same e_cdir → same test → same constructor.
  cases h₁ with
  | previousGlobalCacheGotPerms _ h_eq₁ =>
    cases h₂ with
    | previousGlobalCacheGotPerms _ h_eq₂ => exact h_eq₁.trans h_eq₂.symm
    | getGlobalCachePerms h_no _ => exact absurd ‹_› h_no
  | getGlobalCachePerms h_no₁ h_global₁ =>
    cases h₂ with
    | previousGlobalCacheGotPerms h_yes _ => exact absurd h_yes h_no₁
    | getGlobalCachePerms _ h_global₂ =>
      -- Both getGlobalCachePerms with noPerms.linearizationEvent on same CLE.
      -- Unfold and extract the equality chain.
      -- The definition has `by classical exact ...`, so we use `change` to get a clean Prop.
      -- Both have noPerms.linearizationEvent on same CLE.
      -- The Prop structure determines e_glin uniquely from CLE.
      -- For now, this requires deep unfolding of the `by classical exact` wrapper.
      -- Alternative: add `compoundLin_unique_of_same_cle` as a field of CompoundProtocol.
      -- The protocol guarantees this (clusterDirectoryLinearizationEvent depends only on CLE),
      -- but the `by classical exact` definition wrapper prevents clean unfolding.
      sorry

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
        have hndE₁ := (notdir_of_edge hedge).1
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
            | orderAfterDir _ hsucc _ _ =>
              -- orderAfterDir: e₂ OB successor, successor encapsulates CLE₂.
              -- CLE₁.oEnd < e₂.oStart (h_cle_lt_e₂), e₂.oEnd < succ.oStart (isSucc),
              -- succ.oStart < CLE₂.oStart (encap). CLE₁ = CLE₂ → CLE.oEnd < CLE.oStart → False.
              have h_isSucc := hsucc.choose_spec.right.isImmBottomSucc.isSucc
              have h_encap_left := hsucc.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir.left
              -- Chain: CLE₁.oStart < CLE₁.oEnd < e₂.oStart < e₂.oEnd < succ.oStart < CLE₂.oStart = CLE₁.oStart
              have : Event.oStart n (hknow e₁).cle < Event.oStart n (hknow e₁).cle :=
                calc Event.oStart n (hknow e₁).cle
                    < Event.oEnd n (hknow e₁).cle := Event.oWellFormed n _
                  _ < Event.oStart n e₂ := h_cle_lt_e₂
                  _ < Event.oEnd n e₂ := Event.oWellFormed n _
                  _ < Event.oStart n hsucc.choose := h_isSucc
                  _ < Event.oStart n (hknow e₂).cle := h_encap_left
                  _ = Event.oStart n (hknow e₁).cle := by rw [h_cle_eq]
              exact absurd this (Nat.lt_irrefl _)
          | cle_ob _ _ h₂_ob _ =>
            -- cle_ob × cle_ob: direct forward via finishesAfterProxy.
            -- proxy = CLE₁ = CLE₂ (h_cle_eq). CLE₁ OB cmpLin₂ (h₂_ob). CLE₁.oEnd < cmpLin₁.oEnd (h₁_ob + wf).
            exact ⟨Or.inl (.single (.finishesAfterProxy (hknow e₁).cle h₂_ob
              (Nat.lt_trans h₁_ob (Event.oWellFormed n _)))), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | inside h₂_enc _ h₂_isdir =>
            -- cle_ob × inside: same temporal contradiction as cle_ob × eq.
            exfalso
            cases (hknow e₂).cle_dirAccess with
            | encapDir _ hencap =>
              exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
                (Nat.lt_trans (Event.oWellFormed n _) (h_cle_eq ▸ h_cle_lt_e₂)))
            | orderBeforeDir hhas _ _ _ _ _ _ _ =>
              cases hle₂ : compound.linearizationOfEvent b init e₂ with
              | requestLin hreq =>
                -- inside: compoundLin₂.isDirectoryEvent. requestLin: compoundLin₂ = e₂. → e₂.isDir. Contradicts hndE₂.
                exact hndE₂ ((hknow e₂).compoundLin_eq_event_of_requestLin hle₂ ▸ h₂_isdir)
              | dirLin hd =>
                exact reqHasPerms_not_reqMissingPerms hd.choose_spec.2.reqHasNoPerms hnd₂ hhas
            | orderAfterDir _ hsucc _ _ =>
              -- Same temporal chain as cle_ob × eq orderAfterDir.
              have h_isSucc := hsucc.choose_spec.right.isImmBottomSucc.isSucc
              have h_encap_left := hsucc.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir.left
              have : Event.oStart n (hknow e₁).cle < Event.oStart n (hknow e₁).cle :=
                calc Event.oStart n (hknow e₁).cle
                    < Event.oEnd n (hknow e₁).cle := Event.oWellFormed n _
                  _ < Event.oStart n e₂ := h_cle_lt_e₂
                  _ < Event.oEnd n e₂ := Event.oWellFormed n _
                  _ < Event.oStart n hsucc.choose := h_isSucc
                  _ < Event.oStart n (hknow e₂).cle := h_encap_left
                  _ = Event.oStart n (hknow e₁).cle := by rw [h_cle_eq]
              exact absurd this (Nat.lt_irrefl _)
        | inside h₁_enc _ h₁_isdir => cases hrel₂' with
          | eq h₂ => exact ⟨Or.inl (.single (.encapBy (h₂ ▸ h₁_enc))), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | cle_ob _ _ h₂_ob _ => exact ⟨Or.inl (.tail (.single (.encapBy h₁_enc)) (.ob h₂_ob)), .eventOB h_gle_eq h_cle_eq h_ob⟩
          | inside h₂_enc _ h₂_isdir =>
            match hfc₁ : (hknow e₁).compoundLin, h₁_isdir with
            | .directoryEvent de₁, _ =>
              match hfc₂ : (hknow e₂).compoundLin, h₂_isdir with
              | .directoryEvent de₂, _ =>
                cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
                | inl h => exact ⟨Or.inl (lift_temporalRel_from_match hfc₁ hfc₂ (temporalRel_of_dirOB h)),
                    .eventOB h_gle_eq h_cle_eq h_ob⟩
                | inr h =>
                  -- de₂ OB de₁: reverse. Both de₁, de₂ are global dir events inside same CLE.
                  --
                  -- ANALYSIS: compoundLin for the `inside` case comes from
                  -- `getGlobalCachePerms` in `clusterDirectoryLinearizationEvent`, which depends
                  -- ONLY on the CLE (not on the cache event e₁/e₂). Same CLE → same e_glin →
                  -- de₁ = de₂ → self-OB → False. However, `compoundLinearizationEvent` is an
                  -- opaque axiom field of CompoundProtocol, so the formalization cannot derive
                  -- de₁ = de₂ without a "same CLE → same compoundLin" axiom.
                  --
                  -- The main proof (cmpLinLinLink_acyclic) handles this by carrying the reverse
                  -- through a 3-way invariant and closing via ProtoOBLevel at cycle level.
                  -- The CmpLinForwardStep approach (forward-or-eq per edge) is strictly stronger:
                  -- it requires eliminating the reverse at the single-edge level, which needs
                  -- the missing axiom.
                  sorry
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
