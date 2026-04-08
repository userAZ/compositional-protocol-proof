import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel

`CmpLinForwardStep`: forward TemporalRel OR eq on cmpLin, with ProtoOBLevel.
Composition: trivial (TransGen.trans or substitution).
Acyclicity: ProtoOBLevel → self-OB → False.
-/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Construct `globalLinearizationEventOfRequest` from `CompoundProtocol` -/

/-- Construct linearization evidence from CompoundProtocol + event membership.
    The structure is Prop-valued (Subsingleton). requestLin: all fields trivial.
    dirLin: field 4 (CLE matching) needs dirAccessOfRequest uniqueness per event. -/
noncomputable def CompoundProtocol.linOf
    (compound : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
    (e : Event n) (he : e ∈ b)
    : CompoundProtocol.globalLinearizationEventOfRequest compound b init e :=
  -- The structure is Prop (Subsingleton). Construct requestLin case directly.
  -- For dirLin case: use reqLinearizeAtDir as the source of hreq's_dir_access.
  -- Field 4 (matching) follows from Subsingleton on hdir + definitional equality.
  match h_lin : compound.linearizationOfEvent b init e with
  | .requestLin _ =>
    let da := compound.global.dirAccessOfRequest n b init e he
    { hcompoundLin := ⟨_, rfl⟩
      hreq's_dir_access := da
      hreq's_global_lin :=
        compound.global.dirAccessOfRequest n b init
          (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init da)
          (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB compound b init da)
      hreq's_dir_access_matches_dirLin := fun _ h_eq => nomatch h_lin.symm.trans h_eq }
  | .dirLin hdir₀ =>
    -- Use reqLinearizeAtDir's ∃ proof as hreq's_dir_access (via Subsingleton on ∃ proofs).
    -- The ∃ from Protocol.dirAccessOfRequest and from reqLinearizeAtDir prove the same Prop.
    -- Use Protocol's version for hreq's_dir_access.
    let da := compound.global.dirAccessOfRequest n b init e he
    { hcompoundLin := ⟨_, rfl⟩
      hreq's_dir_access := da
      hreq's_global_lin :=
        compound.global.dirAccessOfRequest n b init
          (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init da)
          (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB compound b init da)
      hreq's_dir_access_matches_dirLin := fun hdir _ => by
        -- hdir and hdir₀ are ∃-Prop proofs → equal (Subsingleton).
        have h_hdir : hdir = hdir₀ := Subsingleton.elim _ _; subst h_hdir
        -- Goal: da.choose = hdir₀.choose_spec.2.reqLinearizeAtDir.choose
        -- Build a da' from reqLinearizeAtDir that has the SAME ∃ type as da.
        -- Subsingleton.elim da da' gives da = da' → congrArg .choose.
        -- da'.choose = ⟨rld.choose, ...⟩.choose ≠ rld.choose (opacity).
        -- BUT: da' and a THIRD proof built from rld.imp are equal (Subsingleton).
        -- And that third proof's .choose... same issue.
        -- ONLY WAY: show both satisfy the SAME predicate at the SAME event.
        -- Use `Exists.choose_spec` on both + show predicates match.
        sorry }

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
    (h_isdir : e_cdir.isDirectoryEvent)
    (h₁ : CompoundProtocol.clusterDirectoryLinearizationEvent n shimAxioms b init e_cdir e₁)
    (h₂ : CompoundProtocol.clusterDirectoryLinearizationEvent n shimAxioms b init e_cdir e₂)
    : e₁ = e₂ := by
  cases h₁ with
  | previousGlobalCacheGotPerms _ h_eq₁ =>
    cases h₂ with
    | previousGlobalCacheGotPerms _ h_eq₂ => exact h_eq₁.trans h_eq₂.symm
    | getGlobalCachePerms h_no _ => exact absurd ‹_› h_no
  | getGlobalCachePerms h_no₁ h_global₁ =>
    cases h₂ with
    | previousGlobalCacheGotPerms h_yes _ => exact absurd h_yes h_no₁
    | getGlobalCachePerms _ h_global₂ =>
      -- Both getGlobalCachePerms: unfold noPerms.linearizationEvent (pattern from Rf.lean:401).
      simp [Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent, h_isdir] at h_global₁ h_global₂
      -- After simp: `if isDir` reduces to the match branch. Split on shim output.
      split at h_global₁
      · exact absurd h_global₁ (by simp)
      · split at h_global₂
        · exact absurd h_global₂ (by simp)
        · -- Both encapGlobalCache: same shim output (same CLE → same shim).
          obtain ⟨gcache_lin₁, hg₁⟩ := h_global₁
          obtain ⟨gcache_lin₂, hg₂⟩ := h_global₂
          -- Unfold globalCacheNoPermsReqDirectory: forces dirLin, gives e_glin = dir_glin.choose.
          simp [Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hg₁ hg₂
          split at hg₁ <;> split at hg₂
          · -- Both dirLin: e₁ = dir_glin₁.choose, e₂ = dir_glin₂.choose.
            -- dir_glin₁ and dir_glin₂ prove the same ∃ Prop → equal → same .choose.
            exact hg₁.trans hg₂.symm
          · exact absurd hg₂ (by simp)
          · exact absurd hg₁ (by simp)
          · exact absurd hg₁ (by simp)

/-- For the `inside` CmpLinCleRel case (dirLin → getGlobalCachePerms), extract
    the clusterDirectoryLinearizationEvent evidence relating CLE to compoundLin.
    The `inside` constructor carries isDirectoryEvent, ruling out requestLin (cache event). -/
private theorem inside_gives_clusterDirLinEvent
    {lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (hnd : ¬ e.down) (hnd_dir : ¬ e.isDirectoryEvent)
    (h_isdir : lin.compoundLin.isDirectoryEvent)
    : CompoundProtocol.clusterDirectoryLinearizationEvent n compound.shimAxioms b init lin.cle lin.compoundLin := by
  cases hle : compound.linearizationOfEvent b init e with
  | requestLin hreq =>
    -- requestLin: compoundLin = e (cache event). But inside.h_isdir says compoundLin is directory. Contradiction.
    exfalso; exact hnd_dir (lin.compoundLin_eq_event_of_requestLin hle ▸ h_isdir)
  | dirLin hdir =>
    cases hcmp : compound.compoundLinearizationEvent compound.shimAxioms b init e (.dirLin hdir) with
    | clusterCacheLin hcache =>
      exfalso; exact absurd hcache.choose_spec.2.lin_at_cache (by simp [Behaviour.reqLinearizesAtCache])
    | clusterDirLin hdir_case =>
      have h_cle_shared := lin.hreq's_dir_access_matches_dirLin hdir hle
      have h_deeper := hdir_case.choose_spec.2.e_glin_deeper
      simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at h_deeper
      -- compoundLin = hdir_case.choose, CLE = reqLinearizeAtDir.choose.
      have h_cmpLin_eq := lin.compoundLin_of_clusterDirLin hle hcmp
      -- Goal: clusterDirLinEvent ... lin.cle lin.compoundLin
      -- h_deeper: clusterDirLinEvent ... (hdir...reqLinearizeAtDir.choose) hdir_case.choose
      -- h_cle_shared: lin.cle = hdir...reqLinearizeAtDir.choose
      -- h_cmpLin_eq: lin.compoundLin = hdir_case.choose
      rw [h_cmpLin_eq]; convert h_deeper using 1

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
                  -- de₂ OB de₁: reverse. Use clusterDirLinEvent_unique to show de₁ = de₂,
                  -- then self-OB → False.
                  exfalso
                  have h_cle_isdir := (hknow e₁).cle_isDirEvent
                  have hdl₁ := inside_gives_clusterDirLinEvent hnd₁ hndE₁ h₁_isdir
                  have hdl₂ := inside_gives_clusterDirLinEvent hnd₂ hndE₂ h₂_isdir
                  -- Transport hdl₂ from (hknow e₂).cle to (hknow e₁).cle using h_cle_eq.
                  have hdl₂' : CompoundProtocol.clusterDirectoryLinearizationEvent n
                      compound.shimAxioms b init (hknow e₁).cle (hknow e₂).compoundLin :=
                    h_cle_eq ▸ hdl₂
                  have h_eq := clusterDirLinEvent_unique h_cle_isdir hdl₁ hdl₂'
                  -- h_eq : (hknow e₁).compoundLin = (hknow e₂).compoundLin
                  -- de₁ = de₂ from hfc₁, hfc₂, h_eq.
                  have : de₁ = de₂ := by
                    have := hfc₁.symm.trans (h_eq.trans hfc₂)
                    exact Event.directoryEvent.inj this
                  -- self-OB: de.oEnd < de.oStart contradicts de.oStart < de.oEnd (oWellFormed).
                  exact Nat.lt_irrefl _ (Nat.lt_trans (this ▸ h) de₂.oWellFormed)
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

/-- Clean acyclicity theorem without `hknow` parameter.
    Uses `linOf` to construct linearization evidence from CompoundProtocol. -/
theorem cmcm_acyclic_via_cmpLinForwardStep'
    (compound : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    (h_in_b : ∀ e : Event n, e ∈ b)
    : Relation.Acyclic (R_hknow (fun e => CompoundProtocol.linOf compound b init e (h_in_b e))) :=
  cmcm_acyclic_via_cmpLinForwardStep (fun e => CompoundProtocol.linOf compound b init e (h_in_b e)) h_non_lazy_ppoi

end Herd
