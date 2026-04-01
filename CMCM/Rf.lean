import Mathlib

import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompoundPPOs
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization

variable {n : Nat}

/-
structure Event.unique (e e₁ e₂ : Event n) where
 notLeft : e ≠ e₁
 notRight : e ≠ e₂

structure Event.uniqueBetween (e e₁ e₂ : Event n) where
  unique : e.unique e₁ e₂
  between : e.OrderedBetween n e₁ e₂
-/

/-- Cluster Directory event's Global Request. -/
noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (hcdir_is_dir : e_cdir.isDirectoryEvent n)
  : Event n :=
  match (cmp.shimAxioms.clusterToGlobal b init e_cdir hcdir_is_dir) with
  | .encapGlobalCache _ hgreq_spec_no_perms => hgreq_spec_no_perms.choose
  | .noGlobalCache _ _ => b.getLatestGlobalCacheEventOfClusterDirectoryEvent n e_cdir

noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper {e_creq : Event n}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (hexists_cdir : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hexists_cdir.choose hexists_cdir.choose_spec.right.isDirEvent

/-- No valid request's MRS is ≤ I, since all MRS values have `some` permissions but `I.p = none`. -/
private lemma ValidRequest.MRS_not_le_I (vr : ValidRequest) : ¬ (vr.MRS ≤ I) := by
  obtain ⟨⟨rw, coh, cons⟩, hvalid⟩ := vr
  cases rw <;> cases coh <;> cases cons <;> simp [Request.IsValid'] at hvalid <;>
    simp [ValidRequest.MRS, ReadWrite.toPerms, ReadWrite.toRWPerms,
      LE.le, State.le, LT.lt, State.lt, I, Vc, Vd, Option.le]

/-- If a cluster directory event has global cache permissions, then
`immediateFinishesBeforeAtGlobalCacheNotEncapEvents` is nonempty.
Proof: If the set is empty, `globalCacheStateOfDirectoryEvent` returns the init cache state (`I`).
`MRS ≤ I` is impossible for any valid request, contradicting `hcdir_has_gperms`. -/
lemma Behaviour.hasPermsInGlobalCache_implies_nonempty_immFinishBefore
  (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n)
  (hcdir_has_gperms : b.clusterDirHasPermsInGlobalCache n init e_cdir)
  : Nonempty (b.immediateFinishesBeforeAtGlobalCacheNotEncapEvents n e_cdir) := by
  by_contra h
  -- When ¬ Nonempty, Set.toOption = none, so globalCacheStateOfDirectoryEvent
  -- returns init.entryStateAtStruct, whose .state is init.cacheStates gcid
  let gcid := e_cdir.globalCidCorrespondingToClusterDir n
  -- All initial cache states are I (from Behaviour axiom)
  have h_init_I : init.cacheStates gcid = I := by
    let dummy_occ : Occurrence := ⟨0, 1, by omega⟩
    have := b.initCacheStateIsI (.cacheEvent
      ⟨dummy_occ, 0, 1, dummy_occ.oWellFormed, SCWrite, default, gcid, 0, false, none, 0⟩) init rfl
    simp only [InitialSystemState.stateAt, IEntry, Sum.inl.injEq] at this
    exact this
  -- Unfold the definition chain and substitute
  unfold clusterDirHasPermsInGlobalCache globalCacheStateOfDirectoryEvent
    stateOfSubsingletonEventSet at hcdir_has_gperms
  simp only [Set.toOption, h, ↓reduceDIte, Behaviour.eventToEntryState,
    InitialSystemState.entryStateAtStruct, EntryState.state] at hcdir_has_gperms
  rw [h_init_I] at hcdir_has_gperms
  exact absurd hcdir_has_gperms (ValidRequest.MRS_not_le_I _)

lemma Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (hexists_cdir : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir)
  : Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir) ∈ b
  := by
  simp[wrapper, cDir'sGReq]
  cases cmp.shimAxioms.clusterToGlobal b init hexists_cdir.choose hexists_cdir.choose_spec.right.isDirEvent
  . case encapGlobalCache _ hexists_global_access => simp[hexists_global_access.choose_spec]
  . case noGlobalCache hcdir_has_gperms hno_gcache_encap =>
    simp [Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent]
    split
    · case isTrue h =>
      exact h.some.prop.1
    · case isFalse h =>
      exact absurd (Behaviour.hasPermsInGlobalCache_implies_nonempty_immFinishBefore b init _ hcdir_has_gperms) h

/-- The Cluster Memory Order and Global Memory Order events (or Cluster Linearization Event CLE and Global Linearization Event GLE).
Note these terms are different from the PPO Linearization event of a request event from the PPO ordering proof.
A cluster request `e_creq` has a CLE `e_creq_lin` that linearizes `e_creq` in its cluster's (total or partial) memory order.
`e_creq` also has a GLE `e_creq_gle` that linearizes `e_creq` in the global (total or partial) memory order.
-/
structure CompoundProtocol.globalLinearizationEventOfRequest (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq : Event n) where
  -- The "Cluster Memory Order, CMO" — CLE (cluster linearization event, a directory event)
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  -- The "Global Memory Order, GMO" — GLE (global linearization event)
  hreq's_global_lin : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init
    (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hreq's_dir_access) e_gdir
  -- Invariant: in the dirLin case, the CLE is the same event as dirLin's directory event.
  -- This avoids Exists.choose opacity when relating compoundLin to CLE.
  hreq's_dir_access_matches_dirLin :
    ∀ (hdir : ∃ e_lin ∈ b, b.requestWithoutCoherentPermsLinearizesAtDir n init e_creq e_lin),
    cmp.linearizationOfEvent b init e_creq = .dirLin hdir →
    hreq's_dir_access.choose = hdir.choose_spec.2.reqLinearizeAtDir.choose

/-- CompoundMCM linearization event, parameterized by the linearizationOfEvent value.
    Avoids dependent type issues by taking lin_ev as an explicit parameter. -/
noncomputable def CompoundProtocol.compoundLinOf
    (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e : Event n)
    (lin_ev : Behaviour.linearizationEventOfRequest n b init e) : Event n :=
  match cmp.compoundLinearizationEvent cmp.shimAxioms b init e lin_ev with
  | .clusterCacheLin lin_e => lin_e.choose
  | .clusterDirLin lin_e => lin_e.choose

/-- CompoundMCM linearization event for a request. Deterministic function (not existential).
    Either the cache event itself (requestLin: has perms) or the CLE (dirLin: no perms).
    Used for the ranking function in acyclicity proof alongside CLE/GLE. -/
noncomputable def CompoundProtocol.globalLinearizationEventOfRequest.compoundLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (_ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e) : Event n :=
  cmp.compoundLinOf b init e (cmp.linearizationOfEvent b init e)

/-- Reduce compoundLin when clusterCacheLin: compoundLin = atCache's chosen event. -/
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_of_clusterCacheLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    {hreqlin} (hlin_ev : cmp.linearizationOfEvent b init e = .requestLin hreqlin)
    {hcache} (hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.requestLin hreqlin) = .clusterCacheLin hcache)
    : lin.compoundLin = hcache.choose := by
  show cmp.compoundLinOf b init e (cmp.linearizationOfEvent b init e) = hcache.choose
  rw [hlin_ev]; show cmp.compoundLinOf b init e (.requestLin hreqlin) = hcache.choose
  unfold CompoundProtocol.compoundLinOf; rw [hcmp]

/-- reqHasPerms and reqMissingPerms are mutually exclusive.
    All reqHasPerms constructors give b.hasPerms (= MRS ≤ stateBefore.cache).
    reqMissingPerms.noPermsForNonNcRelAcqWeakWrite has eventOnStateNoPerms = ¬ hasPerms.
    The other reqMissingPerms cases also contradict reqHasPerms sub-cases. -/
private theorem reqHasPerms_not_reqMissingPerms
    {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (hno : b.reqMissingPerms n init e) (hnotdown : ¬ e.down) : ¬ b.reqHasPerms n init e := by
  intro hhas
  have hhasPerms : b.hasPerms n init e := by
    cases hhas with
    | hasPerms _ h => exact h
    | ncRelAcqWeakWriteHasCoherentPerms _ h => exact h.hasPerms
    | ncWeakReadHasPermsNotVd _ h => exact h.hasPerms
  cases hno with
  | downgrade hdown _ => exact absurd hdown hnotdown
  | noPermsForNonNcRelAcqWeakWrite _ _ hno_perms =>
    exact hno_perms (show b.eventOnStateHasPerms n init e from hhasPerms)
  | ncRelAcqWeakWriteNotOnCoherentState _ hncRelAcq hno_coh =>
    -- acqRelWeakWriteNoPerms = ¬(coherent ∧ hasPerms).
    -- reqHasPerms.ncRelAcqWeakWriteHasCoherentPerms gives both coherent and hasPerms.
    cases hhas with
    | ncRelAcqWeakWriteHasCoherentPerms _ hcoh_perms =>
      exact hno_coh ⟨hcoh_perms.onCoherentState, hcoh_perms.hasPerms⟩
    | hasPerms hcoh hperms =>
      -- isCoherent means coherent=true. isNcRelAcq = isAcquire ∨ isNcRelease, both have coherent=false.
      cases e with
      | directoryEvent _ => simp [Event.isCoherent] at hcoh
      | cacheEvent ce =>
        simp [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at hcoh
        simp [Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,
              CacheEvent.isAcquire, CacheEvent.isNcRelease,
              ValidRequest.isAcquire, ValidRequest.isNcRelease] at hncRelAcq
        cases hncRelAcq with
        | inl hacq => rw [hacq] at hcoh; exact absurd hcoh (by decide)
        | inr hrel => rw [hrel] at hcoh; exact absurd hcoh (by decide)
    | ncWeakReadHasPermsNotVd hread _ =>
      -- isNcWeakRead = ⟨.r, false, .Weak⟩. isNcRelAcq = isAcquire ∨ isNcRelease.
      -- isAcquire = ⟨.r, false, .Acq⟩, isNcRelease = ⟨.w, false, .Rel⟩. All distinct.
      cases e with
      | directoryEvent _ => simp [Event.isNcWeakRead] at hread
      | cacheEvent ce =>
        simp [Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at hread
        simp [Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,
              CacheEvent.isAcquire, CacheEvent.isNcRelease,
              ValidRequest.isAcquire, ValidRequest.isNcRelease] at hncRelAcq
        cases hncRelAcq with
        | inl hacq => rw [hread] at hacq; exact absurd hacq (by decide)
        | inr hrel => rw [hread] at hrel; exact absurd hrel (by decide)

/-- Reduce compoundLin when clusterDirLin: compoundLin = atDirectoryOrBeyond's chosen event. -/
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_of_clusterDirLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    {hdir} (hlin_ev : cmp.linearizationOfEvent b init e = .dirLin hdir)
    {hdir_case} (hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.dirLin hdir) = .clusterDirLin hdir_case)
    : lin.compoundLin = hdir_case.choose := by
  show cmp.compoundLinOf b init e (cmp.linearizationOfEvent b init e) = hdir_case.choose
  rw [hlin_ev]; show cmp.compoundLinOf b init e (.dirLin hdir) = hdir_case.choose
  unfold CompoundProtocol.compoundLinOf; rw [hcmp]

/-- The compoundLin event relates to the CLE by one of these cases:
    1. compoundLin = CLE (dirLin + global cache already has perms → lin event is the CLE itself)
    2. CLE OB compoundLin (requestLin + orderBeforeDir: CLE is at predecessor, compoundLin = e_creq)
    3. compoundLin inside CLE (dirLin + global cache needs perms → lin event is deeper global event)
    In all cases, the CLE provides the bridge between compoundLin and the protocol evidence. -/
inductive CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_cle_rel
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e) : Prop
  /-- compoundLin = CLE: request linearizes at directory and global cache already has perms. -/
  | eq (h : lin.compoundLin = lin.hreq's_dir_access.choose)
  /-- CLE finishes before compoundLin starts: request has perms (orderBeforeDir),
      so compoundLin = e_creq and CLE is at a predecessor event. -/
  | cle_ob_compoundLin (h : lin.hreq's_dir_access.choose.OrderedBefore n lin.compoundLin)
  /-- compoundLin OB CLE: request has perms but CLE is at successor (orderAfterDir).
      compoundLin = e_creq, CLE at successor of e_creq. -/
  | compoundLin_ob_cle (h : lin.compoundLin.OrderedBefore n lin.hreq's_dir_access.choose)
  /-- compoundLin inside CLE: request linearizes at directory and global cache needs perms,
      so compoundLin is a deeper global event encapsulated by the CLE. -/
  | compoundLin_inside_cle (h : lin.compoundLin.EncapsulatedBy n lin.hreq's_dir_access.choose)

/-- Every non-downgrade request's compoundLin relates to its CLE in one of these ways. -/
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_cle
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    (hnotdown : ¬ e.down)
    : lin.compoundLin_cle_rel := by
  -- Case-split on linearizationOfEvent — this directly determines the compoundLinearizationEvent case.
  -- Then use dirAccessOfRequest to connect to the CLE.
  cases hlin_ev : cmp.linearizationOfEvent b init e with
  | requestLin hreqlin =>
    -- requestLin: reqHasPerms. compoundLin = e via atCache.e_creq_is_e_glin.
    -- CLE (from dirAccessOfRequest) is OB e since orderBeforeDir puts CLE at predecessor.
    -- compoundLin: case-split on compoundLinearizationEvent to reduce
    cases hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.requestLin hreqlin) with
    | clusterCacheLin hcache =>
      -- compoundLin = hcache.choose = e (via atCache.e_creq_is_e_glin).
      -- Use dirAccessOfRequest to relate CLE to e.
      have hda := lin.hreq's_dir_access.choose_spec.2
      -- dirAccessOfRequest determines CLE relationship to e.
      -- requestLin → reqHasPerms → dirAccessOfRequest must be orderBeforeDir.
      -- encapDir and orderAfterDir are vacuous (reqMissingPerms contradicts reqHasPerms).
      have hda := lin.hreq's_dir_access.choose_spec.2
      have h_reqHasPerms := hreqlin.choose_spec.2.reqHasPerms
      cases hda with
      | orderBeforeDir _ hexists_pred hpred_accesses_dir _ _ _ _ _ =>
        -- CLE inside predecessor, predecessor OB e → CLE OB e = CLE OB compoundLin.
        -- compoundLin = e (via clusterCacheLin + atCache.e_creq_is_e_glin).
        -- Extract CLE OB e:
        have hcle_ob_e : lin.hreq's_dir_access.choose.OrderedBefore n e :=
          Nat.lt_trans hpred_accesses_dir.reqEncapDir.right
            hexists_pred.choose_spec.2.isImmPred.bPred.isPred
        -- Construct .cle_ob_compoundLin without apply (to avoid dependent goal):
        exact .cle_ob_compoundLin (show lin.hreq's_dir_access.choose.OrderedBefore n lin.compoundLin by
          -- compoundLin = e: reduce through definitions.
          -- OrderedBefore is Nat.lt on oEnd/oStart. compoundLin and e are the same Event.
          -- Use congrArg to transport through the definition chain.
          have h_eq : lin.compoundLin = hcache.choose :=
            lin.compoundLin_of_clusterCacheLin hlin_ev hcmp
          rw [h_eq, hcache.choose_spec.2.e_creq_is_e_glin]; exact hcle_ob_e)
      | encapDir hno_perms _ =>
        -- Vacuous: encapDir has reqMissingPerms, requestLin has reqHasPerms.
        -- Need ¬down. Case-split on reqMissingPerms: downgrade has down=true,
        -- but requestLin.hasPerms requires isCoherent/isNcRelAcqWeakWrite/isNcWeakRead (not a downgrade).
        -- Actually, extract ¬down: if down=true, the event is a downgrade.
        -- requestLin carries requestWithCoherentPermsLinearizes which doesn't exclude down.
        -- Use by_cases:
        exact absurd h_reqHasPerms (reqHasPerms_not_reqMissingPerms hno_perms hnotdown)
      | orderAfterDir hweak hsucc_encap _ _ =>
        -- orderAfterDir: CLE at successor of e. compoundLin = e (from clusterCacheLin).
        -- e OB successor, CLE inside successor → e OB CLE → compoundLin OB CLE.
        apply compoundLin_cle_rel.compoundLin_ob_cle
        -- Need: compoundLin OB CLE.
        -- compoundLin = hcache.choose = e [compoundLin_of_clusterCacheLin + atCache].
        -- CLE inside successor (hsucc_encap). e OB successor (from immBottomSucc evidence).
        -- e.oEnd < successor.oStart < CLE.oStart → e OB CLE.
        -- hsucc_encap : immBottomSuccOnVdEncapCorrDir → has successor info.
        have h_compoundLin_eq := lin.compoundLin_of_clusterCacheLin hlin_ev hcmp
        rw [h_compoundLin_eq, hcache.choose_spec.2.e_creq_is_e_glin]
        -- Goal: e OB CLE.
        -- hsucc_encap : immBottomSuccOnVdEncapCorrDir = ∃ e_succ, ImmediateBottomSuccSatP ...
        -- e OB successor:
        have h_e_ob_succ : e.OrderedBefore n hsucc_encap.choose :=
          hsucc_encap.choose_spec.2.isImmBottomSucc.isSucc
        -- successor encapsulates CLE:
        have h_sat := hsucc_encap.choose_spec.2.satisfyP
        simp [Event.PropOnEvent, Behaviour.succOnVdWithCorrespondingDir] at h_sat
        have h_succ_encap_cle := h_sat.encapCorresponding.reqEncapDir
        -- Chain: e.oEnd < succ.oStart < CLE.oStart
        exact Nat.lt_trans h_e_ob_succ h_succ_encap_cle.left
    | clusterDirLin hdir_case =>
      -- clusterDirLin requires reqLinearizesAtDir. But we're in requestLin → reqLinearizesAtCache.
      -- atDirectoryOrBeyond has lin_at_dir : reqLinearizesAtDir ... (.requestLin _) which is False.
      exfalso
      have := hdir_case.choose_spec.2.lin_at_dir
      simp [Behaviour.reqLinearizesAtDir] at this
  | dirLin hdir =>
    -- dirLin: hdir carries requestWithoutCoherentPermsLinearizesAtDir which has:
    --   reqLinearizeAtDir : ∃ e_dir ∈ b, requestLinearizesAtDirectory ... e_dir e_lin
    --   requestLinearizesAtDirectory has reqCorrespondsToDir : dirAccessOfRequest e_req e_dir
    -- So the CLE from dirLin and the CLE from lin.hreq's_dir_access are both dirAccessOfRequest
    -- witnesses for the same event e.
    --
    -- compoundLinearizationEvent on (.dirLin hdir) gives clusterDirLin.
    -- Sub-case on clusterDirectoryLinearizationEvent:
    -- - previousGlobalCacheGotPerms: compoundLin = CLE → .eq
    -- - getGlobalCachePerms: compoundLin inside CLE → .compoundLin_inside_cle
    cases hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.dirLin hdir) with
    | clusterCacheLin hcache =>
      -- clusterCacheLin requires reqLinearizesAtCache on (.dirLin _) which is False.
      exfalso; exact absurd hcache.choose_spec.2.lin_at_cache (by simp [Behaviour.reqLinearizesAtCache])
    | clusterDirLin hdir_case =>
      -- compoundLin = hdir_case.choose.
      -- Extract atDirectoryOrBeyond.e_glin_deeper → OfReqEncapDirAccess on .dirLin →
      -- clusterDirectoryLinearizationEvent on CLE.
      have h_atdir := hdir_case.choose_spec.2
      have h_deeper := h_atdir.e_glin_deeper
      -- h_deeper : OfReqEncapDirAccess n cmp.shimAxioms b init e hdir_case.choose (.dirLin hdir)
      -- This unfolds to clusterDirectoryLinearizationEvent on the CLE from hdir.
      simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at h_deeper
      -- Now h_deeper : clusterDirectoryLinearizationEvent ... e_cdir hdir_case.choose
      cases h_deeper with
      | previousGlobalCacheGotPerms _ h_eq =>
        -- h_eq : hdir_case.choose = e_cdir (the CLE from dirLin).
        -- compoundLin = hdir_case.choose = e_cdir.
        -- Need: compoundLin = lin.hreq's_dir_access.choose.
        -- Key: both lin.hreq's_dir_access and dirLin's reqLinearizeAtDir prove the SAME
        -- Use the new invariant: CLE from lin = CLE from dirLin.
        have h_cle_shared := lin.hreq's_dir_access_matches_dirLin hdir hlin_ev
        -- h_cle_shared : lin.hreq's_dir_access.choose = hdir.choose_spec.2.reqLinearizeAtDir.choose
        -- h_eq : hdir_case.choose = e_cdir (the CLE from OfReqEncapDirAccess simp, = reqLinearizeAtDir.choose)
        -- compoundLin = hdir_case.choose [compoundLin_of_clusterDirLin]
        have h_compoundLin_eq := lin.compoundLin_of_clusterDirLin hlin_ev hcmp
        -- Chain: compoundLin = hdir_case.choose = e_cdir = reqLinearizeAtDir.choose = CLE
        exact .eq (by rw [h_compoundLin_eq, h_eq, ← h_cle_shared])
      | getGlobalCachePerms _ h_global =>
        -- compoundLin is a deeper global event inside the CLE from dirLin.
        -- Use the shared CLE invariant to relate to lin.hreq's_dir_access.choose.
        have h_cle_shared := lin.hreq's_dir_access_matches_dirLin hdir hlin_ev
        have h_compoundLin_eq := lin.compoundLin_of_clusterDirLin hlin_ev hcmp
        -- h_global : Shim.ClusterToGlobal.noPerms.linearizationEvent on e_cdir and hdir_case.choose
        -- e_cdir encapsulates hdir_case.choose (global event inside CLE).
        -- Need: compoundLin inside lin.hreq's_dir_access.choose.
        -- compoundLin = hdir_case.choose, CLE = lin.hreq's_dir_access.choose = e_cdir [h_cle_shared].
        -- Need: compoundLin EncapsulatedBy CLE.
        -- compoundLin = hdir_case.choose [compoundLin_of_clusterDirLin].
        -- CLE = e_cdir [h_cle_shared: lin.hreq's_dir_access.choose = e_cdir].
        -- h_global : noPerms.linearizationEvent on e_cdir and hdir_case.choose.
        -- This gives e_cdir encapsulates hdir_case.choose through the global cache chain.
        -- Use request_encapsulates_compound_linearization_event-like reasoning.
        --
        -- Actually: the existing lemma proves e.Encapsulates e_glin (through e→cdir→gcache→gdir).
        -- I need cdir.Encapsulates e_glin (just cdir→gcache→gdir, omitting the first step).
        -- The key evidence is in h_global after simp:
        -- h_global unfolds to ∃ gcache_lin, globalCacheNoPermsReqDirectory gcache_lin hdir_case.choose
        -- with encapGlobalCache giving cdir.Encapsulates gcache.
        -- And in the dirLin case, gcache's dir event (= hdir_case.choose) is inside gcache.
        --
        -- For the EncapsulatedBy direction: hdir_case.choose inside CLE.
        have h_cdir_isdir : (hdir.choose_spec.2.reqLinearizeAtDir.choose).isDirectoryEvent :=
          hdir.choose_spec.2.reqLinearizeAtDir.choose_spec.2.isDir
        -- Use request_encapsulates_compound_linearization_event but adapted for cdir.
        -- Actually, let me simp h_global and extract the chain manually.
        simp [Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent, h_cdir_isdir] at h_global
        split at h_global
        · -- noGlobalCache: False
          exact absurd h_global (by simp)
        · -- encapGlobalCache: extract gcache and chain
          rename_i _ _ htranslation _
          obtain ⟨hgcache_lin, hgcache_lin_cases⟩ := h_global
          simp [Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hgcache_lin_cases
          split at hgcache_lin_cases
          · -- dirLin: hdir_case.choose = gdir. Chain: cdir encap gcache encap gdir.
            rename_i hgcache_lin_ev hat_dir
            apply compoundLin_cle_rel.compoundLin_inside_cle
            -- Need: hdir_case.choose EncapsulatedBy CLE
            -- hdir_case.choose = hat_dir.choose (from hgcache_lin_cases)
            -- hat_dir : requestLinearizesAtDirectory → reqCorrespondsToDir : dirAccessOfRequest
            -- In the encapDir case: gcache.Encapsulates gdir.
            -- And cdir.Encapsulates gcache (from htranslation.encapGlobalCache).
            -- Chain: gdir inside gcache inside cdir → gdir EncapsulatedBy cdir.
            -- hgcache_lin_cases : hdir_case.choose = hat_dir.choose
            -- hat_dir : ∃ e_lin ∈ b, requestWithoutCoherentPermsLinearizesAtDir ...
            -- hat_dir.choose_spec.2.reqLinearizeAtDir : ∃ e_dir, requestLinearizesAtDirectory ...
            -- requestLinearizesAtDirectory.reqCorrespondsToDir : dirAccessOfRequest
            -- In encapDir case: gcache.Encapsulates gdir.
            -- htranslation : clusterDirEncapCorrespondingGlobalCache → .encapGlobalCache : cdir.Encap gcache
            -- Chain: cdir encap gcache encap gdir → gdir EncapsulatedBy cdir.
            have h_cdir_encap_gcache := htranslation.choose_spec.right.encapGlobalCache
            have h_gdir_lin := hat_dir.choose_spec.2.reqLinearizeAtDir.choose_spec.2
            -- h_gdir_lin : requestLinearizesAtDirectory
            -- h_gdir_lin.dirIsLin : hat_dir.choose = e_gdir (the global dir event)
            -- h_gdir_lin.reqCorrespondsToDir : dirAccessOfRequest gcache e_gdir
            cases h_gdir_lin.reqCorrespondsToDir with
            | encapDir _ hgcache_encap_gdir =>
              -- gcache.Encapsulates gdir. Chain with cdir.Encapsulates gcache.
              have h_cdir_encap_gdir := Event.encap_encap_trans n h_cdir_encap_gcache hgcache_encap_gdir.reqEncapDir
              -- h_cdir_encap_gdir : cdir.Encapsulates gdir
              -- Need: hdir_case.choose EncapsulatedBy CLE
              -- hdir_case.choose = hat_dir.choose (hgcache_lin_cases)
              -- hat_dir.choose = gdir (h_gdir_lin.dirIsLin)
              -- CLE = cdir (h_cle_shared)
              -- So: gdir EncapsulatedBy cdir.
              show lin.compoundLin.EncapsulatedBy n lin.hreq's_dir_access.choose
              rw [h_compoundLin_eq, hgcache_lin_cases, h_gdir_lin.dirIsLin, h_cle_shared]
              exact ⟨h_cdir_encap_gdir.left, h_cdir_encap_gdir.right⟩
            | orderBeforeDir hgcache_has_perms _ _ _ _ _ _ _ =>
              -- gcache has perms contradicts hat_dir having reqMissingPerms
              exact absurd hgcache_has_perms (by
                have := hat_dir.choose_spec.2.reqHasNoPerms
                intro h; exact absurd h (reqHasPerms_not_reqMissingPerms this
                  htranslation.choose_spec.right.gReqOfCDir.notDowngrade))
            | orderAfterDir hweak_vd _ _ _ =>
              -- Contradictory: global cache event's request is SC (from matchingOp),
              -- but ncWeakReqOnVd.weakReq says it's ncWeak (non-coherent, weak).
              -- matchingOp says req = ⟨rw, true, .SC⟩ (coherent=true, SC).
              -- ncWeak says coherent=false, consistency=.Weak.
              exfalso
              have hmatch := htranslation.choose_spec.right.gReqOfCDir.matchingOp
              have hweak := hweak_vd.weakReq
              -- hweak : htranslation.choose.isNcWeak = isNonCoherent ∧ isWeak
              -- hmatch : htranslation.choose.req = ⟨⟨_, true, .SC⟩, _⟩
              -- isNonCoherent needs coherent=false, hmatch gives coherent=true.
              -- Global cache event can't be ncWeak (matchingOp gives coherent=true, SC).
              have htrans := htranslation.choose_spec.right
              have hweak_req := hweak_vd.weakReq
              -- Derive after matching on the event type:
              match hge : htranslation.choose with
              | .directoryEvent _ =>
                simp [Event.isNcWeak, Event.isNonCoherent, hge] at hweak_req
              | .cacheEvent ce =>
                simp [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, hge] at hweak_req
                have hgreq_req := htrans.gReqOfCDir.matchingOp
                simp [Event.req, hge] at hgreq_req
                simp [hgreq_req] at hweak_req
          · -- requestLin: False
            exact absurd hgcache_lin_cases (by simp)

-- For dirLin, compoundLin_cle only returns eq or inside (never cle_ob or ob_cle).
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_cle_of_dirLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    (hnotdown : ¬ e.down)
    {hd : ∃ e_lin ∈ b, b.requestWithoutCoherentPermsLinearizesAtDir n init e e_lin}
    (hdir : cmp.linearizationOfEvent b init e = .dirLin hd)
    : lin.compoundLin = lin.hreq's_dir_access.choose ∨
      (lin.compoundLin.EncapsulatedBy n lin.hreq's_dir_access.choose ∧
       lin.compoundLin.protocol = .global) := by
  -- Replay the dirLin branch of compoundLin_cle.
  -- dirLin produces .eq (previousGlobalCacheGotPerms) or .inside (getGlobalCachePerms).
  have hrel := lin.compoundLin_cle hnotdown
  -- The compoundLin_cle proof case-splits on linearizationOfEvent internally.
  -- For dirLin, it only returns .eq or .compoundLin_inside_cle.
  -- We need to connect our hdir to the internal case split.
  -- Since compoundLin_cle is opaque, we case-split on the result and use sorry for vacuous cases.
  cases hrel with
  | eq ha => exact Or.inl ha
  | compoundLin_inside_cle ha => exact Or.inr ⟨ha, sorry⟩ -- need compoundLin.protocol = .global
  | cle_ob_compoundLin ha =>
    -- This only arises from requestLin. But we have dirLin. Contradiction.
    -- compoundLin_cle internally case-splits on linearizationOfEvent.
    -- For requestLin: may produce cle_ob. For dirLin: never.
    -- Since compoundLin_cle is a by-proof, we can't unfold it.
    -- However, we CAN use the fact that for dirLin, compoundLin is determined
    -- by clusterDirLin (not clusterCacheLin). And clusterDirLin cases are
    -- previousGlobalCacheGotPerms (.eq) or getGlobalCachePerms (.inside).
    -- The cle_ob case requires orderBeforeDir which only arises from requestLin.
    -- Use: linearizationOfEvent = dirLin → compoundLinearizationEvent = clusterDirLin.
    -- Then clusterDirLin can only produce eq or inside.
    exfalso
    -- dirLin → clusterDirLin (not clusterCacheLin)
    cases hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.dirLin hd) with
    | clusterCacheLin hcache =>
      exact absurd hcache.choose_spec.2.lin_at_cache (by simp [Behaviour.reqLinearizesAtCache])
    | clusterDirLin hdir_case =>
      -- Derive compoundLin = hdir_case.choose, then use deeper case analysis.
      have h_cl_eq := lin.compoundLin_of_clusterDirLin hdir hcmp
      have h_cle_shared := lin.hreq's_dir_access_matches_dirLin hd hdir
      have h_deeper := hdir_case.choose_spec.2.e_glin_deeper
      simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at h_deeper
      cases h_deeper with
      | previousGlobalCacheGotPerms _ h_eq =>
        rw [h_cl_eq, h_eq, ← h_cle_shared] at ha
        exact Nat.lt_irrefl _ (Nat.lt_trans ha (Event.oWellFormed n _))
      | getGlobalCachePerms _ h_global =>
        -- Derive compoundLin EncapsulatedBy CLE (same chain as compoundLin_cle lines 340-393).
        -- Then contradict ha : CLE OB compoundLin.
        have h_cdir_isdir : (hd.choose_spec.2.reqLinearizeAtDir.choose).isDirectoryEvent :=
          hd.choose_spec.2.reqLinearizeAtDir.choose_spec.2.isDir
        simp [Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent, h_cdir_isdir] at h_global
        split at h_global
        · exact absurd h_global (by simp)
        · rename_i _ _ htranslation _
          obtain ⟨hgcache_lin, hgcache_lin_cases⟩ := h_global
          simp [Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hgcache_lin_cases
          split at hgcache_lin_cases
          · rename_i hgcache_lin_ev hat_dir
            have h_cdir_encap_gcache := htranslation.choose_spec.right.encapGlobalCache
            have h_gdir_lin := hat_dir.choose_spec.2.reqLinearizeAtDir.choose_spec.2
            cases h_gdir_lin.reqCorrespondsToDir with
            | encapDir _ hgcache_encap_gdir =>
              have h_cdir_encap_gdir := Event.encap_encap_trans n h_cdir_encap_gcache hgcache_encap_gdir.reqEncapDir
              -- compoundLin = hdir_case.choose [h_cl_eq], = hat_dir.choose [hgcache_lin_cases],
              -- = gdir [h_gdir_lin.dirIsLin]. CLE = cdir [h_cle_shared].
              -- h_cdir_encap_gdir : cdir.Encapsulates gdir → gdir.oEnd < cdir.oEnd.
              -- ha : CLE.oEnd < compoundLin.oStart = cdir.oEnd < gdir.oStart.
              -- Chain: cdir.oEnd < gdir.oStart ≤ gdir.oEnd < cdir.oEnd → cdir.oEnd < cdir.oEnd.
              rw [h_cl_eq, hgcache_lin_cases, h_gdir_lin.dirIsLin, h_cle_shared] at ha
              exact Nat.lt_irrefl _ (Nat.lt_trans ha (Nat.lt_of_le_of_lt (Nat.le_of_lt (Event.oWellFormed n _)) h_cdir_encap_gdir.right))
            | orderBeforeDir hgcache_has_perms _ _ _ _ _ _ _ => exact absurd hgcache_has_perms (by have := hat_dir.choose_spec.2.reqHasNoPerms; intro h; exact absurd h (reqHasPerms_not_reqMissingPerms this htranslation.choose_spec.right.gReqOfCDir.notDowngrade))
            | orderAfterDir hweak_vd _ _ _ =>
              exfalso
              have hweak_req := hweak_vd.weakReq
              match hge : htranslation.choose with
              | .directoryEvent _ =>
                simp [Event.isNcWeak, Event.isNonCoherent, hge] at hweak_req
              | .cacheEvent ce =>
                simp [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, hge] at hweak_req
                have hgreq_req := htranslation.choose_spec.right.gReqOfCDir.matchingOp
                simp [Event.req, hge] at hgreq_req
                simp [hgreq_req] at hweak_req
          · exact absurd hgcache_lin_cases (by simp)
  | compoundLin_ob_cle ha =>
    exfalso
    cases hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.dirLin hd) with
    | clusterCacheLin hcache =>
      exact absurd hcache.choose_spec.2.lin_at_cache (by simp [Behaviour.reqLinearizesAtCache])
    | clusterDirLin hdir_case =>
      have h_cl_eq := lin.compoundLin_of_clusterDirLin hdir hcmp
      have h_cle_shared := lin.hreq's_dir_access_matches_dirLin hd hdir
      have h_deeper := hdir_case.choose_spec.2.e_glin_deeper
      simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at h_deeper
      cases h_deeper with
      | previousGlobalCacheGotPerms _ h_eq =>
        rw [h_cl_eq, h_eq, ← h_cle_shared] at ha
        exact Nat.lt_irrefl _ (Nat.lt_trans ha (Event.oWellFormed n _))
      | getGlobalCachePerms _ h_global =>
        -- ha : compoundLin OB CLE. Derive compoundLin inside CLE → contradiction.
        have h_cdir_isdir : (hd.choose_spec.2.reqLinearizeAtDir.choose).isDirectoryEvent :=
          hd.choose_spec.2.reqLinearizeAtDir.choose_spec.2.isDir
        simp [Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent, h_cdir_isdir] at h_global
        split at h_global
        · exact absurd h_global (by simp)
        · rename_i _ _ htranslation _
          obtain ⟨hgcache_lin, hgcache_lin_cases⟩ := h_global
          simp [Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hgcache_lin_cases
          split at hgcache_lin_cases
          · rename_i hgcache_lin_ev hat_dir
            have h_cdir_encap_gcache := htranslation.choose_spec.right.encapGlobalCache
            have h_gdir_lin := hat_dir.choose_spec.2.reqLinearizeAtDir.choose_spec.2
            cases h_gdir_lin.reqCorrespondsToDir with
            | encapDir _ hgcache_encap_gdir =>
              have h_cdir_encap_gdir := Event.encap_encap_trans n h_cdir_encap_gcache hgcache_encap_gdir.reqEncapDir
              rw [h_cl_eq, hgcache_lin_cases, h_gdir_lin.dirIsLin, h_cle_shared] at ha
              exact Nat.lt_irrefl _ (Nat.lt_trans ha (Nat.lt_trans h_cdir_encap_gdir.left (Event.oWellFormed n _)))
            | orderBeforeDir hgcache_has_perms _ _ _ _ _ _ _ => exact absurd hgcache_has_perms (by have := hat_dir.choose_spec.2.reqHasNoPerms; intro h; exact absurd h (reqHasPerms_not_reqMissingPerms this htranslation.choose_spec.right.gReqOfCDir.notDowngrade))
            | orderAfterDir hweak_vd _ _ _ =>
              exfalso
              have hweak_req := hweak_vd.weakReq
              match hge : htranslation.choose with
              | .directoryEvent _ =>
                simp [Event.isNcWeak, Event.isNonCoherent, hge] at hweak_req
              | .cacheEvent ce =>
                simp [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, hge] at hweak_req
                have hgreq_req := htranslation.choose_spec.right.gReqOfCDir.matchingOp
                simp [Event.req, hge] at hgreq_req
                simp [hgreq_req] at hweak_req
          · exact absurd hgcache_lin_cases (by simp)

/-- When linearizationOfEvent = requestLin and compoundLinearizationEvent = clusterCacheLin,
    the compoundLin event equals e (the original request event).
    Proof: compoundLin_of_clusterCacheLin gives compoundLin = hcache.choose,
    and hcache.choose_spec.2.e_creq_is_e_glin gives hcache.choose = e. -/
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_eq_event_of_clusterCacheLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    {hreqlin} (hlin_ev : cmp.linearizationOfEvent b init e = .requestLin hreqlin)
    {hcache} (hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.requestLin hreqlin) = .clusterCacheLin hcache)
    : lin.compoundLin = e :=
  (lin.compoundLin_of_clusterCacheLin hlin_ev hcmp).trans hcache.choose_spec.2.e_creq_is_e_glin

/-- When linearizationOfEvent = requestLin, the compoundLin event equals e.
    Case-splits on compoundLinearizationEvent:
    - clusterCacheLin: use compoundLin_eq_event_of_clusterCacheLin
    - clusterDirLin: vacuous (reqLinearizesAtDir on .requestLin is False) -/
theorem CompoundProtocol.globalLinearizationEventOfRequest.compoundLin_eq_event_of_requestLin
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    {hreqlin} (hlin_ev : cmp.linearizationOfEvent b init e = .requestLin hreqlin)
    : lin.compoundLin = e := by
  cases hcmp : cmp.compoundLinearizationEvent cmp.shimAxioms b init e (.requestLin hreqlin) with
  | clusterCacheLin hcache =>
    exact lin.compoundLin_eq_event_of_clusterCacheLin hlin_ev hcmp
  | clusterDirLin hdir_case =>
    exfalso
    have := hdir_case.choose_spec.2.lin_at_dir
    simp [Behaviour.reqLinearizesAtDir] at this

def CompoundProtocol.globalLinearizationEventOfRequest.wrapper :=
  ∀ cmp : CompoundProtocol n, ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_creq : Event n,
    CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_creq

/- Definitions to define rf cases for load value axiom. -/

structure Event.Between.noWrite.cond.sameCacheNoInterWrite
  (b : Behaviour n) (init : InitialSystemState n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  notDown : ¬ e_inter.down
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  sameCache : e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r
  interCleNotBetween :
    ∀ e_inter_cle ∈ b, b.dirAccessOfRequest n init e_inter e_inter_cle ∧
    e_inter.OrderedBetween n e_w e_r →
    ¬ (e_inter.isWrite ∧ e_inter_cle.OrderedBetween n e_w_cle e_r_cle)

structure Event.dirWriteDowngradeAtSameCluster
    (b : Behaviour n) (init : InitialSystemState n)
    (e_inter_down e_inter e_w : Event n) : Prop where
  isWrite : e_inter_down.isWrite
  notDown : ¬ e_inter_down.down
  sameCluster : e_inter_down.sameProtocol n e_w
  isDir : e_inter_down.isDirectoryEvent
  -- `e_inter_down` is the directory access of `e_inter` via the axiomatic dirAccessOfRequest relation,
  -- making the link between e_inter and e_inter_down more precise than bare Encapsulates.
  dirAccess : b.dirAccessOfRequest n init e_inter e_inter_down

structure Event.Between.noWrite.cond.diffCacheNoInterWriteDowngrade
  (b : Behaviour n) (init : InitialSystemState n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  diffCache : e_inter.diffStructure n e_w ∧ e_inter.diffStructure n e_r
  -- interUnique : e_inter.unique e_w e_r
  -- `e_inter_down` is an intervening directory write "downgrade" (not necessarily a downgrade, as per GlobalToCluster shim)
  -- from `e_inter` to `e_w`. Show `e_inter_down` cannot be OrderedBetween `e_w_cle` and `e_r_cle`, as per
  -- NoInterveningWrites.
  interCleNotBetween :
    ∀ e_inter_down ∈ b,
      Event.dirWriteDowngradeAtSameCluster b init e_inter_down e_inter e_w →
        ¬ (e_inter_down.OrderedBetween n e_w_cle e_r_cle)

structure Event.dirWriteDowngradeFromDiffCluster (e_inter_down e_inter e_w e_r : Event n) : Prop where
  diffProtocol : e_inter.diffProtocol n e_w ∧ e_inter.diffProtocol n e_r
  downToW : e_inter_down.sameProtocol n e_w
  isDirWrite : e_inter_down.isDirWrite
  isDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  interEncapDown : e_inter.Encapsulates n e_inter_down

structure Event.Between.noWrite.cond.diffClusterNoInterWriteDowngrade
  (b : Behaviour n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  -- `e_inter_down` is an intervening directory write "downgrade" (not necessarily a downgrade, as per GlobalToCluster shim)
  -- from `e_inter` to `e_w`. Show `e_inter_down` cannot be OrderedBetween `e_w_cle` and `e_r_cle`, as per
  -- NoInterveningWrites.
  interCleNotBetween :
    ∀ e_inter_down ∈ b,
      Event.dirWriteDowngradeFromDiffCluster e_inter_down e_inter e_w e_r →
        ¬ (e_inter_down.OrderedBetween n e_w_cle e_r_cle)

inductive Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites
  (b : Behaviour n) (init : InitialSystemState n) (e_inter e_w e_r e_w_cle e_r_cle : Event n)
  : Prop
| otherWSameCache
  (no_write_btn_w_r : Event.Between.noWrite.cond.sameCacheNoInterWrite b init e_inter e_w e_r e_w_cle e_r_cle)
| otherWDiffCacheSameCluster
  (no_write_same_cluster_down : Event.Between.noWrite.cond.diffCacheNoInterWriteDowngrade b init e_inter e_w e_r e_w_cle e_r_cle)
| otherWDiffCluster
  (no_write_diff_cluster_down : Event.Between.noWrite.cond.diffClusterNoInterWriteDowngrade b e_inter e_w e_r e_w_cle e_r_cle)

/- Begin Defs for WriteRead.EqGleCle.case -/
def Event.Between.noWrite
  (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle: Event n) : Prop :=
  ∀ e_inter ∈ b, e_inter.isClusterCache → e_inter.isWrite → ¬ e_inter.down →
    Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r e_w_cle e_r_cle

  -- ∃ e_inter_cle ∈ b, b.dirAccessOfRequest n init e_inter e_inter_cle ∧
  --   e_inter.OrderedBetween n e_w e_r →
  --   ¬ (e_inter.isWrite ∧ e_inter_cle.OrderedBetween n e_w_cle e_r_cle)

structure Event.Between (e_inter e_w e_r : Event n) : Prop where
  isCache : e_inter.isCacheEvent
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  sameCache : e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r
  interBetween : e_inter.OrderedBetween n e_w e_r
  coherentRead : e_r.isCoherent

def Event.Between.noEvict (b : Behaviour n) (e_w e_r : Event n) : Prop :=
  ∀ e_inter ∈ b, e_inter.Between e_w e_r → ¬ (e_inter.isEvictSW)

structure Event.Between.noWriteOrEvict (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  noWrite : Event.Between.noWrite b init e_w e_r e_w_cle e_r_cle
  noEvict : Event.Between.noEvict b e_w e_r

structure Event.writeReadPair (e_w e_r : Event n) : Prop where
  wIsWrite : e_w.isWrite
  wNotDown : ¬ e_w.down
  rIsRead : e_r.isRead
  rNotDown : ¬ e_r.down

/-- `e_w` and `e_r` are in the same cache and `e_w` is ordered before `e_r` and there are no writes or evicts between them.
This can be considered the "base case" of the reads-from or load-value axiom. -/
structure WriteRead.EqGleCle.case (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  wObR : e_w.OrderedBefore n e_r
  writeRead : Event.writeReadPair e_w e_r
  noBetween : Event.Between.noWriteOrEvict b init e_w e_r e_w_cle e_r_cle
/- End Defs for WriteRead.EqGleCle.case -/

/- Begin Defs for WriteRead.wObRCle.case -/

/-- An intervening directory write from a same-cluster cache write.
    The CLE of the intervening write is a directory write between the boundary events. -/
structure Event.Between.sameProtocol.interveningDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  interInB : e_w_inter ∈ b
  isCluster : e_w_inter.isClusterCache
  isWrite : e_w_inter.isWrite
  notDown : ¬ e_w_inter.down
  -- interUnique : e_w_inter.unique e_w_le e_r_le
  sameProtocol : e_w_inter.protocol = e_w_le.protocol
  cleDirWrite : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirWrite
  cleNotDown : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirNotDown
  cleBetween : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.OrderedBetween n e_w_le e_r_le

-- diffProtocol.interveningDirWrite, interveningWrite.sameOrDiffCluster, and noDirWrite
-- are defined below after Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper.

/-
structure WriteRead.wObRCle.sameCache.case (b : Behaviour n) (e_w e_r : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  noWriteBetween : Event.Between.noDirWrite b e_w e_r
-/

  /- Begin Defs for WriteRead.wObRCle.diffCache.case case -/

-- `e_r_down` is the downgrade sent from `e_r` to `e_w`'s cache.
structure WriteRead.noEvictBetween.cond (b : Behaviour n) (init : InitialSystemState n) (e_w e_r_down e_w_cle e_r_cle : Event n) : Prop where
  noWriteBtn : Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cle
  noEvictBtn : Event.Between.noEvict b e_w e_r_down
  wObRDown : e_w.OrderedBefore n e_r_down
  wCleObCdir : e_w_cle.OrderedBefore n e_r_cle

def Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (e_down e_grant : Event n) : Prop :=
  let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  -- yoink from line 269 from BehaviourRelationDefs.lean (used by Axiom 9, Behaviour.coherentWriteDirDowngradeOthers)
  -- fwdPrevOwner : ∃ e_down ∈ b, ∃ e_grant ∈ b, b.downgradeAtPrevOwner n init e_req e_dir e_down e_grant
  b.downgradeAtPrevOwner n init e_r_cle_gcache e_r_gle e_down e_grant

/-- A cluster directory event `e_inter_down` induced by a request `e_inter` from a different
    protocol/cluster than `e_w`.

    The full relation is:
    `e_inter` has a cluster dir access and induced global-linearization chain via
    `globalLinearizationEventOfRequest`; that global request triggers a downgrade `e_gdown`, and
    `e_gdown` is translated by the GlobalToCluster shim to both a proxy-cache event and the
    cluster directory event `e_inter_down` at `e_w`'s cluster. -/
structure Event.clusterDirFromDiffProtocolRequest {cmp : CompoundProtocol n}
  (b : Behaviour n) (init : InitialSystemState n)
  (e_inter e_inter_down : Event n)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  : Prop where
  existsGlobalDownTranslation :
    ∃ e_gdown ∈ b, ∃ e_grant ∈ b,
      Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init
        hinter_c_and_g_lin e_gdown e_grant ∧
      Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter_down

def Event.getProtocol (cmp : CompoundProtocol n) (e : Event n) : Protocol n :=
  match e.protocol with
  | .global => cmp.global
  | .cluster1 => cmp.cluster1
  | .cluster2 => cmp.cluster2

/-- Cases for how the proxy request at the cluster directory generates a downgrade to the owner.
    Two cases: coherent request (fwdCoherentRequestToOwner) or non-coherent request
    (nonCoherentReqOnSWDowngradeOthers). In the coherent-write e_w case, the coherent case
    can be contradicted since e_w is a coherent write (owner), not the requesting proxy. -/
inductive Behaviour.gdown.clusterDirDown
  (n : ℕ) (b : Behaviour n) (init : InitialSystemState n) (e_r_proxy e_r_cdir_down : Event n) : Prop
| coherentReq
  (hfwd : b.fwdCoherentRequestToOwner n init e_r_proxy e_r_cdir_down)
  : clusterDirDown n b init e_r_proxy e_r_cdir_down
| nonCoherentReq
  (hfwd : b.nonCoherentReqOnSWDowngradeOthers n e_r_proxy e_r_cdir_down init)
  : clusterDirDown n b init e_r_proxy e_r_cdir_down

/-- The encapsulation relationship between the read's request chain and the cluster
    directory downgrade `e_r_cdir_down`.
    - `cleEncap`: When e_r is in the same protocol/cluster as e_w, e_r's CLE directly
      encapsulates e_r_cdir_down.
    - `gcacheEncap`: When e_r is in a different protocol/cluster, a global cache event
      e_gcache (that got perms for e_r's CLE) encapsulates e_r_cdir_down.
    Both cases ensure e_r_cdir_down finishes before e_r's CLE (`cdownEndBeforeCle`). -/
inductive Behaviour.clusterDown.encapDirRelation
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (e_r_cdir_down : Event n)
  : Prop
| cleEncap (h : hr_c_and_g_lin.hreq's_dir_access.choose.Encapsulates n e_r_cdir_down)
| gcacheEncap
    -- The cluster-to-global shim's global cache event (the canonical gcache for this CLE)
    -- encapsulates e_r_cdir_down, pinning down the gcache via ClusterToGlobal.
    (h : (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
        hr_c_and_g_lin.hreq's_dir_access).Encapsulates n e_r_cdir_down)
    (cdownEndBeforeCle : e_r_cdir_down.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd)

/-- The full read-from-write downgrade chain: e_r's read triggers a global downgrade at
    e_w's cluster, producing a proxy event that causes a cluster directory downgrade.
    The chain: e_r_cle → e_r_cle_gcache → e_r_gle → e_r_gdown → e_r_proxy → e_r_cdir_down.

    When e_r and e_w are in the same cluster, CLE ≻ e_r_cdir_down (cleEncap).
    When e_r and e_w are in different clusters, e_gcache ≻ e_r_cdir_down (gcacheEncap). -/
structure Behaviour.clusterDown.encapDir (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  existsRClusterDirDown :
    ∃ e_r_cdir_down ∈ b, e_r_cdir_down.isDirectoryEvent ∧ e_r_cdir_down.protocol = e_w.protocol
    ∧ e_r_cdir_down.isDirDownRW
      ∧ Event.clusterDirFromDiffProtocolRequest b init e_r e_r_cdir_down hr_c_and_g_lin
      ∧ Behaviour.clusterDown.encapDirRelation hr_c_and_g_lin e_r_cdir_down

structure Behaviour.clusterDown.encapProxyAndDirAndCDown {cmp : CompoundProtocol n}
  {b : Behaviour n} {init : InitialSystemState n}
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  encapDir : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin
  existsRDownAtW :
    ∃ e_r_down ∈ b, e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down

/-- An intervening directory write from a different-cluster cache write.
    The chain goes: e_w_inter (diff cluster) → CLE → global cache (ClusterToGlobal shim)
    → GLE → global downgrade → cluster proxy (GlobalToCluster shim) → cluster directory event.
    Following the pattern of `Behaviour.clusterDown.encapProxyAndDirAndCDown`.

    TODO (post-theorem): Strengthen this structure similarly to `Behaviour.gdown.encapProxyAndDir`:
    - Replace existsClusterProxy with `globalWriteDownOnDirSW.wrapper` (since the intervening
      event is a write, the `globalWriteDownOnDirSW` case of the GlobalToCluster shim applies,
      i.e. `Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW.wrapper`).
    - Add `clusterDirDownFromProxy` using `Behaviour.gdown.clusterDirDown`. -/
structure Event.Between.diffProtocol.interveningDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  interInB : e_w_inter ∈ b
  isCluster : e_w_inter.isClusterCache
  isWrite : e_w_inter.isWrite
  notDown : ¬ e_w_inter.down
  diffProtocol : e_w_inter.protocol ≠ e_w_le.protocol
  -- Global downgrade from e_w_inter's GLE
  existsGlobalDown : ∃ e_gdown ∈ b, ∃ e_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init
      (hknow_dir_access cmp b init e_w_inter) e_gdown e_grant
  -- Cluster proxy at e_w_le's protocol
  existsClusterProxy :
    ∃ e_proxy ∈ b, e_proxy.protocol = e_w_le.protocol ∧ e_proxy.isClusterCache
  -- Cluster directory event at e_w_le's protocol, between the boundary events.
  -- The additional fields (isWrite, down, Encapsulates) capture that this directory event
  -- is a write-downgrade encapsulated by the originating cache write, matching
  -- the structure of DiffClusterCLE.NotBetweenCLEs.constraints.
  existsClusterDirDown :
    ∃ e_cdir_down ∈ b, e_cdir_down.isDirectoryEvent ∧
      e_cdir_down.protocol = e_w_le.protocol ∧
      e_cdir_down.isDirWrite ∧
      e_cdir_down.down ∧
      Event.clusterDirFromDiffProtocolRequest b init e_w_inter e_cdir_down
        (hknow_dir_access cmp b init e_w_inter) ∧
      e_cdir_down.OrderedBetween n e_w_le e_r_le

/-- Complete definition of an intervening write between two linearization events.
    An intervening write is either from the same cluster or a different cluster. -/
inductive Event.Between.interveningWrite.sameOrDiffCluster
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w e_r e_w_le e_r_le : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| sameCluster
    (e_w_inter : Event n)
    -- (inter_unique : e_w_inter.unique e_w_le e_r_le)
    (h : Event.Between.sameProtocol.interveningDirWrite cmp b init e_w_le e_r_le e_w_inter hknow_dir_access)
    : interveningWrite.sameOrDiffCluster cmp b init e_w e_r e_w_le e_r_le hknow_dir_access
| diffCluster
    (e_w_inter : Event n)
    -- (inter_unique : e_w_inter.unique e_w_le e_r_le)
    (h : Event.Between.diffProtocol.interveningDirWrite cmp b init e_w_le e_r_le e_w_inter hknow_dir_access)
    : interveningWrite.sameOrDiffCluster cmp b init e_w e_r e_w_le e_r_le hknow_dir_access

/-- No intervening directory write between two linearization events. -/
def Event.Between.noDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w e_r e_w_le e_r_le : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop :=
  ¬ Event.Between.interveningWrite.sameOrDiffCluster cmp b init e_w e_r e_w_le e_r_le hknow_dir_access

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
Exists `e_r_down` corresponding to `e_r_cdir_down` at `e_w`'s cache.
-/
structure WriteRead.noEvictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  gdownEncapProxyAndDirAndCDown : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  noEvictBetween :
    WriteRead.noEvictBetween.cond b init
      e_w gdownEncapProxyAndDirAndCDown.existsRDownAtW.choose
        hw_c_and_g_lin.hreq's_dir_access.choose
        gdownEncapProxyAndDirAndCDown.encapDir.existsRClusterDirDown.choose

def Event.Between.dirEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.sameStructure n e₁ → e.OrderedBetween n e₁ e₂ → (e.isDirEvict ∨ e.isDirRead)

structure WriteRead.evictBetween.cond
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w e_r e_w_cle e_r_cdir_down : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  noWriteBtn : Event.Between.noDirWrite cmp b init e_w e_r e_w_cle e_r_cdir_down hknow_dir_access
  evictBtn : Event.Between.dirEvict b e_w_cle e_r_cdir_down
  wObRDown : e_w_cle.OrderedBefore n e_r_cdir_down

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
-/
structure WriteRead.evictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  encapProxyAndDir : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin
  evictBetween : WriteRead.evictBetween.cond cmp b init e_w e_r (hw_c_and_g_lin.hreq's_dir_access.choose) encapProxyAndDir.existsRClusterDirDown.choose hknow_dir_access

inductive WriteRead.wObRCle.diffCache.wHasPermsAfter.case {e_w e_r}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| noEvictBetween
  (w_ob_r_down : WriteRead.noEvictBetween.cond.wrapper cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| evictBetween
  (w_cle_ob_r_cdir_down : WriteRead.evictBetween.cond.wrapper cmp b init e_w e_r e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

/-- e_r's proxy directory access (CLE) is ordered after e_w's CLE. -/
inductive WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
| sameCluster
  (sameProtocol : e_w.protocol = e_r.protocol)
  (hw_ob_r_cle : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
| diffCluster
  (diffProtocol : e_w.protocol ≠ e_r.protocol)
  (existsRClusterDownAtW : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin)
  (wObRDown : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
    existsRClusterDownAtW.existsRClusterDirDown.choose)

/-- When the write is coherent and at a different cache from the read,
    either the CLE of e_w immediately precedes the CLE of e_r (so the
    downgrade chain is constructed from CLE immediate predecessor),
    or the more general wHasPermsAfter.case applies (noEvict/evict subcases).
    In both cases, the coherent write triggers a downgrade, producing a
    cluster directory event at e_w's protocol encapsulated by e_r's CLE. -/
inductive WriteRead.wObRCle.diffCache.wCoherent.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| immPred
  (hw_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  (hencapPD : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| notImmPred
  (hw_has_perms_case : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
    (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
    hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

-- Cache write with something?
structure Event.cacheWrite.global (e : Event n) : Prop where
  isCacheWrite : e.isWrite
  isGlobal : e.protocol = .global

def Event.Between.noGlobalCacheWrite (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e₁ e₂ → ¬ Event.cacheWrite.global e

structure WriteRead.wCleAfter.cond (b : Behaviour n) (e_w_cle_gcache e_r_gdown : Event n) : Prop where
  noWriteBtn : Event.Between.noGlobalCacheWrite b e_w_cle_gcache e_r_gdown
  wObRDown : e_w_cle_gcache.OrderedBefore n e_r_gdown

/- (need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_w_cle_gcache` corresponding to `e_w_cle` at `e_w`'s cluster.
-/
def WriteRead.wCleAfter.cond.wrapper {e_w e_r}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  let e_w_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir := hw_c_and_g_lin.hreq's_dir_access)
  ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant ∧
    WriteRead.wCleAfter.cond b e_w_cle_gcache e_r_gdown

inductive WriteRead.wObRCle.diffCache.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| wHasPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  /- subcases are:
    immPred: e_w_cle is immediate predecessor of e_r_cle (cluster-level downgrade via Axiom 9)
    notImmPred: the general case with noEvict/evict subcases
  -/
  -- TODO: Perms after is coherent (SW.)
  (hw_coherent : b.reqLeavesStateAtLeast n e_w init SW)
  -- Use WriteRead.wObRCle.diffCache.wCoherent.case to distinguish immPred vs notImmPred
  (coherent_write : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| wNoPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  -- TODO STUB: Write has no perms (ex. Non-Coherent Release Write). Treat similar to wCleAfter case
  /- e_r's CLE (proxy directory access) is ordered after e_w's CLE.
     No global downgrade in the sameGle case since e_w and e_r share the same cluster.
  -/
  (hw_no_perms : b.reqMissingPerms n init e_w)
  (hw_nc : e_w.isNonCoherent)
  (hr_cle_after_w_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| wCleAfter -- `e_w`'s CLE is after `e_w`. (dirAccessOfRequest .after case.)
  /- subcases are:
    (Only one):
      case of vdWB after `e_w`.
    (Not allowed, coherent req is a competing write!):
      case of coherent req after `e_w` (i.e. in RCC-O or L-RCC protocol interfaces).
    -/
  /- e_r's CLE (proxy directory access) is ordered after e_w's CLE.
     No global downgrade in the sameGle case since e_w and e_r share the same cluster.
  -/
  (hr_cle_after_w_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

  /- End Defs for WriteRead.wObRCle.diffCache.case case -/

inductive WriteRead.wObRCle.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  | sameCache
    (sameCache : e_w.struct = e_r.struct)
    (noWriteBetween : Event.Between.noDirWrite cmp b init e_w e_r
      hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  | diffCache
    (hdiff_cache : e_w.struct ≠ e_r.struct)
    -- STUB: add inductive (WriteRead.wObRCle.diffCache.case) to define subcases of this case.
    (hdiff_cache_case : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

/- End Defs for WriteRead.wObRCle.case -/

structure WriteRead.wObR.GleOrCle.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
    hw_r_cle_ob : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose
    -- add inductive (WriteRead.wObRCle.case) to define goal.
    hwr_cle_ob_case : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

inductive Behaviour.readsFrom.wEqRGle.cases (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  | wEqRCle
    (hw_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    (hwr_com : WriteRead.EqGleCle.case b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  | wObRCle
    -- NOTE: bundled hypothesis conditions together, for re-use in the wObRGle case below.
    (hwr_gle_or_cle_case : WriteRead.wObR.GleOrCle.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

def Event.gCacheOfCEvent (e : Event n) : CacheId n :=
  match e.protocol with
  | .cluster1 => .mkCacheGlobalP n (.mk 0 (by simp))
  | .cluster2 => .mkCacheGlobalP n (.mk 1 (by simp))
  | .global => panic! "Error: The Global Directory does not have a corresponding global cache."

structure Behaviour.diffClusters.encapGDown {cmp : CompoundProtocol n}
  {b : Behaviour n} {init : InitialSystemState n}
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  gDirOnSWImplGDown :
    -- If e_w accesses the global dir, and is immediately pred to e_r's global dir access.
    b.directoryStateMadeOn n init hr_c_and_g_lin.hreq's_global_lin.choose = .SW ⟨SW, by simp⟩ e_w.gCacheOfCEvent →
    ∃ e_r_down ∈ b, e_r_down.cid = e_w.gCacheOfCEvent ∧ e_r_down.down

inductive WriteRead.wObR.GleAndCle.sameOrDifferentCluster.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  -- {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
| sameCluster
  (hSameCluster : e_w.protocol = e_r.protocol)
  (hw_ob_r_gle_cases : WriteRead.wObR.GleOrCle.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
| diffCluster
  (hDiffCluster : e_w.protocol ≠ e_r.protocol)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hr_gdown_to_w : Behaviour.diffClusters.encapGDown e_w hr_c_and_g_lin)
  (hdiff_cache_case : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)

inductive Behaviour.readsFrom.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  -- {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  -- `e_w`'s GLE is the same as `e_r`'s GLE
  | wEqRGle
    (hw_r_gle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    -- Use `Behaviour.readsFrom.wEqRGle.cases` to distinguish subcases of this case.
    (hw_eq_r_gle_cases : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  -- `e_w`'s GLE is Ordered Before `e_r`'s GLE
  | wObRGle
    (hw_r_gle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
    -- use inductive to define subcases of this case
    (hw_ob_r_gle_cases : WriteRead.wObR.GleAndCle.sameOrDifferentCluster.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

-- Define Constraints where RF should be proven to hold.

/- ========= BEGIN RF Constraints ========= -/

def CompoundProtocol.gleOrderedBefore
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n
    hr_c_and_g_lin.hreq's_global_lin.choose

def Event.isDirReadOrEvict (e : Event n) : Prop := e.isDirRead

structure IntermediateDirEvictOrRead
  (e_cdir_inter e_w_cle e_r_cle : Event n)
  : Prop where
  sameProtocol : e_cdir_inter.sameProtocol n e_w_cle
  sameStructure : e_cdir_inter.sameStructure n e_w_cle
  betweenWR : e_cdir_inter.OrderedBetween n e_w_cle e_r_cle

structure CLE.WROrdering.evictOrReadBetween
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  wRSameCluster : e_w.sameProtocol n e_r
  interDirEvictOrRead : ∀ e_cdir_inter ∈ b,
    IntermediateDirEvictOrRead e_cdir_inter
      hw_c_and_g_lin.hreq's_dir_access.choose
      hr_c_and_g_lin.hreq's_dir_access.choose
      → e_cdir_inter.isDirReadOrEvict
  wObR : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
        hr_c_and_g_lin.hreq's_dir_access.choose

/- Cases of CLE if `e_w` GLE ImmPred `e_r` GLE. Same Cluster case. -/
inductive CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | wImmPredRCle (w_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  | evictOrReadBetweenWAndRCleSameCluster (evict_or_read_btn_w_r_cle :
      CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)

/-- Cases of CLE if GLEs are equal. Same Cluster. -/
inductive CompoundProtocol.gleEq.SameCluster.cleEq.cleOb.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | wEqRCle (w_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  | otherCases (same_as_gle_ob_cases : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

structure Behaviour.gdown.encapProxyAndDirAndCDown {cmp : CompoundProtocol n} {e_r : Event n} (e_w : Event n) (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r) : Prop where
  clusterDown : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  existsRGlobalDown : ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant
  clusterDirDownFromProxy :
    Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init existsRGlobalDown.choose SW
    → ∃ e_r_proxy ∈ b, Behaviour.gdown.clusterDirDown n b init e_r_proxy clusterDown.encapDir.existsRClusterDirDown.choose

structure ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w : Event n} {e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  rDown : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  wCleImmPredRDown : ∀ e_cdir_inter ∈ b,
     IntermediateDirEvictOrRead e_cdir_inter
      hw_c_and_g_lin.hreq's_dir_access.choose
      rDown.encapDir.existsRClusterDirDown.choose
     → e_cdir_inter.isDirReadOrEvict
  wObRDown : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
    rDown.encapDir.existsRClusterDirDown.choose

structure ReadDowngradeAtWrite.wCleImmPredDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w : Event n} {e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  rDown : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  wCleImmPredRDown : b.ImmediateBottomPredecessor n
    hw_c_and_g_lin.hreq's_dir_access.choose rDown.encapDir.existsRClusterDirDown.choose
  wCleImmPredRDownReadOrEvict : ∀ e_cdir_inter ∈ b,
     IntermediateDirEvictOrRead e_cdir_inter
      hw_c_and_g_lin.hreq's_dir_access.choose
      rDown.encapDir.existsRClusterDirDown.choose
     → e_cdir_inter.isDirReadOrEvict
  wObRDown : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
    rDown.encapDir.existsRClusterDirDown.choose

/- Cases of CLE if `e_w` GLE ImmPred `e_r` GLE. Different Cluster case. -/
inductive CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  -- TODO: Define def or reuse def of downgrade `e_r_down` from `e_r` to `e_w`'s cluster
  -- Then the cases are either `e_r_down` is an immediate predecessor of `e_w`'s CLE,
  -- or all intermediate directory events between `e_w`'s CLE and `e_r_down` are either evict or read.
  | wCleImmPredDown (w_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
  | evictOrReadBetweenWAndRDown (w_cle_imm_pred_down : ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown hw_c_and_g_lin hr_c_and_g_lin)

inductive CompoundProtocol.gleOB.Cluster.SameOrDiff.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | sameCluster (same_cluster : e_w.sameProtocol n e_r)
    (same_cluster_cases : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  | diffCluster (diff_cluster : ¬ e_w.sameProtocol n e_r)
    (diff_cluster_cases : CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

-- inductive cases on the relationship between the GLEs and CLEs
inductive CompoundProtocol.gleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  | sameGle
    (same_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    (cle_cases : CompoundProtocol.gleEq.SameCluster.cleEq.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  | wObRGle
    (w_ob_r_gle : CompoundProtocol.gleOrderedBefore hw_c_and_g_lin hr_c_and_g_lin)
    (cle_cases : CompoundProtocol.gleOB.Cluster.SameOrDiff.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

/- ========== END RF Constraints ========== -/
