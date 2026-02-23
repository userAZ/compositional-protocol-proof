import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompositionalProof.ProofBasicHelperLemmas

variable (n : Nat)

/- State that for any PPO pair of requests in the same cluster, they satisfy compound linearization order. -/

noncomputable def ClusterRequestLinearizationEvent.linearizationEvent {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
  (e_cmplin : ClusterRequestLinearizationEvent n cmp.shimAxioms b init e (cmp.linearizationOfEvent b init e)) : Event n := match e_cmplin with
  | .clusterCacheLin lin_e => lin_e.choose
  | .clusterDirLin lin_e => lin_e.choose

-- Goal: compound linearization events are in PPO

structure Behaviour.coherentWriteSucceededByDirectoryRequest (b : Behaviour n) (init : InitialSystemState n) (e₂ e₃ : Event n) where
  e₂CoherentWrite : e₂.isCoherentWrite
  e₂NotDown : e₂.isCoherentWrite
  diffCache : e₃.cid ≠ e₂.cid
  sameProtocol : e₃.sameProtocol n e₂
  e₃NotDown : ¬e₃.down
  e₃MissingPerms : b.reqMissingPerms n init e₃

structure Event.rccOStyleDowngrade (b : Behaviour n) (e₂ e₃_dir e₃_downgrade e₃_wb : Event n) where
  dirEncapDowngrade : e₃_dir.Encapsulates n e₃_downgrade
  dirIsDir : e₃_dir.isDirectoryEvent
  downIsDown : e₃_downgrade.down
  downCoherentWeakWrite : e₃_downgrade.isCWeakWrite
  downAtE₂ : e₃_downgrade.cid = e₂.cid
  downgradeBroadcastWb : Behaviour.broadcastWbFromDowngrade n b e₃_downgrade e₃_wb

structure Event.writeBackAtEvent (e₁ e₃_wb e₃_downgrade : Event n) where
  isVdWb : e₃_wb.isVdWriteBack
  sameEntryAsEvent : e₃_wb.sameEntry n e₁
  downEncapWb : e₃_downgrade.Encapsulates n e₃_wb

def CompoundProtocol.lazyCompoundLinearizationOrder (b : Behaviour n) (init : InitialSystemState n)
  (e₂ e_lin₁ : Event n)
  : Prop :=
  ∀ e₃ ∈ b,
    ∀ e₂_dir ∈ b, b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e₂) true e₂ e₂_dir →
    ∀ e₃_dir ∈ b, b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e₃) true e₃ e₃_dir →
    b.ImmediateBottomPredecessor n e₂_dir e₃_dir →
    e₂.addr = e₃.addr → e₂_dir.addr = e₃_dir.addr →
    e_lin₁.finishesBefore n e₃_dir

def CompoundProtocol.CompoundLinearizationOrder (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e₁ e₂ : Event n) -- (cmp_lin : Behaviour.clusterRequestLinearizationEvent.wrapper n)
  : Prop :=
  let e_lin₁ := cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁) |>.linearizationEvent
  let e_lin₂ := cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂) |>.linearizationEvent
  e₁.isPPOPair n e₂ →
  e_lin₁.OrderedBefore n e_lin₂
  ∨ CompoundProtocol.lazyCompoundLinearizationOrder n b init e₂ e_lin₁

lemma CompoundProtocol.compound_linearization_order_of_events_ordered_before_and_linearizes_at_cache
  {cmp : CompoundProtocol n}
  (he₁_ob_e₂ : Event.OrderedBefore n e₁ e₂)
  (hcluster_cache_lin_e₁ : ∃ e_cmplin ∈ b, Behaviour.eventCompoundLinearizes.atCache n b init e₁ e_cmplin (cmp.linearizationOfEvent b init e₁))
  (hcluster_cache_lin_e₂ : ∃ e_cmplin ∈ b, Behaviour.eventCompoundLinearizes.atCache n b init e₂ e_cmplin (cmp.linearizationOfEvent b init e₂))
  (he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁) = ClusterRequestLinearizationEvent.clusterCacheLin hcluster_cache_lin_e₁)
  (he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂) = ClusterRequestLinearizationEvent.clusterCacheLin hcluster_cache_lin_e₂)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  have he₁_lin_cache := hcluster_cache_lin_e₁.choose_spec.right.e_creq_is_e_glin
  have he₂_lin_cache := hcluster_cache_lin_e₂.choose_spec.right.e_creq_is_e_glin

  simp[CompoundProtocol.CompoundLinearizationOrder]
  intro hppo
  apply Or.intro_left
  simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

  simp[he₁_lin_cache, he₂_lin_cache, he₁_ob_e₂]

lemma Event.contradiction_of_has_perms_and_no_perms {b init e rw property}
  (he_req : e.req = ⟨⟨rw, true, .SC⟩, property⟩)
  (he_not_down : ¬ e.down)
  (he_has_perms : Behaviour.reqHasPerms n b init e)
  (he_no_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
    cases he_has_perms
    . case hasPerms his_coherent hhas_perms =>
      simp[Behaviour.hasPerms] at hhas_perms
      cases he_no_perms
      . case downgrade he₁_down hgreq_on_mrs =>
        absurd he₁_down
        simp [he_not_down]
      . case noPermsForNonNcRelAcqWeakWrite hnot_down hrel hno_perms =>
        simp[Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
        absurd hhas_perms
        simp[hno_perms]
      . case ncRelAcqWeakWriteNotOnCoherentState hnot_down hrel_acq hno_perms =>
        simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,] at hrel_acq
        match e with
        | .cacheEvent ce =>
          simp[Event.req] at he_req
          simp[CacheEvent.isAcquire, CacheEvent.isNcRelease, ValidRequest.isAcquire, ValidRequest.isNcRelease,
            he_req] at hrel_acq
        | .directoryEvent _ => simp[] at hrel_acq
    . case ncRelAcqWeakWriteHasCoherentPerms hrel_acq_ww hcoherent_perms =>
        simp[Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite] at hrel_acq_ww
        match e with
        | .cacheEvent ce =>
          simp[Event.req] at he_req
          simp[CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
            ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
            he_req] at hrel_acq_ww
        | .directoryEvent _ => simp[] at hrel_acq_ww
    . case ncWeakReadHasPermsNotVd hweak_read hhas_perms_not_vd =>
        simp[Event.isNcWeakRead,] at hweak_read
        match e with
        | .cacheEvent ce =>
          simp[Event.req] at he_req
          simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead,
            he_req] at hweak_read
        | .directoryEvent _ => simp[] at hweak_read

lemma Event.contradiction_of_nc_release_request_has_perms_and_no_perms {b init e}
  (he_req : e.req.isNcRelease)
  (he_not_down : ¬ e.down)
  (he_has_perms : Behaviour.reqHasPerms n b init e)
  (he_no_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
    cases he_has_perms
    . case hasPerms his_coherent hhas_perms =>
      simp[Behaviour.hasPerms] at hhas_perms
      simp[isCoherent] at his_coherent
      match e with
      | .cacheEvent ce =>
        simp[ValidRequest.isCoherent, Request.isCoherent] at his_coherent
        simp[Event.req, ValidRequest.isNcRelease,] at he_req
        simp[he_req] at his_coherent
      | .directoryEvent _ => simp[] at his_coherent
    . case ncRelAcqWeakWriteHasCoherentPerms hrel_acq_ww hcoherent_perms =>
      cases he_no_perms
      . case downgrade hdown hevict => contradiction
      . case noPermsForNonNcRelAcqWeakWrite hnot_down hnotrel_acq_ww hno_perms => contradiction
      . case ncRelAcqWeakWriteNotOnCoherentState hnot_down hacq_rel hacq_rel_ww_no_perms =>
        simp[Behaviour.acqRelWeakWriteNoPerms] at hacq_rel_ww_no_perms
        apply hacq_rel_ww_no_perms
        . case a =>
          simp[Behaviour.eventOnCoherentState, ]
          have hmade_on_coherent_state := hcoherent_perms.onCoherentState
          simp[ Behaviour.reqMadeOnCoherentState, Behaviour.stateReqMadeOn] at hmade_on_coherent_state
          simp[hmade_on_coherent_state]
        . case a =>
          simp[Behaviour.eventOnStateHasPerms]
          have hhas_perms := hcoherent_perms.hasPerms
          simp[Behaviour.hasPerms] at hhas_perms
          simp[hhas_perms]
    . case ncWeakReadHasPermsNotVd hweak_read hhas_perms_not_vd =>
        simp[Event.isNcWeakRead,] at hweak_read
        match e with
        | .cacheEvent ce =>
          simp[Event.req, ValidRequest.isNcRelease, ] at he_req
          simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, ] at hweak_read
          simp[hweak_read] at he_req
        | .directoryEvent _ => simp[] at hweak_read

lemma Event.contradiction_of_weak_write_request_has_perms_and_no_perms {b init e}
  -- (he_req : e.req.isAcquire)
  (he_req : Event.req n e = ⟨{ rw := .w, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he_not_down : ¬ e.down)
  (he_has_perms : Behaviour.reqHasPerms n b init e)
  (he_no_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
    cases he_has_perms
    . case hasPerms his_coherent hhas_perms =>
      simp[Behaviour.hasPerms] at hhas_perms
      simp[isCoherent] at his_coherent
      match e with
      | .cacheEvent ce =>
        simp[ValidRequest.isCoherent, Request.isCoherent] at his_coherent
        simp[Event.req, ValidRequest.isAcquire,] at he_req
        simp[he_req] at his_coherent
      | .directoryEvent _ => simp[] at his_coherent
    . case ncRelAcqWeakWriteHasCoherentPerms hrel_acq_ww hcoherent_perms =>
      cases he_no_perms
      . case downgrade hdown hevict => contradiction
      . case noPermsForNonNcRelAcqWeakWrite hnot_down hnotrel_acq_ww hno_perms => contradiction
      . case ncRelAcqWeakWriteNotOnCoherentState hnot_down hacq_rel hacq_rel_ww_no_perms =>
        simp[Behaviour.acqRelWeakWriteNoPerms] at hacq_rel_ww_no_perms
        apply hacq_rel_ww_no_perms
        . case a =>
          simp[Behaviour.eventOnCoherentState, ]
          have hmade_on_coherent_state := hcoherent_perms.onCoherentState
          simp[ Behaviour.reqMadeOnCoherentState, Behaviour.stateReqMadeOn] at hmade_on_coherent_state
          simp[hmade_on_coherent_state]
        . case a =>
          simp[Behaviour.eventOnStateHasPerms]
          have hhas_perms := hcoherent_perms.hasPerms
          simp[Behaviour.hasPerms] at hhas_perms
          simp[hhas_perms]
    . case ncWeakReadHasPermsNotVd hweak_read hhas_perms_not_vd =>
      simp[Event.isNcWeakRead,] at hweak_read
      match e with
      | .cacheEvent ce =>
        simp[Event.req, ValidRequest.isAcquire, ] at he_req
        simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, ] at hweak_read
        simp[hweak_read] at he_req
      | .directoryEvent _ => simp[] at hweak_read

lemma Event.contradiction_of_acquire_request_has_perms_and_no_perms {b init e}
  (he_req : e.req.isAcquire)
  (he_not_down : ¬ e.down)
  (he_has_perms : Behaviour.reqHasPerms n b init e)
  (he_no_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
    cases he_has_perms
    . case hasPerms his_coherent hhas_perms =>
      simp[Behaviour.hasPerms] at hhas_perms
      simp[isCoherent] at his_coherent
      match e with
      | .cacheEvent ce =>
        simp[ValidRequest.isCoherent, Request.isCoherent] at his_coherent
        simp[Event.req, ValidRequest.isAcquire,] at he_req
        simp[he_req] at his_coherent
      | .directoryEvent _ => simp[] at his_coherent
    . case ncRelAcqWeakWriteHasCoherentPerms hrel_acq_ww hcoherent_perms =>
      cases he_no_perms
      . case downgrade hdown hevict => contradiction
      . case noPermsForNonNcRelAcqWeakWrite hnot_down hnotrel_acq_ww hno_perms => contradiction
      . case ncRelAcqWeakWriteNotOnCoherentState hnot_down hacq_rel hacq_rel_ww_no_perms =>
        simp[Behaviour.acqRelWeakWriteNoPerms] at hacq_rel_ww_no_perms
        apply hacq_rel_ww_no_perms
        . case a =>
          simp[Behaviour.eventOnCoherentState, ]
          have hmade_on_coherent_state := hcoherent_perms.onCoherentState
          simp[ Behaviour.reqMadeOnCoherentState, Behaviour.stateReqMadeOn] at hmade_on_coherent_state
          simp[hmade_on_coherent_state]
        . case a =>
          simp[Behaviour.eventOnStateHasPerms]
          have hhas_perms := hcoherent_perms.hasPerms
          simp[Behaviour.hasPerms] at hhas_perms
          simp[hhas_perms]
    . case ncWeakReadHasPermsNotVd hweak_read hhas_perms_not_vd =>
        simp[Event.isNcWeakRead,] at hweak_read
        match e with
        | .cacheEvent ce =>
          simp[Event.req, ValidRequest.isAcquire, ] at he_req
          simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, ] at hweak_read
          simp[hweak_read] at he_req
        | .directoryEvent _ => simp[] at hweak_read

lemma Event.contradiction_of_coherent_request_has_perms_and_no_perms {b init e}
  (he_req : e.req.isCoherent)
  (he_not_down : ¬ e.down)
  (he_has_perms : Behaviour.reqHasPerms n b init e)
  (he_no_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
    cases he_has_perms
    . case hasPerms his_coherent hhas_perms =>
      simp[Behaviour.hasPerms] at hhas_perms
      cases he_no_perms
      . case downgrade he₁_down hgreq_on_mrs =>
        absurd he₁_down
        simp [he_not_down]
      . case noPermsForNonNcRelAcqWeakWrite hnot_down hrel hno_perms =>
        simp[Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
        absurd hhas_perms
        simp[hno_perms]
      . case ncRelAcqWeakWriteNotOnCoherentState hnot_down hrel_acq hno_perms =>
        simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,] at hrel_acq
        match e with
        | .cacheEvent ce =>
          simp[Event.req, ValidRequest.isCoherent, Request.isCoherent] at he_req
          simp[CacheEvent.isAcquire, CacheEvent.isNcRelease, ValidRequest.isAcquire, ValidRequest.isNcRelease,]
            at hrel_acq
          cases hrel_acq
          . case inl hce_req_acq => simp[hce_req_acq] at he_req
          . case inr hce_req_nc_rel => simp[hce_req_nc_rel] at he_req
        | .directoryEvent _ => simp[] at hrel_acq
    . case ncRelAcqWeakWriteHasCoherentPerms hrel_acq_ww hcoherent_perms =>
        simp[Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite] at hrel_acq_ww
        match e with
        | .cacheEvent ce =>
          simp[Event.req, ValidRequest.isCoherent, Request.isCoherent] at he_req
          simp[CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
            ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,] at hrel_acq_ww
          cases hrel_acq_ww
          . case inl hce_acq => simp[hce_acq] at he_req
          . case inr hnc_rel_ww =>
            cases hnc_rel_ww
            . case inl hnc_rel => simp[hnc_rel] at he_req
            . case inr hww => simp[hww] at he_req
        | .directoryEvent _ => simp[] at hrel_acq_ww
    . case ncWeakReadHasPermsNotVd hweak_read hhas_perms_not_vd =>
        simp[Event.isNcWeakRead,] at hweak_read
        match e with
        | .cacheEvent ce =>
          simp[Event.req, ValidRequest.isCoherent, Request.isCoherent] at he_req
          simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, ] at hweak_read
          simp[hweak_read] at he_req
        | .directoryEvent _ => simp[] at hweak_read

/-- [useful] Very useful -/
lemma CompoundProtocol.dir_lin_encap_global_dir_lin
  {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  -- (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_generated_cdir e_translated_greq)
  -- (he_encap_corr_dir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init e) true e e_generated_cdir)
  (hgenerated_cdir_encap_greq :
    Event.clusterDirEncapCorrespondingGlobalCache n b e_generated_cdir e_translated_greq)
  (hgreq_encap_corr_gdir :
    Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_translated_greq e_translated_greq_lin /- rename hat_dir.choose to e_translated_greq_lin -/)
  (hgcache_lin_at_gdir :
    Behaviour.requestLinearizesAtDirectory n b init e_translated_greq e_gdir e_translated_greq_lin)
  : e_generated_cdir.Encapsulates n e_translated_greq_lin := by
  have hglin_is_gdir := hgcache_lin_at_gdir.dirIsLin
  rw[hglin_is_gdir]

  have hgreq_lin := hgcache_lin_at_gdir.reqCorrespondsToDir
  cases hgreq_lin
  . case encapDir hgreq_no_perms hgreq_encap_gdir =>
    calc Event.Encapsulates n _ e_translated_greq := hgenerated_cdir_encap_greq.encapGlobalCache
      Event.Encapsulates n _ e_gdir := hgreq_encap_gdir.reqEncapDir
  . case orderBeforeDir hgreq_has_perms _ _ _ _ =>
    exfalso
    apply Event.contradiction_of_has_perms_and_no_perms
    . case he_req => exact hgenerated_cdir_encap_greq.gReqOfCDir.matchingOp
    . case he_not_down => exact hgenerated_cdir_encap_greq.gReqOfCDir.notDowngrade
    . case he_has_perms => exact hgreq_has_perms
    . case he_no_perms => exact hgreq_encap_corr_gdir.reqHasNoPerms
  . case orderAfterDir hweak_read_vd himm_successor _ =>
    have hweak_req := hweak_read_vd.weakReq
    have hgreq_req := hgenerated_cdir_encap_greq.gReqOfCDir.matchingOp
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e_translated_greq with
    | .cacheEvent ce =>
      simp[Event.req] at hgreq_req
      simp[hgreq_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req


lemma CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin
  {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_generated_cdir e_translated_greq)
  (he_encap_corr_dir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init e) true e e_generated_cdir)
  (hgenerated_cdir_encap_greq :
    Event.clusterDirEncapCorrespondingGlobalCache n b e_generated_cdir e_translated_greq)
  (hgreq_encap_corr_gdir :
    Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_translated_greq e_translated_greq_lin /- rename hat_dir.choose to e_translated_greq_lin -/)
  (hgcache_lin_at_gdir :
    Behaviour.requestLinearizesAtDirectory n b init e_translated_greq e_gdir e_translated_greq_lin)
  : e.Encapsulates n e_translated_greq_lin := by
  have hglin_is_gdir := hgcache_lin_at_gdir.dirIsLin
  rw[hglin_is_gdir]

  have hgreq_lin := hgcache_lin_at_gdir.reqCorrespondsToDir
  cases hgreq_lin
  . case encapDir hgreq_no_perms hgreq_encap_gdir =>
    calc e.Encapsulates n e_generated_cdir := he_encap_corr_dir.reqEncapDir
      Event.Encapsulates n _ e_translated_greq := hgenerated_cdir_encap_greq.encapGlobalCache
      Event.Encapsulates n _ e_gdir := hgreq_encap_gdir.reqEncapDir
  . case orderBeforeDir hgreq_has_perms _ _ _ _ =>
    exfalso
    apply Event.contradiction_of_has_perms_and_no_perms
    . case he_req => exact htranslation.gReqOfCDir.matchingOp
    . case he_not_down => exact htranslation.gReqOfCDir.notDowngrade
    . case he_has_perms => exact hgreq_has_perms
    . case he_no_perms => exact hgreq_encap_corr_gdir.reqHasNoPerms
  . case orderAfterDir hweak_read_vd himm_successor _ =>
    have hweak_req := hweak_read_vd.weakReq
    have hgreq_req := htranslation.gReqOfCDir.matchingOp
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e_translated_greq with
    | .cacheEvent ce =>
      simp[Event.req] at hgreq_req
      simp[hgreq_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req

/-- Very useful. -/
lemma CompoundProtocol.request_encapsulates_compound_linearization_event
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (hgenerated_cdir_is_dir : e_generated_cdir.isDirectoryEvent)
  (he_encap_corr_dir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init e) true e e_generated_cdir)
  (hcdir_requests_gcache : Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent n cmp.shimAxioms b init e_generated_cdir e_generated_cmp_lin)
  : e.Encapsulates n e_generated_cmp_lin := by
      simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hcdir_requests_gcache
      simp[hgenerated_cdir_is_dir] at hcdir_requests_gcache

      split at hcdir_requests_gcache
      . case h_1 _ _ _ _ =>
        exfalso; exact hcdir_requests_gcache
      . case h_2 _ _ htranslation _ =>
        have := htranslation.choose_spec.right
        have hdir_encap_gcache := htranslation.choose_spec.right
        -- .encapGlobalCache
        simp[Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hcdir_requests_gcache
        obtain ⟨hgcache_lin,hgcache_lin_cases⟩ := hcdir_requests_gcache
        split at hgcache_lin_cases
        . case h_1 hgcache_lin_event hat_dir =>
          have := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right.reqCorrespondsToDir
          simp[hgcache_lin_cases]
          -- lemma here.
          -- calc e.Encapsulates n e_generated_cdir := he_encap_dir
            -- Event.Encapsulates n _ e_
          apply CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin
          . case htranslation => exact htranslation.choose_spec.right
          . case he_encap_corr_dir => exact he_encap_corr_dir
          . case hgenerated_cdir_encap_greq => exact hdir_encap_gcache
          . case hgreq_encap_corr_gdir => exact hat_dir.choose_spec.right
          . case hgcache_lin_at_gdir => exact hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        . case h_2 hgcache_lin_event hat_cache =>
          exfalso; exact hgcache_lin_cases

lemma CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (he_req : e.req.isNcRelease)
  (he_not_down : ¬ e.down)
  (hdir_lin : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e e_generated_lin)
  (he_has_no_perms : Behaviour.reqMissingPerms n b init e)
  (he_req_at_cdir : Behaviour.requestLinearizesAtDirectory n b init e e_generated_cdir e_generated_lin)
  (he_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir e_generated_cmp_lin)
  : e.Encapsulates n e_generated_cmp_lin := by

  have he_cdir_spec := he_req_at_cdir.reqCorrespondsToDir
  cases he_cdir_spec
  . case encapDir he_missing_perms he_encap_corr_dir =>
    have he_encap_dir := he_encap_corr_dir.reqEncapDir

    have hreq_corr_to_dir := he_req_at_cdir
    cases he_lin_dir
    . case previousGlobalCacheGotPerms hgcache_has_perms hcdir_is_glin =>
      simp[hcdir_is_glin]
      exact he_encap_dir
    . case getGlobalCachePerms hcdir_no_perms_in_gcache hcdir_requests_gcache =>
      simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hcdir_requests_gcache
      simp[he_req_at_cdir.isDir] at hcdir_requests_gcache

      split at hcdir_requests_gcache
      . case h_1 _ _ _ _ =>
        exfalso; exact hcdir_requests_gcache
      . case h_2 _ _ htranslation _ =>
        have := htranslation.choose_spec.right
        have hdir_encap_gcache := htranslation.choose_spec.right
        -- .encapGlobalCache
        simp[Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hcdir_requests_gcache
        obtain ⟨hgcache_lin,hgcache_lin_cases⟩ := hcdir_requests_gcache
        split at hgcache_lin_cases
        . case h_1 hgcache_lin_event hat_dir =>
          have := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right.reqCorrespondsToDir
          simp[hgcache_lin_cases]
          -- lemma here.
          -- calc e.Encapsulates n e_generated_cdir := he_encap_dir
            -- Event.Encapsulates n _ e_
          apply CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin
          . case htranslation => exact htranslation.choose_spec.right
          . case he_encap_corr_dir => exact he_encap_corr_dir
          . case hgenerated_cdir_encap_greq => exact hdir_encap_gcache
          . case hgreq_encap_corr_gdir => exact hat_dir.choose_spec.right
          . case hgcache_lin_at_gdir => exact hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        . case h_2 hgcache_lin_event hat_cache =>
          exfalso; exact hgcache_lin_cases
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir _ _ =>
    exfalso
    apply Event.contradiction_of_nc_release_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir _ =>
    have hweak_req := hweak_read.weakReq
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e with
    | .cacheEvent ce =>
      simp[Event.req, ValidRequest.isNcRelease,] at he_req
      simp[he_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req

lemma CompoundProtocol.acquire_request_encapsulates_compound_linearization_event
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (he_req : e.req.isAcquire)
  (he_not_down : ¬ e.down)
  (hdir_lin : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e e_generated_lin)
  (he_has_no_perms : Behaviour.reqMissingPerms n b init e)
  (he_req_at_cdir : Behaviour.requestLinearizesAtDirectory n b init e e_generated_cdir e_generated_lin)
  (he_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir e_generated_cmp_lin)
  : e.Encapsulates n e_generated_cmp_lin := by

  have he_cdir_spec := he_req_at_cdir.reqCorrespondsToDir
  cases he_cdir_spec
  . case encapDir he_missing_perms he_encap_corr_dir =>
    have he_encap_dir := he_encap_corr_dir.reqEncapDir

    have hreq_corr_to_dir := he_req_at_cdir
    cases he_lin_dir
    . case previousGlobalCacheGotPerms hgcache_has_perms hcdir_is_glin =>
      simp[hcdir_is_glin]
      exact he_encap_dir
    . case getGlobalCachePerms hcdir_no_perms_in_gcache hcdir_requests_gcache =>
      simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hcdir_requests_gcache
      simp[he_req_at_cdir.isDir] at hcdir_requests_gcache

      split at hcdir_requests_gcache
      . case h_1 _ _ _ _ =>
        exfalso; exact hcdir_requests_gcache
      . case h_2 _ _ htranslation _ =>
        have := htranslation.choose_spec.right
        have hdir_encap_gcache := htranslation.choose_spec.right
        -- .encapGlobalCache
        simp[Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hcdir_requests_gcache
        obtain ⟨hgcache_lin,hgcache_lin_cases⟩ := hcdir_requests_gcache
        split at hgcache_lin_cases
        . case h_1 hgcache_lin_event hat_dir =>
          have := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right.reqCorrespondsToDir
          simp[hgcache_lin_cases]
          -- lemma here.
          -- calc e.Encapsulates n e_generated_cdir := he_encap_dir
            -- Event.Encapsulates n _ e_
          apply CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin
          . case htranslation => exact htranslation.choose_spec.right
          . case he_encap_corr_dir => exact he_encap_corr_dir
          . case hgenerated_cdir_encap_greq => exact hdir_encap_gcache
          . case hgreq_encap_corr_gdir => exact hat_dir.choose_spec.right
          . case hgcache_lin_at_gdir => exact hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        . case h_2 hgcache_lin_event hat_cache =>
          exfalso; exact hgcache_lin_cases
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir _ _ =>
    exfalso
    apply Event.contradiction_of_acquire_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir _ =>
    have hweak_req := hweak_read.weakReq
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e with
    | .cacheEvent ce =>
      simp[Event.req, ValidRequest.isAcquire,] at he_req
      simp[he_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req

lemma CompoundProtocol.coherent_request_encapsulates_compound_linearization_event
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (he_req : e.req.isCoherent)
  (he_not_down : ¬ e.down)
  (hdir_lin : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e e_generated_lin)
  (he_has_no_perms : Behaviour.reqMissingPerms n b init e)
  (he_req_at_cdir : Behaviour.requestLinearizesAtDirectory n b init e e_generated_cdir e_generated_lin)
  (he_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir e_generated_cmp_lin)
  : e.Encapsulates n e_generated_cmp_lin := by

  have he_cdir_spec := he_req_at_cdir.reqCorrespondsToDir
  cases he_cdir_spec
  . case encapDir he_missing_perms he_encap_corr_dir =>
    have he_encap_dir := he_encap_corr_dir.reqEncapDir

    have hreq_corr_to_dir := he_req_at_cdir
    cases he_lin_dir
    . case previousGlobalCacheGotPerms hgcache_has_perms hcdir_is_glin =>
      simp[hcdir_is_glin]
      exact he_encap_dir
    . case getGlobalCachePerms hcdir_no_perms_in_gcache hcdir_requests_gcache =>
      simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hcdir_requests_gcache
      simp[he_req_at_cdir.isDir] at hcdir_requests_gcache

      split at hcdir_requests_gcache
      . case h_1 _ _ _ _ =>
        exfalso; exact hcdir_requests_gcache
      . case h_2 _ _ htranslation _ =>
        have := htranslation.choose_spec.right
        have hdir_encap_gcache := htranslation.choose_spec.right
        -- .encapGlobalCache
        simp[Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hcdir_requests_gcache
        obtain ⟨hgcache_lin,hgcache_lin_cases⟩ := hcdir_requests_gcache
        split at hgcache_lin_cases
        . case h_1 hgcache_lin_event hat_dir =>
          have := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right.reqCorrespondsToDir
          simp[hgcache_lin_cases]
          -- lemma here.
          -- calc e.Encapsulates n e_generated_cdir := he_encap_dir
            -- Event.Encapsulates n _ e_
          apply CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin
          . case htranslation => exact htranslation.choose_spec.right
          . case he_encap_corr_dir => exact he_encap_corr_dir
          . case hgenerated_cdir_encap_greq => exact hdir_encap_gcache
          . case hgreq_encap_corr_gdir => exact hat_dir.choose_spec.right
          . case hgcache_lin_at_gdir => exact hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        . case h_2 hgcache_lin_event hat_cache =>
          exfalso; exact hgcache_lin_cases
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir _ _ =>
    exfalso
    apply Event.contradiction_of_coherent_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir _ =>
    have hweak_req := hweak_read.weakReq
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e with
    | .cacheEvent ce =>
      simp[Event.req, ValidRequest.isCoherent, Request.isCoherent] at he_req
      simp[he_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req

inductive Event.ncReleaseOrAcquireOrCoherent (e : Event n)
| ncRelease (nc_rel : e.req.isNcRelease) : Event.ncReleaseOrAcquireOrCoherent e
| acquire (acq : e.req.isAcquire) : Event.ncReleaseOrAcquireOrCoherent e
| coherent (coherent : e.req.isCoherent) : Event.ncReleaseOrAcquireOrCoherent e

lemma CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
  {cmp : CompoundProtocol n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (he₁_req : e₁.ncReleaseOrAcquireOrCoherent n)
  (he₂_req : e₂.ncReleaseOrAcquireOrCoherent n)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
    match he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁)
      , he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂)
      with
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      apply CompoundProtocol.compound_linearization_order_of_events_ordered_before_and_linearizes_at_cache
      . case he₁_ob_e₂ => exact he₁_ob_e₂
      . case he₁_lin => exact he₁_lin
      . case he₂_lin => exact he₂_lin
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_cache := hcluster_cache_lin_e₂.choose_spec.right.e_creq_is_e_glin

      simp[he₂_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir
      split at he₁_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₁_lin_dir
      . case h_2 hcreq_lin hdir_lin hrequest_lin =>
        have hreq_without_perms_lin_at_dir := hdir_lin.choose_spec.right
        have hreq_lin_at_dir := hdir_lin.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        have he₁_encap_e₁_cmp_lin : e₁.Encapsulates n hcluster_dir_lin_e₁.choose := by
          cases he₁_req
          . case ncRelease hnc_rel =>
            apply CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event n hnc_rel
            . case he_not_down => exact he₁_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₁_lin_dir
          . case acquire hacq =>
            apply CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n hacq
            . case he_not_down => exact he₁_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₁_lin_dir
          . case coherent hcoherent =>
            apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n hcoherent
            . case he_not_down => exact he₁_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₁_lin_dir

        calc hcluster_dir_lin_e₁.choose.EncapsulatedBy n e₁ := he₁_encap_e₁_cmp_lin
          Event.OrderedBefore n e₁ e₂ := he₁_ob_e₂
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_cache := hcluster_cache_lin_e₁.choose_spec.right.e_creq_is_e_glin
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[he₁_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₂_lin_dir
      split at he₂_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₂_lin_dir
      . case h_2 hcreq_lin hdir_lin hrequest_lin =>
        have hreq_without_perms_lin_at_dir := hdir_lin.choose_spec.right
        have hreq_lin_at_dir := hdir_lin.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        have he₂_encap_e₂_cmp_lin : e₂.Encapsulates n hcluster_dir_lin_e₂.choose := by
          cases he₂_req
          . case ncRelease hnc_rel =>
            apply CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event n hnc_rel
            . case he_not_down => exact he₂_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₂_lin_dir
          . case acquire hacq =>
            apply CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n hacq
            . case he_not_down => exact he₂_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₂_lin_dir
          . case coherent hcoherent =>
            apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n hcoherent
            . case he_not_down => exact he₂_not_down
            . case hdir_lin => exact hreq_without_perms_lin_at_dir
            . case he_has_no_perms => exact hreq_without_perms_lin_at_dir.reqHasNoPerms
            . case he_req_at_cdir => exact hreq_lin_at_dir
            . case he_lin_dir => exact he₂_lin_dir

        calc Event.OrderedBefore n e₁ e₂ := he₁_ob_e₂
          e₂.Encapsulates n hcluster_dir_lin_e₂.choose := he₂_encap_e₂_cmp_lin
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir he₂_lin_dir
      split at he₁_lin_dir
      . case h_1 _ h _ => exfalso; exact he₁_lin_dir
      . case h_2 _ hdir_lin₁ _ =>
        split at he₂_lin_dir
        . case h_1 _ h _ => exfalso; exact he₂_lin_dir
        . case h_2 _ hdir_lin₂ _ =>
          have hreq₁_lin_at_dir := hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have hreq₂_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right

          have hreq_without_perms_lin_at_dir₁ := hdir_lin₁.choose_spec.right
          have hreq_lin_at_dir₁ := hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have he₁_encap_e₁_cmp_lin : e₁.Encapsulates n hcluster_dir_lin_e₁.choose := by
            cases he₁_req
            . case ncRelease hnc_rel =>
              apply CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event n hnc_rel
              . case he_not_down => exact he₁_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₁
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₁.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₁
              . case he_lin_dir => exact he₁_lin_dir
            . case acquire hacq =>
              apply CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n hacq
              . case he_not_down => exact he₁_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₁
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₁.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₁
              . case he_lin_dir => exact he₁_lin_dir
            . case coherent hcoherent =>
              apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n hcoherent
              . case he_not_down => exact he₁_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₁
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₁.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₁
              . case he_lin_dir => exact he₁_lin_dir

          have hreq_without_perms_lin_at_dir₂ := hdir_lin₂.choose_spec.right
          have hreq_lin_at_dir₂ := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have he₂_encap_e₂_cmp_lin : e₂.Encapsulates n hcluster_dir_lin_e₂.choose := by
            cases he₂_req
            . case ncRelease hnc_rel =>
              apply CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event n hnc_rel
              . case he_not_down => exact he₂_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₂
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₂.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₂
              . case he_lin_dir => exact he₂_lin_dir
            . case acquire hacq =>
              apply CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n hacq
              . case he_not_down => exact he₂_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₂
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₂.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₂
              . case he_lin_dir => exact he₂_lin_dir
            . case coherent hcoherent =>
              apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n hcoherent
              . case he_not_down => exact he₂_not_down
              . case hdir_lin => exact hreq_without_perms_lin_at_dir₂
              . case he_has_no_perms => exact hreq_without_perms_lin_at_dir₂.reqHasNoPerms
              . case he_req_at_cdir => exact hreq_lin_at_dir₂
              . case he_lin_dir => exact he₂_lin_dir

          calc hcluster_dir_lin_e₁.choose.EncapsulatedBy n e₁ := he₁_encap_e₁_cmp_lin
            e₁.OrderedBefore n e₂ := he₁_ob_e₂
            e₂.Encapsulates n hcluster_dir_lin_e₂.choose := he₂_encap_e₂_cmp_lin

/- Non-Coherent Release: Weak request ordered before a release -/

/-

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_read_and_non_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_req : Event.req n e₁ = ⟨{ rw := .r, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := false, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  sorry

-- BEGIN attempt to prove that a weak write `e_ww` linearizes before or at a VdWriteBack where `e_ww.OrderedBefore e_wb`

inductive Event.isAcqNcRelCRelVdWB (e : Event n) : Prop
| acq (isAcq : e.isAcquire) : Event.isAcqNcRelCRelVdWB e
| ncRel (isNcRel : e.isNcRelease) : Event.isAcqNcRelCRelVdWB e
| CRel (isCRel : e.isCRelease) : Event.isAcqNcRelCRelVdWB e
| VdWB (isVdWB : e.isVdWriteBack) : Event.isAcqNcRelCRelVdWB e
| scW (isSCW : e.isSCWrite) : Event.isAcqNcRelCRelVdWB e
| scR (isSCR : e.isSCRead) : Event.isAcqNcRelCRelVdWB e

def Event.isAcqNcRelCRelVdWB' (e : Event n) : Prop :=
  e.isAcquire ∨ e.isNcRelease ∨ e.isCRelease ∨ e.isVdWriteBack ∨ e.isSCWrite ∨ e.isSCRead

lemma CompoundProtocol.state_before_Vd_of_no_btn_events_on_vd_produce_vd
  (hww_ob_wb : e_ww.OrderedBefore n e_wb)
  (hno_tail_sat : ∀ e ∈ b,
  Event.OrderedBetween n e e_ww e_wb →
    -- Behaviour.stateAfter n b (InitialSystemState.stateAt n init e) e = VdEntry n →
    Behaviour.stateBefore n b (InitialSystemState.stateAt n init e) e = VdEntry n →
    ¬Event.isAcqNcRelCRelVdWB' n e)
  : List.stateAfter n (Behaviour.eventsUpToEvent n b e_wb) (InitialSystemState.stateAt n init e_wb) = VdEntry n := by
  /- This means the immediate predecessor is not `¬Event.isAcqNcRelCRelVdWB'`, so the state after is Vd. -/
  sorry


lemma CompoundProtocol.weak_write_OrderedBefore_vd_write_back'
  {b : Behaviour n} {init : InitialSystemState n}
  (hww_stateAfter_Vd : (Behaviour.stateAfter n b (init.stateAt n e_ww) e_ww).cache = Vd)
  (hsucc_wb : -- ∃ e_succ ∈ b.es,
  Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e_succ_wb fun x =>
    Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  (hww_ob_wb : e_ww.OrderedBefore n e_wb)
  (hww_is_weak_write_or_read : e_ww.isNcWeakWrite ∨ e_ww.isNcWeakRead)
  (hwb_is_vdwb : e_wb.isVdWriteBack)
  (hww_same_entry_wb : e_ww.sameEntry n e_wb)
  : e_succ_wb = e_wb ∨ e_succ_wb.OrderedBefore n e_wb := by
  /- Strategy:
  1. consider eventsUpToEvent `e_wb`. reverse induction on the list -/
  -- have hsucc_wb_in_eventsUpToEvent_wb : e_succ_wb ∈ (Behaviour.eventsUpToEvent n b e_wb) ∨ e_succ_wb = e_wb := by
  --   sorry
  by_cases hno_tail_sat : ∀ e ∈ b, e.OrderedBetween n e_ww e_wb →
    -- (b.stateAfter n (init.stateAt n e) e) = VdEntry n →
    (b.stateBefore n (init.stateAt n e) e) = VdEntry n →
    ¬(e.isAcqNcRelCRelVdWB')
  . case pos =>
    --
    have he_wb_imm_succ : Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e_wb fun x =>
      Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww := by
      constructor
      . case isImmBottomSucc =>
        constructor
        . case isSucc =>
          sorry
        . case noIntermediateSatP =>
          simp[Behaviour.NoIntermediatePredecessorSatisfyingProp, Behaviour.noBottomIntermediatePredecessorAtSuccSatisfyingProp]
          intro e he_in_b he_bot_same_entry he_btn_sat_prop
          obtain ⟨he_ordered_btn,he_sat_prop⟩ := he_btn_sat_prop
          simp [Behaviour.succOnVdWithCorrespondingDir, ] at he_sat_prop
          have he_is_rel_acq_etc := he_sat_prop.isRelAcqOrVdWB
          have := he_sat_prop
          absurd he_is_rel_acq_etc
          apply hno_tail_sat
          . case mk.a => exact he_in_b
          . case mk.a => exact he_ordered_btn
            /-
          . case mk.a =>
            -- have he_before_vd := he_sat_prop.stateBeforeAsVd
            simp[Behaviour.stateAfter]
            rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]
            simp [he_sat_prop.stateBeforeAsVd]
            sorry-/
          . case mk.a =>
            simp[he_sat_prop.stateBeforeAsVd]
        . case sameEntry =>
          sorry
        . case predInB =>
          sorry
        . case succInB =>
          sorry
      . case isBottom =>
        sorry
      . case satisfyP =>
        --
        simp [Event.PropOnEvent]
        simp [Behaviour.succOnVdWithCorrespondingDir]
        constructor
        . case stateBeforeAsVd =>
          simp [Behaviour.stateBefore]
          sorry
        . case isRelAcqOrVdWB =>
          sorry
        . case encapCorresponding =>
          sorry
    rw [show e_succ_wb = e_wb from
      Behaviour.immediate_bottom_successor_satisfying_p_unique
      n b e_ww e_succ_wb e_wb (fun x =>
        Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
      hsucc_wb he_wb_imm_succ
      ]
    apply Or.intro_left
    rfl
  . case neg =>
    simp at hno_tail_sat
    obtain ⟨x, hx_in_b, hx_ob_wb, hx_stateBefore_Vd, hx_rel_acq_etc⟩ := hno_tail_sat
    case intro.intro.intro.intro =>
    apply Or.intro_right
    have hshrinking : ({e ∈ (b.es.finSetEvents n b.finite) | e_ww.OrderedBefore n e ∧ e.OrderedBefore n x})
      ⊂ ({e ∈ (b.es.finSetEvents n b.finite) | e_ww.OrderedBefore n e ∧ e.OrderedBefore n e_wb}) := by
      simp[Set.finSetEvents, Set.Finite.toFinset]
      simp[Finset.ssubset_iff]
      use x
      apply And.intro
      . case h.left =>
        intro hxb hww_ob_x hx_ob_x
        apply Event.contradiction_of_reflexive_ordered_before
        . case he_ob_e => exact hx_ob_x
      . case h.right =>
        apply Finset.insert_subset
        . case ha =>
          simp[Membership.mem] at hx_in_b
          simp
          apply And.intro
          . case left =>
            simp[Membership.mem]
            simp[hx_in_b]
          . case right =>
            simp[hx_ob_wb.pred, hx_ob_wb.succ]
        . case hs =>
          simp[Finset.subset_iff]
          intro y hyb hww_ob_y hy_ob_x
          simp[hyb, hww_ob_y]
          calc Event.OrderedBefore n y x := hy_ob_x
            Event.OrderedBefore n x e_wb := hx_ob_wb.succ
    have hshrinking' := Finset.card_lt_card hshrinking
    have hx_is_succ_wb_or_ob_x : e_succ_wb = x ∨ e_succ_wb.OrderedBefore n x := by
      apply CompoundProtocol.weak_write_OrderedBefore_vd_write_back'
      . case hww_stateAfter_Vd => exact hww_stateAfter_Vd
      . case hsucc_wb => exact hsucc_wb
      . case hww_ob_wb => exact hx_ob_wb.pred
      . case hww_is_weak_write_or_read => exact hww_is_weak_write_or_read
      . case hwb_is_vdwb => exact sorry
      . case hww_same_entry_wb => exact sorry

    cases hx_is_succ_wb_or_ob_x
    . case h.inl he_succ_wb_eq_x =>
      simp[he_succ_wb_eq_x, hx_ob_wb.succ]
    . case h.inr hsucc_wb_ob_x =>
      calc e_succ_wb.OrderedBefore n x := hsucc_wb_ob_x
        x.OrderedBefore n e_wb := hx_ob_wb.succ
termination_by sizeOf ({e' ∈ (b.es.finSetEvents n b.finite) | e_ww.OrderedBefore n e' ∧ e'.OrderedBefore n e_wb}).card
-/

-- END attempt to prove that a weak write `e_ww` linearizes before or at a VdWriteBack where `e_ww.OrderedBefore e_wb`

lemma CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir
  {cmp : CompoundProtocol n}
  {e_generated_cdir : Event n}
  (he_req_at_cdir : Behaviour.requestLinearizesAtDirectory n b init e e_generated_cdir e_generated_lin)
  (hnc_rel_cluster_to_global_translation : Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent n
    cmp.shimAxioms b init e_generated_cdir e_generated_cmp_lin)
  : e_generated_cdir.Encapsulates n e_generated_cmp_lin := by
  simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hnc_rel_cluster_to_global_translation
  simp[he_req_at_cdir.isDir] at hnc_rel_cluster_to_global_translation

  split at hnc_rel_cluster_to_global_translation
  . case h_1 _ _ _ _ =>
    exfalso; exact hnc_rel_cluster_to_global_translation
  . case h_2 _ _ htranslation _ =>
    simp[Behaviour.compoundLinearizationEvent.globalCacheNoPermsReqDirectory] at hnc_rel_cluster_to_global_translation
    obtain ⟨hgcache_lin,hgcache_lin_cases⟩ := hnc_rel_cluster_to_global_translation
    split at hgcache_lin_cases
    . case h_1 hgcache_lin_event hat_dir =>
      have := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right.reqCorrespondsToDir
      simp[hgcache_lin_cases]
      have hgreq_lin_at_gdir := hat_dir.choose_spec.right.reqLinearizeAtDir.choose_spec.right
      have hgreq_spec := hat_dir.choose_spec.right
      apply CompoundProtocol.dir_lin_encap_global_dir_lin
      . case hgenerated_cdir_encap_greq => exact htranslation.choose_spec.right
      . case hgreq_encap_corr_gdir => exact hgreq_spec
      . case hgcache_lin_at_gdir => exact hgreq_lin_at_gdir
    . case h_2 hgcache_lin_event hat_cache =>
      exfalso; exact hgcache_lin_cases

lemma CompoundProtocol.weak_write_or_read_and_nc_release_linearize_at_directory
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  -- {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  -- {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (hww_addr_ne_rel : e_ww.addr ≠ e_nc_rel.addr)
  (hww_eq_rel_cid : e_ww.sameCid n e_nc_rel)
  (he_ww_ob_e_nc_rel : e_ww.OrderedBefore n e_nc_rel)

  (he_ww_in_b : e_ww ∈ b)
  (he_ww_cache : e_ww.isCacheEvent)
  (he_req_ww : Event.req n e_ww = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_ww⟩)
  (he_not_down_ww : ¬ e_ww.down)
  -- (hdir_lin_ww : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_ww e_generated_lin_ww)
  (he_has_no_perms_ww : Behaviour.reqMissingPerms n b init e_ww)
  (he_req_at_cdir_ww : Behaviour.requestLinearizesAtDirectory n b init e_ww e_generated_cdir_ww e_generated_lin_ww)
  (he_lin_dir_ww : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir_ww e_generated_cmp_lin_ww)
  (hgenerated_cdir_ww_in_b : e_generated_cdir_ww ∈ b)

  (hnc_rel_in_b : e_nc_rel ∈ b)
  (he_nc_rel_cache : e_nc_rel.isCacheEvent)
  (hnc_rel_cdir_in_b : e_generated_cdir_nc_rel ∈ b)
  (he_req_nc_rel : Event.req n e_nc_rel = ⟨{ rw := .w, coherent := false, consistency := .Rel }, property_rel⟩)
  (he_not_down_nc_rel : ¬ e_nc_rel.down)
  (hdir_lin_nc_rel : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_nc_rel e_generated_lin_nc_rel)
  (he_has_no_perms_nc_rel : Behaviour.reqMissingPerms n b init e_nc_rel)
  (he_req_at_cdir_nc_rel : Behaviour.requestLinearizesAtDirectory n b init e_nc_rel e_generated_cdir_nc_rel e_generated_lin_nc_rel)
  (he_lin_dir_nc_rel : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir_nc_rel e_generated_cmp_lin_nc_rel)
  : e_generated_cmp_lin_ww.OrderedBefore n e_generated_cmp_lin_nc_rel /- hcluster_dir_lin_e₁.choose abbrev e_generated_cmp_lin -/ := by
  -- have hrel_encap_cmp_lin := CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin n he_lin_dir_nc_rel
  have hrel_encap_lin : Event.Encapsulates n e_nc_rel e_generated_cmp_lin_nc_rel :=
    CompoundProtocol.nc_release_request_encapsulates_compound_linearization_event n
    (by simp[ValidRequest.isNcRelease,]; exact he_req_nc_rel) he_not_down_nc_rel hdir_lin_nc_rel he_has_no_perms_nc_rel
    he_req_at_cdir_nc_rel he_lin_dir_nc_rel

  have hww_cdir_spec := he_req_at_cdir_ww.reqCorrespondsToDir
  cases hww_cdir_spec
  . case encapDir hww_missing_perms hww_encap_corr_dir =>
    -- a Weak Write Cache Request Event (`e_ww`) do not encap a directory event. show a contradiction
    cases hww_missing_perms
    . case downgrade hww_is_down hww_evict_on_mrs => contradiction
    . case noPermsForNonNcRelAcqWeakWrite hww_not_down hww_not_rel_acq_ww hww_no_perms =>
      simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
        Event.isNcRelease, Event.isAcquire, Event.isNcWeakWrite] at hww_not_rel_acq_ww
      cases rw
      . case r =>
        cases he_lin_dir_ww
        . case previousGlobalCacheGotPerms hhas_perms hcmp_lin_is_cdir_ww =>
          rw[hcmp_lin_is_cdir_ww]
          calc e_generated_cdir_ww.EncapsulatedBy n e_ww := hww_encap_corr_dir.reqEncapDir
            e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
            e_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hrel_encap_lin
        . case getGlobalCachePerms hno_gcache_perms hcdir_translate_to_gcache =>
          have hweak_read_lin : Event.Encapsulates n e_ww e_generated_cmp_lin_ww :=
            CompoundProtocol.request_encapsulates_compound_linearization_event n hww_encap_corr_dir.isDir
            hww_encap_corr_dir hcdir_translate_to_gcache
          calc
            e_generated_cmp_lin_ww.EncapsulatedBy n e_ww := hweak_read_lin
            e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
            e_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hrel_encap_lin
      . case w =>
        have hnot_ww := hww_not_rel_acq_ww.right.right
        match e_ww with
        | .cacheEvent ce_ww =>
          simp[Event.req, ] at he_req_ww
          simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite,] at hnot_ww
          contradiction
        | .directoryEvent _ => simp[Event.isCacheEvent] at he_ww_cache
    . case ncRelAcqWeakWriteNotOnCoherentState hww_not_down hww_is_rel_acq hrel_acq_no_perms =>
      simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease] at hww_is_rel_acq
      match e_ww with
      | .cacheEvent ce_ww =>
        simp [Event.req] at he_req_ww hww_is_rel_acq
        simp[CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hww_is_rel_acq
        simp[he_req_ww] at hww_is_rel_acq
      | .directoryEvent _ => simp at hww_is_rel_acq
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir _ _ =>
    cases rw
    . case r =>
      simp [Behaviour.reqHasPermsSoDirPred] at hexists_pred_get_perms
      have hpred_gets_wr_perms := hexists_pred_get_perms.choose_spec.right
      rw[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast, Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_gets_wr_perms
      have hpred_ob_wr := hpred_gets_wr_perms.isImmPred.bPred.isPred
      rw[Event.Predecessor] at hpred_ob_wr

      have hpred_encap_dir' := hpred_encap_dir.reqEncapDir
      have hpred_encap_corr_dir := hpred_gets_wr_perms.satisfyP
      rw[Event.PropOnEvent,Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_encap_corr_dir

      cases he_lin_dir_ww
      . case previousGlobalCacheGotPerms hhas_perms hcmp_lin_is_cdir_ww =>
        rw[hcmp_lin_is_cdir_ww]
        calc e_generated_cdir_ww.EncapsulatedBy n hexists_pred_get_perms.choose  := hpred_encap_dir'
          hexists_pred_get_perms.choose.OrderedBefore n e_ww := hpred_ob_wr
          e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
          e_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hrel_encap_lin
      . case getGlobalCachePerms hno_gcache_perms hcdir_translate_to_gcache =>
        have hweak_read_lin : Event.Encapsulates n hexists_pred_get_perms.choose e_generated_cmp_lin_ww :=
          CompoundProtocol.request_encapsulates_compound_linearization_event n hpred_encap_dir.isDir
          hpred_encap_dir hcdir_translate_to_gcache
        calc
          e_generated_cmp_lin_ww.EncapsulatedBy n hexists_pred_get_perms.choose := hweak_read_lin
          hexists_pred_get_perms.choose.OrderedBefore n e_ww := hpred_ob_wr
          e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
          e_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hrel_encap_lin
    . case w =>
      exfalso
      apply Event.contradiction_of_weak_write_request_has_perms_and_no_perms
      . case he_req => exact he_req_ww
      . case he_not_down => exact he_not_down_ww
      . case he_has_perms => exact he_has_perms
      . case he_no_perms => exact he_has_no_perms_ww
  . case orderAfterDir hweak_req_on_vd hsuccessor_dir _ =>
    simp[Behaviour.immBottomSuccOnVdEncapCorrDir] at hsuccessor_dir
    obtain ⟨e_succ_wb, hsucc_wb_in_b, hww_successor_wb⟩ := hsuccessor_dir
    -- have hww_successor_wb := hsuccessor_dir.choose_spec.right
    simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hww_successor_wb
    simp [Behaviour.succOnVdWithCorrespondingDir, ] at hww_successor_wb

    -- have hww := hww_successor_wb.isImmBottomSucc.noIntermediateSatP

    have hww_successor_sat_p := hww_successor_wb.satisfyP
    simp[Event.PropOnEvent] at hww_successor_sat_p
    have := hww_successor_sat_p.encapCorresponding

    /- A release has WBs to other addresses, so the successor is either the WB, or an event before. -/

    have hrel_ax := cmp.cluster1.reqAxioms.relAcqSelfBroadcast.ncReleaseWBs b init e_nc_rel hnc_rel_in_b
    obtain ⟨e_rel_wb_original, hwb_original_in_b, hrel_wb_original_spec⟩ := cmp.cluster1.reqAxioms.relAcqSelfBroadcast.ncReleaseWBs b init e_nc_rel hnc_rel_in_b
    have hrel_wb_ax := hrel_wb_original_spec e_generated_cdir_nc_rel hnc_rel_cdir_in_b
    have hrel_wb_cast := hrel_wb_ax.broadcastWB.broadcast.broadcastToEntries e_ww.addr hww_addr_ne_rel
    obtain ⟨e_rel_wb, hrel_wb_in_b, hrel_wb_cast_spec⟩ := hrel_wb_cast
    case intro.intro.intro.intro.intro.intro =>

    /- We know that `e_ww.OrderedBefore e_wb` -/
    have hww_ob_wb : e_ww.OrderedBefore n e_rel_wb := by
      calc e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
        e_nc_rel.Encapsulates n e_rel_wb := hrel_wb_cast_spec.broadcastEncapInBase.baseEncapCast

    /- We know that `e_wb.OrderedBefore e_rel_lin` -/
    have hwb_ob_rel_lin : e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hrel_wb_cast_spec.beforeDir

    /- Then do cases, either `e_wb` is the `immediate successor`-/
    have hww_is_weak_write_or_read : e_ww.isNcWeakWrite ∨ e_ww.isNcWeakRead := by
      simp[Event.isNcWeakWrite, Event.isNcWeakRead]
      match e_ww with
      | .cacheEvent cww =>
        cases rw
        . case r =>
          simp[CacheEvent.isNcWeakRead,]
          simp[Event.req] at he_req_ww
          simp[he_req_ww, ValidRequest.isNcWeakRead]
        . case w =>
          simp[CacheEvent.isNcWeakWrite,]
          simp[Event.req] at he_req_ww
          simp[he_req_ww, ValidRequest.isNcWeakWrite]
      | .directoryEvent _ =>
        simp[Event.isCacheEvent] at he_ww_cache
    have hwb_is_vdwb : e_rel_wb.isVdWriteBack := by
      have hrel_wb_spec := hrel_wb_original_spec e_generated_cdir_ww hgenerated_cdir_ww_in_b
      have hrel_wb_original_vd_wb := hrel_wb_spec.isVdWriteBack
      have hrel_wb_orig_vd_wb := hrel_wb_spec.isVdWriteBack
      simp [Event.isVdWriteBack] at hrel_wb_orig_vd_wb

      have hrel_wb_copy_of_original := hrel_wb_cast_spec.broadcastEncapInBase.castOriginal
      simp[Event.copyOfForCasting] at hrel_wb_copy_of_original
      match hwb_orig : e_rel_wb_original, hrel_wb : e_rel_wb with
      | .cacheEvent ce_wb_original, .cacheEvent ce_wb =>
        simp at hrel_wb_orig_vd_wb
        simp[] at hrel_wb_copy_of_original
        have hwb_orig_same_req := hrel_wb_copy_of_original.sameReq
        have hwb_orig_same_down := hrel_wb_copy_of_original.sameDown
        simp[Event.isVdWriteBack,]
        constructor
        . case isDown => simp[hwb_orig_same_down, hrel_wb_orig_vd_wb.isDown]
        . case isWeakWrite => simp[hwb_orig_same_req, hrel_wb_orig_vd_wb.isWeakWrite]
      | .directoryEvent ce_wb_original, .cacheEvent ce_wb
      | .directoryEvent ce_wb_original, .directoryEvent ce_wb
      | .cacheEvent ce_wb_original, .directoryEvent ce_wb =>
        simp [] at hrel_wb_copy_of_original
    have hww_same_entry_wb : e_ww.sameEntry n e_rel_wb := by
      constructor
      . case sameStruct =>
        simp[Event.sameStructure, Event.struct]
        have hrel_wb_of_original := hrel_wb_cast_spec.broadcastEncapInBase.castOriginal
        simp[Event.copyOfForCasting] at hrel_wb_of_original
        match e_rel_wb_original, e_rel_wb with
        | .cacheEvent cwb_orig, .cacheEvent cwb =>
          have hrel_wb_spec := hrel_wb_original_spec e_generated_cdir_ww hgenerated_cdir_ww_in_b
          have horig_and_wb_same_cache := hrel_wb_of_original.sameCache
          have horig_and_ww_same_cache := hrel_wb_spec.sameCid
          simp[Event.cid] at horig_and_ww_same_cache
          match e_ww, e_nc_rel with
          | .cacheEvent cww, .cacheEvent cnc_rel =>
            simp
            simp [Event.sameCid] at hww_eq_rel_cid
            simp[horig_and_wb_same_cache, horig_and_ww_same_cache, hww_eq_rel_cid]
          | .directoryEvent _ , .cacheEvent _
          | .cacheEvent _ , .directoryEvent _
          | .directoryEvent _ , .directoryEvent _ =>
            simp[Event.isCacheEvent] at he_ww_cache he_nc_rel_cache
        | .directoryEvent _, .directoryEvent _
        | .cacheEvent _, .directoryEvent _
        | .directoryEvent _, .cacheEvent _ =>
          simp at hrel_wb_of_original
      . case sameAddr => simp[Event.sameAddr, hrel_wb_cast_spec.broadcastEncapInBase.toOtherAddr]
    have hsucc_wb_before_or_eq_e_rel_wb : e_succ_wb = e_rel_wb ∨ e_succ_wb.OrderedBefore n e_rel_wb :=
      cmp.cluster1.reqAxioms.vdWriteBackAfterWeakRequestLinearizationEventEqOrOrderedBefore
      b init hweak_req_on_vd.reqOnOrAfterVd hww_successor_wb hww_ob_wb
      hww_is_weak_write_or_read hwb_is_vdwb hww_same_entry_wb
    /-
      by apply CompoundProtocol.weak_write_OrderedBefore_vd_write_back'
      . case hww_stateAfter_Vd => sorry
      . case hsucc_wb => exact hww_successor_wb
      . case hww_ob_wb => exact hww_ob_wb
      . case hww_is_weak_write_or_read =>
        simp[Event.isNcWeakWrite, Event.isNcWeakRead]
        match e_ww with
        | .cacheEvent cww =>
          cases rw
          . case r =>
            simp[CacheEvent.isNcWeakRead,]
            simp[Event.req] at he_req_ww
            simp[he_req_ww, ValidRequest.isNcWeakRead]
          . case w =>
            simp[CacheEvent.isNcWeakWrite,]
            simp[Event.req] at he_req_ww
            simp[he_req_ww, ValidRequest.isNcWeakWrite]
        | .directoryEvent _ =>
          simp[Event.isCacheEvent] at he_ww_cache
      . case hwb_is_vdwb =>
        have hrel_wb_spec := hrel_wb_original_spec e_generated_cdir_ww hgenerated_cdir_ww_in_b
        have hrel_wb_original_vd_wb := hrel_wb_spec.isVdWriteBack
        have hrel_wb_orig_vd_wb := hrel_wb_spec.isVdWriteBack
        simp [Event.isVdWriteBack] at hrel_wb_orig_vd_wb

        have hrel_wb_copy_of_original := hrel_wb_cast_spec.broadcastEncapInBase.castOriginal
        simp[Event.copyOfForCasting] at hrel_wb_copy_of_original
        match hwb_orig : e_rel_wb_original, hrel_wb : e_rel_wb with
        | .cacheEvent ce_wb_original, .cacheEvent ce_wb =>
          simp at hrel_wb_orig_vd_wb
          simp[] at hrel_wb_copy_of_original
          have hwb_orig_same_req := hrel_wb_copy_of_original.sameReq
          have hwb_orig_same_down := hrel_wb_copy_of_original.sameDown
          simp[Event.isVdWriteBack,]
          constructor
          . case isDown => simp[hwb_orig_same_down, hrel_wb_orig_vd_wb.isDown]
          . case isWeakWrite => simp[hwb_orig_same_req, hrel_wb_orig_vd_wb.isWeakWrite]
        | .directoryEvent ce_wb_original, .cacheEvent ce_wb
        | .directoryEvent ce_wb_original, .directoryEvent ce_wb
        | .cacheEvent ce_wb_original, .directoryEvent ce_wb =>
          simp [] at hrel_wb_copy_of_original
      . case hww_same_entry_wb =>
        sorry-/

    /- `e_succ_wb` has the linearization event -/
    have hsuccessor_wb_spec := hww_successor_wb.satisfyP
    simp[Event.PropOnEvent, ] at hsuccessor_wb_spec
    have hsucc_wb_encap_generated_dir := hsuccessor_wb_spec.encapCorresponding.reqEncapDir

    /- First consider where is the compound linearization event of `e_ww`, later do the same for `e_nc_rel` -/
    cases he_lin_dir_ww
    . case previousGlobalCacheGotPerms hww_has_gcache_perms hww_cmp_lin_eq_generated_cdir =>
      rw[hww_cmp_lin_eq_generated_cdir]

      /- Now determine where is the compound linearization event of `e_nc_rel` -/
      cases he_lin_dir_nc_rel
      . case previousGlobalCacheGotPerms hnc_rel_has_gcache_perms hnc_rel_cmp_lin_eq_generated_cdir =>
        rw[hnc_rel_cmp_lin_eq_generated_cdir]
        obtain ⟨e_rel_dir, hrel_dir_in_b, hrel_dir_spec⟩ := hdir_lin_nc_rel.reqLinearizeAtDir

        cases hsucc_wb_before_or_eq_e_rel_wb
        . case inl hsucc_wb_eq_rel_wb =>
          calc e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb = e_rel_wb := hsucc_wb_eq_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
        . case inr hsucc_wb_ob_rel_wb =>
          calc e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb.OrderedBefore n e_rel_wb := hsucc_wb_ob_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
      . case getGlobalCachePerms hnc_rel_no_gcache_perms hnc_rel_cluster_to_global_translation =>
        have hgenerated_cdir_nc_rel_encap_glin : Event.Encapsulates n e_generated_cdir_nc_rel e_generated_cmp_lin_nc_rel :=
          CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
          he_req_at_cdir_nc_rel hnc_rel_cluster_to_global_translation

        cases hsucc_wb_before_or_eq_e_rel_wb
        . case inl hsucc_wb_eq_rel_wb =>
          calc e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb = e_rel_wb := hsucc_wb_eq_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
            e_generated_cdir_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hgenerated_cdir_nc_rel_encap_glin
        . case inr hsucc_wb_ob_rel_wb =>
          calc e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb.OrderedBefore n e_rel_wb := hsucc_wb_ob_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
            e_generated_cdir_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hgenerated_cdir_nc_rel_encap_glin
    . case getGlobalCachePerms hww_no_gcache_perms hww_cluster_to_global_translation =>
      have hgenerated_cdir_ww_encap_glin : Event.Encapsulates n e_generated_cdir_ww e_generated_cmp_lin_ww :=
        CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
        he_req_at_cdir_ww hww_cluster_to_global_translation
      simp[Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent] at hww_cluster_to_global_translation
      simp[he_req_at_cdir_ww.isDir] at hww_cluster_to_global_translation

      cases he_lin_dir_nc_rel
      . case previousGlobalCacheGotPerms hnc_rel_has_gcache_perms hnc_rel_cmp_lin_eq_generated_cdir =>
        rw[hnc_rel_cmp_lin_eq_generated_cdir]
        obtain ⟨e_rel_dir, hrel_dir_in_b, hrel_dir_spec⟩ := hdir_lin_nc_rel.reqLinearizeAtDir

        cases hsucc_wb_before_or_eq_e_rel_wb
        . case inl hsucc_wb_eq_rel_wb =>
          calc
            e_generated_cmp_lin_ww.EncapsulatedBy n e_generated_cdir_ww := hgenerated_cdir_ww_encap_glin
            e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb = e_rel_wb := hsucc_wb_eq_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
        . case inr hsucc_wb_ob_rel_wb =>
          calc
            e_generated_cmp_lin_ww.EncapsulatedBy n e_generated_cdir_ww := hgenerated_cdir_ww_encap_glin
            e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb.OrderedBefore n e_rel_wb := hsucc_wb_ob_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
      . case getGlobalCachePerms hnc_rel_no_gcache_perms hnc_rel_cluster_to_global_translation =>
        have hgenerated_cdir_nc_rel_encap_glin : Event.Encapsulates n e_generated_cdir_nc_rel e_generated_cmp_lin_nc_rel :=
          CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
          he_req_at_cdir_nc_rel hnc_rel_cluster_to_global_translation

        cases hsucc_wb_before_or_eq_e_rel_wb
        . case inl hsucc_wb_eq_rel_wb =>
          calc
            e_generated_cmp_lin_ww.EncapsulatedBy n e_generated_cdir_ww := hgenerated_cdir_ww_encap_glin
            e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb = e_rel_wb := hsucc_wb_eq_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
            e_generated_cdir_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hgenerated_cdir_nc_rel_encap_glin
        . case inr hsucc_wb_ob_rel_wb =>
          calc
            e_generated_cmp_lin_ww.EncapsulatedBy n e_generated_cdir_ww := hgenerated_cdir_ww_encap_glin
            e_generated_cdir_ww.EncapsulatedBy n e_succ_wb := hsucc_wb_encap_generated_dir
            e_succ_wb.OrderedBefore n e_rel_wb := hsucc_wb_ob_rel_wb
            e_rel_wb.OrderedBefore n e_generated_cdir_nc_rel := hwb_ob_rel_lin
            e_generated_cdir_nc_rel.Encapsulates n e_generated_cmp_lin_nc_rel := hgenerated_cdir_nc_rel_encap_glin

    /- At the end, use `e_generated_cdir_nc_rel` to state that the `cdir` are the `e_generated_cmp_lin`. -/

lemma CompoundProtocol.acquire_and_weak_request_linearize_at_directory
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  -- {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  -- {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (he_acq_ob_e_ww : e_acq.OrderedBefore n e_ww)
  (hacq_in_b : e_acq ∈ b)
  (he_acq_cache : e_acq.isCacheEvent)
  (hacq_cdir_in_b : e_generated_cdir_acq ∈ b)
  (he_req_acq : Event.req n e_acq = ⟨{ rw := .r, coherent := false, consistency := .Acq }, property_rel⟩)
  (he_not_down_acq : ¬ e_acq.down)
  (hdir_lin_acq : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_acq e_generated_lin_acq)
  (he_has_no_perms_acq : Behaviour.reqMissingPerms n b init e_acq)
  (he_req_at_cdir_acq : Behaviour.requestLinearizesAtDirectory n b init e_acq e_generated_cdir_acq e_generated_lin_acq)
  (he_lin_dir_acq : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir_acq e_generated_cmp_lin_acq)

  (hww_addr_ne_rel : e_acq.addr ≠ e_ww.addr)
  (hww_eq_rel_cid : e_acq.cid = e_ww.cid)

  (he_ww_in_b : e_ww ∈ b)
  (he_ww_cache : e_ww.isCacheEvent)
  (he_req_ww : Event.req n e_ww = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_ww⟩)
  (he_not_down_ww : ¬ e_ww.down)
  -- (hdir_lin_ww : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_ww e_generated_lin_ww)
  (he_has_no_perms_ww : Behaviour.reqMissingPerms n b init e_ww)
  (he_req_at_cdir_ww : Behaviour.requestLinearizesAtDirectory n b init e_ww e_generated_cdir_ww e_generated_lin_ww)
  (he_lin_dir_ww : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir_ww e_generated_cmp_lin_ww)
  (hgenerated_cdir_ww_in_b : e_generated_cdir_ww ∈ b)

  : e_generated_cmp_lin_acq.OrderedBefore n e_generated_cmp_lin_ww /- hcluster_dir_lin_e₁.choose abbrev e_generated_cmp_lin -/ := by
  -- have hrel_encap_cmp_lin := CompoundProtocol.e_encap_dir_lin_encap_global_dir_lin n he_lin_dir_acq
  have hacq_encap_lin : Event.Encapsulates n e_acq e_generated_cmp_lin_acq :=
    CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n
    (by simp[ValidRequest.isAcquire,]; exact he_req_acq) he_not_down_acq hdir_lin_acq he_has_no_perms_acq
    he_req_at_cdir_acq he_lin_dir_acq

  have hww_cdir_spec := he_req_at_cdir_ww.reqCorrespondsToDir
  cases hww_cdir_spec
  . case encapDir hww_missing_perms hww_encap_corr_dir =>
    -- a Weak Write Cache Request Event (`e_ww`) do not encap a directory event. show a contradiction
    cases hww_missing_perms
    . case downgrade hww_is_down hww_evict_on_mrs => contradiction
    . case noPermsForNonNcRelAcqWeakWrite hww_not_down hww_not_rel_acq_ww hww_no_perms =>
      simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
        Event.isNcRelease, Event.isAcquire, Event.isNcWeakWrite] at hww_not_rel_acq_ww
      cases rw
      . case r =>
        cases he_lin_dir_ww
        . case previousGlobalCacheGotPerms hhas_perms hcmp_lin_is_cdir_ww =>
          rw[hcmp_lin_is_cdir_ww]
          calc
            e_generated_cmp_lin_acq.EncapsulatedBy n e_acq := hacq_encap_lin
            e_acq.OrderedBefore n e_ww := he_acq_ob_e_ww
            e_ww.Encapsulates n e_generated_cdir_ww := hww_encap_corr_dir.reqEncapDir
        . case getGlobalCachePerms hno_gcache_perms hcdir_translate_to_gcache =>
          have hweak_read_lin : Event.Encapsulates n e_ww e_generated_cmp_lin_ww :=
            CompoundProtocol.request_encapsulates_compound_linearization_event n hww_encap_corr_dir.isDir
            hww_encap_corr_dir hcdir_translate_to_gcache
          calc
            e_generated_cmp_lin_acq.EncapsulatedBy n e_acq := hacq_encap_lin
            e_acq.OrderedBefore n e_ww := he_acq_ob_e_ww
            e_ww.Encapsulates n e_generated_cmp_lin_ww := hweak_read_lin
      . case w =>
        have hnot_ww := hww_not_rel_acq_ww.right.right
        match e_ww with
        | .cacheEvent ce_ww =>
          simp[Event.req, ] at he_req_ww
          simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite,] at hnot_ww
          contradiction
        | .directoryEvent _ => simp[Event.isCacheEvent] at he_ww_cache
    . case ncRelAcqWeakWriteNotOnCoherentState hww_not_down hww_is_rel_acq hrel_acq_no_perms =>
      simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease] at hww_is_rel_acq
      match e_ww with
      | .cacheEvent ce_ww =>
        simp [Event.req] at he_req_ww hww_is_rel_acq
        simp[CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hww_is_rel_acq
        simp[he_req_ww] at hww_is_rel_acq
      | .directoryEvent _ => simp at hww_is_rel_acq
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir _ _ =>
    cases rw
    . case r =>
      simp [Behaviour.reqHasPermsSoDirPred] at hexists_pred_get_perms
      have hpred_gets_wr_perms := hexists_pred_get_perms.choose_spec.right
      rw[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast, Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_gets_wr_perms
      have hpred_ob_wr := hpred_gets_wr_perms.isImmPred.bPred.isPred
      rw[Event.Predecessor] at hpred_ob_wr

      have hacq_invals := cmp.cluster1.reqAxioms.acqInvals b e_acq e_generated_cdir_acq
      have hacq_invals_spec := hacq_invals.invalOther e_ww.addr (by simp[Eq.comm]; exact hww_addr_ne_rel)
      obtain ⟨e_inval, hinval_in_b, hacq_inval⟩ := hacq_invals_spec

      have hinval_ob_ww : e_inval.OrderedBefore n e_ww := by
        calc e_inval.EncapsulatedBy n e_acq := hacq_inval.acqEncapInval
          e_acq.OrderedBefore n e_ww := he_acq_ob_e_ww
      have hww_same_entry_wb : e_ww.sameEntry n e_inval := by
        have hacq_inval_cache := hacq_inval.cacheEvent
        constructor
        . case sameStruct =>
          simp[Event.sameStructure, Event.struct]
          match e_ww, hinv_match : e_inval with
          | .cacheEvent ce_ww, .cacheEvent ce_inval =>
            have hinval_cid := hacq_inval.sameCid
            simp[Event.cid] at hinval_cid hww_eq_rel_cid
            simp[← hww_eq_rel_cid, ← hinval_cid]
          | .directoryEvent ce_ww, .cacheEvent ce_inval
          | .cacheEvent ce_ww, .directoryEvent ce_inval
          | .directoryEvent ce_ww, .directoryEvent ce_inval =>
            simp[Event.isCacheEvent] at hacq_inval_cache he_ww_cache
        . case sameAddr =>
          simp[Event.sameAddr, hacq_inval.otherAddr]
      have hweak_read_after_acq : e_inval.OrderedBefore n hexists_pred_get_perms.choose :=
        cmp.cluster1.reqAxioms.acquireInvalBeforeReadPredecessor b init e_inval hinval_in_b hexists_pred_get_perms.choose
        hexists_pred_get_perms.choose_spec.left e_ww he_ww_in_b
        -- CompoundProtocol.acquire_invalidation_OrderedBefore_weak_read_predecessor_that_gets_perms n
        hpred_gets_wr_perms hinval_ob_ww (by simp[Event.isNcWeakRead', ValidRequest.isNcWeakRead]; simp[he_req_ww])
        hacq_inval.vcInval hww_same_entry_wb

      have hpred_encap_dir := hpred_encap_dir.reqEncapDir

      cases he_lin_dir_acq
      . case previousGlobalCacheGotPerms hhas_gcache_perms_acq hcmplin_is_cdir_acq =>
        rw[hcmplin_is_cdir_acq]
        -- have :=
        cases he_lin_dir_ww
        . case previousGlobalCacheGotPerms hhas_gcache_perms hcmplin_is_cdir =>
          rw[hcmplin_is_cdir]
          calc
            e_generated_cdir_acq.OrderedBefore n e_inval := hacq_inval.dirBeforeInval
            e_inval.OrderedBefore n hexists_pred_get_perms.choose := hweak_read_after_acq
            hexists_pred_get_perms.choose.Encapsulates n e_generated_cdir_ww := hpred_encap_dir
        . case getGlobalCachePerms hno_gperms hww_cluster_to_global_translation =>
          have hgenerated_cdir_ww_encap_glin : Event.Encapsulates n e_generated_cdir_ww e_generated_cmp_lin_ww :=
            CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
            he_req_at_cdir_ww hww_cluster_to_global_translation

          calc
            e_generated_cdir_acq.OrderedBefore n e_inval := hacq_inval.dirBeforeInval
            e_inval.OrderedBefore n hexists_pred_get_perms.choose := hweak_read_after_acq
            hexists_pred_get_perms.choose.Encapsulates n e_generated_cdir_ww := hpred_encap_dir
            e_generated_cdir_ww.Encapsulates n e_generated_cmp_lin_ww := hgenerated_cdir_ww_encap_glin
      . case getGlobalCachePerms hno_gcache_perms hcdir_translate_to_gcache =>
        have hgenerated_cdir_acq_encap_glin : Event.Encapsulates n e_generated_cdir_acq e_generated_cmp_lin_acq :=
          CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
          he_req_at_cdir_acq hcdir_translate_to_gcache
        -- have :=
        cases he_lin_dir_ww
        . case previousGlobalCacheGotPerms hhas_gcache_perms hcmplin_is_cdir =>
          rw[hcmplin_is_cdir]
          calc
            e_generated_cmp_lin_acq.EncapsulatedBy n e_generated_cdir_acq := hgenerated_cdir_acq_encap_glin
            e_generated_cdir_acq.OrderedBefore n e_inval := hacq_inval.dirBeforeInval
            e_inval.OrderedBefore n hexists_pred_get_perms.choose := hweak_read_after_acq
            hexists_pred_get_perms.choose.Encapsulates n e_generated_cdir_ww := hpred_encap_dir
        . case getGlobalCachePerms hno_gperms hww_cluster_to_global_translation =>
          have hgenerated_cdir_ww_encap_glin : Event.Encapsulates n e_generated_cdir_ww e_generated_cmp_lin_ww :=
            CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
            he_req_at_cdir_ww hww_cluster_to_global_translation

          calc
            e_generated_cmp_lin_acq.EncapsulatedBy n e_generated_cdir_acq := hgenerated_cdir_acq_encap_glin
            e_generated_cdir_acq.OrderedBefore n e_inval := hacq_inval.dirBeforeInval
            e_inval.OrderedBefore n hexists_pred_get_perms.choose := hweak_read_after_acq
            hexists_pred_get_perms.choose.Encapsulates n e_generated_cdir_ww := hpred_encap_dir
            e_generated_cdir_ww.Encapsulates n e_generated_cmp_lin_ww := hgenerated_cdir_ww_encap_glin
    . case w =>
      exfalso
      apply Event.contradiction_of_weak_write_request_has_perms_and_no_perms
      . case he_req => exact he_req_ww
      . case he_not_down => exact he_not_down_ww
      . case he_has_perms => exact he_has_perms
      . case he_no_perms => exact he_has_no_perms_ww
  . case orderAfterDir hweak_req_on_vd hsuccessor_dir _ =>
    simp[Behaviour.immBottomSuccOnVdEncapCorrDir] at hsuccessor_dir
    obtain ⟨e_succ_wb, hsucc_wb_in_b, hww_successor_wb⟩ := hsuccessor_dir
    -- have hww_successor_wb := hsuccessor_dir.choose_spec.right
    simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hww_successor_wb
    simp [Behaviour.succOnVdWithCorrespondingDir, ] at hww_successor_wb

    -- have hww := hww_successor_wb.isImmBottomSucc.noIntermediateSatP
    have hww_ob_sucessor_wb := hww_successor_wb.isImmBottomSucc.isSucc
    rw[Event.Successor, Event.Predecessor] at hww_ob_sucessor_wb

    have hww_successor_sat_p := hww_successor_wb.satisfyP
    rw[Event.PropOnEvent] at hww_successor_sat_p
    have hsucc_wb_encap_gen_cdir := hww_successor_sat_p.encapCorresponding.reqEncapDir

    /- First consider where is the compound linearization event of `e_ww`, later do the same for `e_acq` -/
    cases he_lin_dir_ww
    . case previousGlobalCacheGotPerms hww_has_gcache_perms hww_cmp_lin_eq_generated_cdir =>
      rw[hww_cmp_lin_eq_generated_cdir]

      /- Now determine where is the compound linearization event of `e_acq` -/
      calc e_generated_cmp_lin_acq.EncapsulatedBy n e_acq := hacq_encap_lin
        e_acq.OrderedBefore n e_ww := he_acq_ob_e_ww
        e_ww.OrderedBefore n e_succ_wb := hww_ob_sucessor_wb
        e_succ_wb.Encapsulates n e_generated_cdir_ww := hsucc_wb_encap_gen_cdir
    . case getGlobalCachePerms hno_gperms hww_cluster_to_global_translation =>
      have hgenerated_cdir_ww_encap_glin : Event.Encapsulates n e_generated_cdir_ww e_generated_cmp_lin_ww :=
        CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
        he_req_at_cdir_ww hww_cluster_to_global_translation

      calc e_generated_cmp_lin_acq.EncapsulatedBy n e_acq := hacq_encap_lin
        e_acq.OrderedBefore n e_ww := he_acq_ob_e_ww
        e_ww.OrderedBefore n e_succ_wb := hww_ob_sucessor_wb
        e_succ_wb.Encapsulates n e_generated_cdir_ww := hsucc_wb_encap_gen_cdir
        e_generated_cdir_ww.Encapsulates n e_generated_cmp_lin_ww := hgenerated_cdir_ww_encap_glin

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_write_or_read_and_non_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_in_b : e₁ ∈ b)
  (he₂_in_b : e₂ ∈ b)
  (hsame_cid : e₁.sameCid n e₂)
  (he₁_cache : e₁.isCacheEvent)
  (he₂_cache : e₂.isCacheEvent)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := .Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := .w, coherent := false, consistency := .Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (hweak_write_and_non_coherent_rel_cannot_linearize_at_cache :
    e₁.req.isNcRelease ∧ e₂.req.isWeak ∨ e₁.req.isWeak ∧ e₂.req.isNcRelease → (∃ e ∈ [e₁, e₂], (∃ e_cmplin ∈ b,
    Behaviour.eventCompoundLinearizes.atCache n b init e e_cmplin (cmp.linearizationOfEvent b init e)) ) → False)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
    match he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁)
      , he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂)
      with
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      apply CompoundProtocol.compound_linearization_order_of_events_ordered_before_and_linearizes_at_cache
      . case he₁_ob_e₂ => exact he₁_ob_e₂
      . case he₁_lin => exact he₁_lin
      . case he₂_lin => exact he₂_lin
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      exfalso
      apply hweak_write_and_non_coherent_rel_cannot_linearize_at_cache
      . case a =>
        apply Or.intro_right
        simp[ValidRequest.isWeak, ValidRequest.isNcRelease]
        simp[he₁_req, he₂_req]
      . case a =>
        use e₂
        simp
        exact hcluster_cache_lin_e₂
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      exfalso
      apply hweak_write_and_non_coherent_rel_cannot_linearize_at_cache
      . case a =>
        apply Or.intro_right
        simp[ValidRequest.isWeak, ValidRequest.isNcRelease]
        simp[he₁_req, he₂_req]
      . case a =>
        use e₁
        simp
        exact hcluster_cache_lin_e₁
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      case h =>
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir he₂_lin_dir
      split at he₁_lin_dir
      . case h_1 _ h _ => exfalso; exact he₁_lin_dir
      . case h_2 _ hdir_lin₁ _ =>
        split at he₂_lin_dir
        . case h_1 _ h _ => exfalso; exact he₂_lin_dir
        . case h_2 _ hdir_lin₂ _ =>
          have hreq₁_lin_at_dir := hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have hreq₂_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right

          apply CompoundProtocol.weak_write_or_read_and_nc_release_linearize_at_directory
          . case hww_addr_ne_rel => exact hdiff_addr
          . case hww_eq_rel_cid => exact hsame_cid
          . case he_ww_ob_e_nc_rel => exact he₁_ob_e₂
          . case he_ww_in_b => exact he₁_in_b
          . case he_ww_cache => exact he₁_cache
          . case he_req_ww => exact he₁_req
          . case he_not_down_ww => exact he₁_not_down
          . case he_has_no_perms_ww =>
            have he₁_no_perms := hdir_lin₁.choose_spec.right.reqHasNoPerms
            exact he₁_no_perms
          . case he_req_at_cdir_ww =>
            have he₁_lin_at_dir := hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.right
            exact he₁_lin_at_dir
          . case he_lin_dir_ww => exact he₁_lin_dir
          . case hgenerated_cdir_ww_in_b =>
            exact hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.left
          . case hnc_rel_in_b => exact he₂_in_b
          . case he_nc_rel_cache =>
            exact he₂_cache
          . case hnc_rel_cdir_in_b =>
            exact hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.left
          . case he_req_nc_rel =>
            exact he₂_req
          . case he_not_down_nc_rel =>
            exact he₂_not_down
          . case hdir_lin_nc_rel =>
            exact hdir_lin₂.choose_spec.right
          . case he_has_no_perms_nc_rel =>
            exact hdir_lin₂.choose_spec.right.reqHasNoPerms
          . case he_req_at_cdir_nc_rel =>
            exact hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          . case he_lin_dir_nc_rel =>
            exact he₂_lin_dir

lemma CompoundProtocol.contradiction_of_weak_write_encapsulating_corresponding_directory_event
  (he_cache : e.isCacheEvent)
  (he_req : Event.req n e = ⟨{ rw := .w, coherent := false, consistency := .Weak }, property_weak⟩)
  (he_not_down : ¬ e.down)
  (hreq_missing_perms : Behaviour.reqMissingPerms n b init e)
  : False := by
  cases hreq_missing_perms
  . case downgrade hww_is_down hww_on_mrs_state =>
    contradiction
  . case noPermsForNonNcRelAcqWeakWrite hnot_down hww_not_rel_acq_ww hno_perms =>
    simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
      Event.isNcRelease, Event.isAcquire, Event.isNcWeakWrite] at hww_not_rel_acq_ww
    have hnot_ww := hww_not_rel_acq_ww.right.right
    match e with
    | .cacheEvent ce =>
      simp[Event.req, ] at he_req
      simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite,] at hnot_ww
      contradiction
    | .directoryEvent _ => simp[Event.isCacheEvent] at he_cache
  . case ncRelAcqWeakWriteNotOnCoherentState hww_not_down hww_is_rel_acq hrel_acq_no_perms =>
    simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease] at hww_is_rel_acq
    match e with
    | .cacheEvent ce =>
      simp [Event.req] at he_req hww_is_rel_acq
      simp[CacheEvent.isAcquire, CacheEvent.isNcRelease,
        ValidRequest.isAcquire, ValidRequest.isNcRelease] at hww_is_rel_acq
      simp[he_req] at hww_is_rel_acq
    | .directoryEvent _ => simp at hww_is_rel_acq

lemma CompoundProtocol.CompoundLinearizationOrder_of_acquire_and_weak_request
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_in_b : e₁ ∈ b)
  (he₂_in_b : e₂ ∈ b)
  (hsame_cid : e₁.cid = e₂.cid)
  (he₁_cache : e₁.isCacheEvent)
  (he₂_cache : e₂.isCacheEvent)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_req : Event.req n e₁ = ⟨{ rw := .r, coherent := false, consistency := .Acq }, property_acq⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := rw, coherent := false, consistency := .Weak }, property_weak⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (hno_consistency_of_acq_on_sw : e₁.req.isAcquire → e₁.isPPOPair n e₂ → (∃ e_cmplin ∈ b,
    Behaviour.eventCompoundLinearizes.atCache n b init e₁ e_cmplin (cmp.linearizationOfEvent b init e₁)) → False)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
    match he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁)
      , he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂)
      with
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      apply CompoundProtocol.compound_linearization_order_of_events_ordered_before_and_linearizes_at_cache
      . case he₁_ob_e₂ => exact he₁_ob_e₂
      . case he₁_lin => exact he₁_lin
      . case he₂_lin => exact he₂_lin
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_cache := hcluster_cache_lin_e₂.choose_spec.right.e_creq_is_e_glin

      simp[he₂_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir
      split at he₁_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₁_lin_dir
      . case h_2 hcreq_lin hdir_lin hrequest_lin =>
        /- Show this is bogus; nc release on SW, and SW isn't a state in the protocol. -/
        -- [TODO] add a
        have hreq_without_perms_lin_at_dir := hdir_lin.choose_spec.right
        have hreq_lin_at_dir := hdir_lin.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        -- have he₁_encap_e₁_cmp_lin : e₁.Encapsulates n hcluster_dir_lin_e₁.choose := by
        have he₁_encap_dir_lin : Event.Encapsulates n e₁ hcluster_dir_lin_e₁.choose := CompoundProtocol.acquire_request_encapsulates_compound_linearization_event n
          (by simp[ValidRequest.isAcquire]; exact he₁_req) he₁_not_down hdir_lin.choose_spec.right
          hreq_without_perms_lin_at_dir.reqHasNoPerms hreq_lin_at_dir he₁_lin_dir
        calc hcluster_dir_lin_e₁.choose.EncapsulatedBy n e₁ := he₁_encap_dir_lin
          e₁.OrderedBefore n e₂ := he₁_ob_e₂
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_cache := hcluster_cache_lin_e₁.choose_spec.right.e_creq_is_e_glin
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[he₁_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₂_lin_dir
      split at he₂_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₂_lin_dir
      . case h_2 hcreq_lin hdir_lin_weak hrequest_lin =>

        cases rw
        . case r =>
          /- State this is bogus; Acq on SW, does not need to invalidate other lines, or provide ordering with Reads. -/
          exfalso
          apply hno_consistency_of_acq_on_sw
          . case a => simp[he₁_req, ValidRequest.isAcquire]
          . case a =>
            constructor
            . case requestPPO =>
              simp [ValidRequest.isPPOPair]
              simp[he₁_req, he₂_req]
            . case sameCache =>
              simp[Event.sameCid]
              match e₁, e₂ with
              | .cacheEvent ce₁, .cacheEvent ce₂ =>
                simp[Event.cid] at hsame_cid
                simp[hsame_cid]
              | .directoryEvent _, .cacheEvent _
              | .cacheEvent _, .directoryEvent _
              | .directoryEvent _, .directoryEvent _ =>
                simp[Event.isCacheEvent] at he₁_cache he₂_cache
            -- simp[Event.isPPOPair]
          . case a => exact hcluster_cache_lin_e₁
        . case w =>
          /- Weak Write linearizing at the directory always ordered after. -/
          /- obtain is a nice idea, but the `.choose` variables get garbled later. -/
          -- obtain ⟨e_cluster_lin, hcluster_lin_in_b, hcluster_lin_spec⟩ := hdir_lin_weak
          -- obtain ⟨e_cluster_dir, hcluster_dir_in_b, hcluster_dir_spec⟩ := hcluster_lin_spec.reqLinearizeAtDir
          have hcluster_lin_spec := hdir_lin_weak.choose_spec.right
          have hcluster_dir_spec := hcluster_lin_spec.reqLinearizeAtDir.choose_spec.right
          have := hcluster_dir_spec.dirIsLin
          cases hcluster_dir_spec.reqCorrespondsToDir
          . case encapDir hreq_missing_perms hencap_dir =>
            exfalso
            apply CompoundProtocol.contradiction_of_weak_write_encapsulating_corresponding_directory_event
            . case he_cache => exact he₂_cache
            . case he_req => exact he₂_req
            . case he_not_down => exact he₂_not_down
            . case hreq_missing_perms => exact hreq_missing_perms
          . case orderBeforeDir hww_req_has_perms hww_exists_pred_get_perms hww_encap_corr_dir _ _ =>
            exfalso
            apply Event.contradiction_of_weak_write_request_has_perms_and_no_perms
            . case he_req => exact he₂_req
            . case he_not_down => exact he₂_not_down
            . case he_has_perms => exact hww_req_has_perms
            . case he_no_perms => exact hcluster_lin_spec.reqHasNoPerms
          . case orderAfterDir hweak_req_on_vd hsucc_encap_dir _ =>
            -- obtain ⟨e_succ_wb, hsucc_in_b, hsucc_spec⟩ := hsucc_encap_dir
            have hsucc_spec := hsucc_encap_dir.choose_spec.right
            rw[Behaviour.ImmediateBottomSuccSatisfyingProp,] at hsucc_spec
            have hsucc_prop := hsucc_spec.satisfyP
            rw[Event.PropOnEvent] at hsucc_prop
            have hsucc_encap_cluster_dir := hsucc_prop.encapCorresponding.reqEncapDir

            cases he₂_lin_dir
            . case previousGlobalCacheGotPerms hww_has_gperms hcluster_lin_eq_glin =>
              rw[hcluster_lin_eq_glin]
              calc
                e₁.OrderedBefore n e₂ := he₁_ob_e₂
                e₂.OrderedBefore n hsucc_encap_dir.choose := hsucc_spec.isImmBottomSucc.isSucc
                hsucc_encap_dir.choose.Encapsulates n (hcluster_lin_spec.reqLinearizeAtDir.choose) := hsucc_encap_cluster_dir
            . case getGlobalCachePerms hno_gperms hww_cdir_encap_gcache_translation =>
              have hgenerated_cdir_ww_encap_glin : Event.Encapsulates n hcluster_lin_spec.reqLinearizeAtDir.choose hcluster_dir_lin_e₂.choose :=
                CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n
                hcluster_dir_spec hww_cdir_encap_gcache_translation
              calc
                e₁.OrderedBefore n e₂ := he₁_ob_e₂
                e₂.OrderedBefore n hsucc_encap_dir.choose := hsucc_spec.isImmBottomSucc.isSucc
                hsucc_encap_dir.choose.Encapsulates n (hcluster_lin_spec.reqLinearizeAtDir.choose) := hsucc_encap_cluster_dir
                hcluster_lin_spec.reqLinearizeAtDir.choose.Encapsulates n hcluster_dir_lin_e₂.choose := hgenerated_cdir_ww_encap_glin
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      intro hppo
      apply Or.intro_left
      case h =>
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir he₂_lin_dir
      split at he₁_lin_dir
      . case h_1 _ h _ => exfalso; exact he₁_lin_dir
      . case h_2 _ hdir_lin₁ _ =>
        split at he₂_lin_dir
        . case h_1 _ h _ => exfalso; exact he₂_lin_dir
        . case h_2 _ hdir_lin₂ _ =>
          have hreq₁_lin_at_dir := hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have hreq₂_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right

          apply CompoundProtocol.acquire_and_weak_request_linearize_at_directory
          . case he_acq_ob_e_ww => exact he₁_ob_e₂
          . case hacq_in_b => exact he₁_in_b
          . case he_acq_cache =>
            exact he₁_cache
          . case hacq_cdir_in_b =>
            exact hdir_lin₁.choose_spec.right.reqLinearizeAtDir.choose_spec.left
          . case he_req_acq =>
            exact he₁_req
          . case he_not_down_acq =>
            exact he₁_not_down
          . case hdir_lin_acq =>
            exact hdir_lin₁.choose_spec.right
          . case he_has_no_perms_acq =>
            exact hdir_lin₁.choose_spec.right.reqHasNoPerms
          . case he_req_at_cdir_acq =>
            exact hreq₁_lin_at_dir
          . case he_lin_dir_acq =>
            exact he₁_lin_dir
          . case hww_addr_ne_rel =>
            simp
            simp[ hdiff_addr]
          . case hww_eq_rel_cid =>
            -- rw[Eq.comm]
            simp[hsame_cid]
          . case he_ww_in_b => exact he₂_in_b
          . case he_ww_cache => exact he₂_cache
          . case he_req_ww => exact he₂_req
          . case he_not_down_ww => exact he₂_not_down
          . case he_has_no_perms_ww =>
            have he₂_no_perms := hdir_lin₂.choose_spec.right.reqHasNoPerms
            exact he₂_no_perms
          . case he_req_at_cdir_ww =>
            have he₂_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right
            exact he₂_lin_at_dir
          . case he_lin_dir_ww => exact he₂_lin_dir
          . case hgenerated_cdir_ww_in_b =>
            exact hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.left

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_non_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_in_b : e₁ ∈ b) (he₂_in_b : e₂ ∈ b)
  (hsame_cid : e₁.sameCid n e₂)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := false, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (hweak_write_and_non_coherent_rel_cannot_linearize_at_cache :
    e₁.req.isNcRelease ∧ e₂.req.isWeak ∨ e₁.req.isWeak ∧ e₂.req.isNcRelease → (∃ e ∈ [e₁, e₂], (∃ e_cmplin ∈ b,
    Behaviour.eventCompoundLinearizes.atCache n b init e e_cmplin (cmp.linearizationOfEvent b init e)) ) → False)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  apply CompoundProtocol.CompoundLinearizationOrder_of_weak_write_or_read_and_non_coherent_release
  . case he₁_ob_e₂ => exact he₁_ob_e₂
  . case hsame_protocol => exact hsame_protocol
  . case he₁_in_b => exact he₁_in_b
  . case he₂_in_b => exact he₂_in_b
  . case hsame_cid => exact hsame_cid
  . case he₁_cache => exact he₁_cache
  . case he₂_cache => exact he₂_cache
  . case hdiff_addr => exact hdiff_addr
  . case he₁_req => exact he₁_req
  . case he₂_req => exact he₂_req
  . case he₁_not_down => exact he₁_not_down
  . case he₂_not_down => exact he₂_not_down
  . case hweak_write_and_non_coherent_rel_cannot_linearize_at_cache => exact hweak_write_and_non_coherent_rel_cannot_linearize_at_cache

/- Coherent Release: Weak request ordered before a release -/

def Event.interfaceMatchingProtocol' (e : Event n) (cmp : CompoundProtocol n) : ProtocolInterface :=
  match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy pi => match pi with
      | .global => cmp.global.requests -- panic! "We do not consider proxy caches in the global protocol."
      | .cluster1 => cmp.cluster1.requests
      | .cluster2 => cmp.cluster2.requests
    | .cache pci => match pci with
      | .globalP _ => cmp.global.requests
      | .cluster1 _ => cmp.cluster2.requests
      | .cluster2 _ => cmp.cluster2.requests
  | .directoryEvent de => match de.pInst with
    | .global => cmp.global.requests
    | .cluster1 => cmp.cluster1.requests
    | .cluster2 => cmp.cluster2.requests

lemma CompoundProtocol.lazy_coherent_release_ordering'
  {cmp : CompoundProtocol n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁cid_eq_e₂cid : e₁.cid = e₂.cid)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := true, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (hweak_req_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_weak_req_generated_dir e_generated_weak_req_cmplin)
  (hweak_req_cluster_lin_at_dir : Behaviour.requestLinearizesAtDirectory n b init e₁ e_weak_req_generated_dir e_generated_weak_req_cluster_lin)
  (hweak_req_on_vd : Behaviour.ncWeakReqOnVd n b init e₁)
  (hsucc_encap_dir : Behaviour.immBottomSuccOnVdEncapCorrDir n b init e₁ e_weak_req_generated_dir)
  {e₃ : Event n}
  (he₃_in_b : e₃ ∈ b)
  {e₂_alt_dir : Event n}
  (e₂_alt_dir_in_b : e₂_alt_dir ∈ b)
  (he₂_alt_dir_spec : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init e₂) true e₂ e₂_alt_dir)
  {e₃_dir : Event n}
  -- (he₃_dir_in_b : e₃_dir ∈ b)
  (he₃_dir_spec : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init e₃) true e₃ e₃_dir)
  (he₂_dir_imm_pred_e₃_dir : Behaviour.ImmediateBottomPredecessor n b e₂_alt_dir e₃_dir)
  (he₂_eq_e₃_addr : Event.addr n e₂ = Event.addr n e₃)
  (he₂_dir_eq_e₃_dir_addr : Event.addr n e₂_alt_dir = Event.addr n e₃_dir)
  (he₃_dir_downgrade : ∃ e_down ∈ b, Behaviour.requestDowngradePrevOwner n b init e₃ e₃_dir e_down)
  : Event.finishesBefore n e_generated_weak_req_cmplin e₃_dir := by
  /- Use to show the e₃_down is at the previou owner e₂. -/
  obtain ⟨e₃_downgrade, he₃_down_in_b, he₃_down_spec⟩ := he₃_dir_downgrade
  have he₃_down_at_prev_owner_e₂ := he₃_down_spec.atPrevOwner

  /- Use to show that the downgrade `e₃_down` causes Vd Writebacks `e₃_wb`. -/
  have he₃_down_broadcast_spec := cmp.cluster1.reqAxioms.relAcqSelfBroadcast.downgradeWB b e₃_downgrade he₃_down_in_b (e₃.interfaceMatchingProtocol' n cmp)
  obtain ⟨e₃_wb_orig, he₃_wb_orig_in_b, he₃_wb_orig_spec⟩ := he₃_down_broadcast_spec.broadcastWBs
  have he₁_e₃_diff_addr : e₁.addr ≠ e₃_downgrade.addr := by
    simp[he₃_down_spec.sameAddrAsReq,]
    simp[← he₂_eq_e₃_addr, hdiff_addr]
  have he₃_wb_orig_spec_broadcast := he₃_wb_orig_spec.broadcastWb.broadcastWB.broadcast.broadcastToEntries e₁.addr he₁_e₃_diff_addr
  obtain ⟨e₃_wb, he₃_wb_in_b, he₃_wb_spec⟩ := he₃_wb_orig_spec_broadcast
  have he₃_wb_cast_spec := he₃_wb_spec.castOriginal
  simp[Event.copyOfForCasting] at he₃_wb_cast_spec


  have he₃_original_cache := he₃_wb_orig_spec.wbCache
  have he₃_wb_cache := he₃_wb_spec.castAtCache
  have he₃_wb_encapsulated_by_e₃_downgrade := he₃_wb_spec.baseEncapCast

  have he₃_wb_vd_wb_and_same_entry_as_e₁ : e₃_wb.isVdWriteBack ∧ e₁.sameEntry n e₃_wb := by
    cases he₃_wb_orig : e₃_wb_orig
    . case cacheEvent ce₃_wb_orig =>
      cases he₃_wb : e₃_wb
      . case cacheEvent ce₃_wb =>
        simp [he₃_wb_orig, he₃_wb] at he₃_wb_cast_spec
        apply And.intro
        . case left =>
          have hsame_req := he₃_wb_cast_spec.sameReq
          have hsame_down := he₃_wb_cast_spec.sameDown
          simp[Event.isVdWriteBack, ]
          constructor
          . case isDown =>
            rw[hsame_down]
            have he₃_wb_orig_spec_vdwb := he₃_wb_orig_spec.broadcastWb.isVdWriteBack
            simp[Event.isVdWriteBack, he₃_wb_orig] at he₃_wb_orig_spec_vdwb
            exact he₃_wb_orig_spec_vdwb.isDown
          . case isWeakWrite =>
            rw[hsame_req]
            have he₃_wb_orig_spec_vdwb := he₃_wb_orig_spec.broadcastWb.isVdWriteBack
            simp[Event.isVdWriteBack, he₃_wb_orig] at he₃_wb_orig_spec_vdwb
            exact he₃_wb_orig_spec_vdwb.isWeakWrite
        . case right =>
          have hsame_cache := he₃_wb_cast_spec.sameCache
          constructor
          . case sameStruct =>
            simp[Event.sameStructure]
            simp[Event.struct]
            cases e₁
            . case cacheEvent ce₁ =>
              simp[]
              /- [TODO]: use these two hyps to show e₃_down.cid = e₂.cid, and we know e₁.cid = e₂.cid -/
              have := he₃_wb_orig_spec.wbSameCidAsDown
              have := he₃_down_at_prev_owner_e₂
              -- have he₃_down_at_prev_owner_e₂ := he₃_down_spec.atPrevOwner
              simp[Event.downgradeAtPrevOwner] at he₃_down_at_prev_owner_e₂
              --
              simp[Behaviour.stateBefore] at he₃_down_at_prev_owner_e₂
              rw[Behaviour.upTo_immediatePredecessor_eq n he₂_dir_imm_pred_e₃_dir] at he₃_down_at_prev_owner_e₂
              rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore] at he₃_down_at_prev_owner_e₂
              simp[List.stateAfter] at he₃_down_at_prev_owner_e₂
              simp[Event.SucceedingState] at he₃_down_at_prev_owner_e₂
              cases e₂_alt_dir
              . case cacheEvent _ =>
                have he₂_dir := he₂_alt_dir_spec.isDir
                simp [Event.isDirectoryEvent] at he₂_dir
              . case directoryEvent de₂_alt_dir =>
                simp [DirectoryEvent.SucceedingState] at he₃_down_at_prev_owner_e₂
                have he₂_alt_dir_of_e₂ := he₂_alt_dir_spec.dirCorresponds
                have he₂_alt_dir_down := he₂_alt_dir_of_e₂.sameDown
                simp [Event.down] at he₂_alt_dir_down
                simp [he₂_alt_dir_down] at he₃_down_at_prev_owner_e₂
                cases e₂
                . case cacheEvent ce₂ =>
                  simp[Event.down] at he₂_not_down
                  simp [he₂_not_down] at he₃_down_at_prev_owner_e₂

                  have he₂_alt_dir_req := he₂_alt_dir_of_e₂.dirReq
                  simp [Event.req, Behaviour.reqToDirOfRequestEvent] at he₂_alt_dir_req
                  simp [Event.req] at he₂_req
                  simp [he₂_req] at he₂_alt_dir_req
                  simp[Event.reqToDirOfRequestEvent, Event.req, Event.down, he₂_not_down] at he₂_alt_dir_req
                  simp [he₂_req] at he₂_alt_dir_req

                  simp [he₂_alt_dir_req, EntryState.directory] at he₃_down_at_prev_owner_e₂
                  have he₃_down_cache := he₃_down_spec.fwdFromRequester
                  simp[Event.downgradeCorrespondingToRequest ] at he₃_down_cache
                  cases e₃_downgrade
                  . case cacheEvent ce₃_downgrade he₃_wb_orig_cid_eq_e₃_down_cid =>
                    simp at he₃_down_at_prev_owner_e₂
                    have he₃_wb_orig_same_cid_as_e₃_down := he₃_wb_orig_spec.wbSameCidAsDown
                    rw[hsame_cache]
                    simp [he₃_wb_orig, Event.cid] at he₃_wb_orig_same_cid_as_e₃_down
                    rw[he₃_wb_orig_same_cid_as_e₃_down]

                    rw[he₃_down_at_prev_owner_e₂]
                    have he₂_alt_dir_eReq := he₂_alt_dir_spec.dirCorresponds.reqEvent
                    simp[Event.isDirEventOfReqEvent] at he₂_alt_dir_eReq
                    rw[he₂_alt_dir_eReq]

                    -- e₁ e₂ same cid
                    simp[Event.cid] at he₁cid_eq_e₂cid
                    simp[he₁cid_eq_e₂cid]
                  . case directoryEvent _ =>
                    simp at he₃_down_cache
                . case directoryEvent _ =>
                  simp [Event.isCacheEvent] at he₂_cache
            . case directoryEvent _ =>
              simp[Event.isCacheEvent] at he₁_cache
          . case sameAddr =>
            simp[Event.sameAddr]
            simp [← he₃_wb, he₃_wb_spec.toOtherAddr]
      . case directoryEvent _ =>
        simp [Event.isCacheEvent, he₃_wb] at he₃_wb_cache
    . case directoryEvent _ =>
      simp [Event.isCacheEvent, he₃_wb_orig] at he₃_original_cache

  have hww_is_weak_write_or_read : e₁.isNcWeakWrite ∨ e₁.isNcWeakRead := by
    simp[Event.isNcWeakWrite, Event.isNcWeakRead]
    match e₁ with
    | .cacheEvent cww =>
      cases rw
      . case r =>
        simp[CacheEvent.isNcWeakRead,]
        simp[Event.req] at he₁_req
        simp[he₁_req, ValidRequest.isNcWeakRead]
      . case w =>
        simp[CacheEvent.isNcWeakWrite,]
        simp[Event.req] at he₁_req
        simp[he₁_req, ValidRequest.isNcWeakWrite]
    | .directoryEvent _ =>
      simp[Event.isCacheEvent] at he₁_cache
  obtain ⟨he₃_wb_vd_wb, he₃_same_entry_as_e₁⟩ := he₃_wb_vd_wb_and_same_entry_as_e₁

  have hww_ob_wb : e₁.OrderedBefore n e₃_wb := by
    simp[Behaviour.ImmediateBottomPredecessor] at he₂_dir_imm_pred_e₃_dir
    calc e₁.OrderedBefore n e₂ := he₁_ob_e₂
      e₂.Encapsulates n e₂_alt_dir := he₂_alt_dir_spec.reqEncapDir
      e₂_alt_dir.OrderedBefore n e₃_dir := he₂_dir_imm_pred_e₃_dir.isImmPred.bPred.isPred
      e₃_dir.Encapsulates n e₃_downgrade := he₃_down_spec.dirEncapDowngrade
      e₃_downgrade.Encapsulates n e₃_wb := he₃_wb_encapsulated_by_e₃_downgrade
  have hsucc_wb_before_or_eq_e_rel_wb : hsucc_encap_dir.choose = e₃_wb ∨ hsucc_encap_dir.choose.OrderedBefore n e₃_wb :=
    cmp.cluster1.reqAxioms.vdWriteBackAfterWeakRequestLinearizationEventEqOrOrderedBefore
    b init hweak_req_on_vd.reqOnOrAfterVd hsucc_encap_dir.choose_spec.right hww_ob_wb
    hww_is_weak_write_or_read he₃_wb_vd_wb he₃_same_entry_as_e₁

  have hsucc_wb_encap_dir := hsucc_encap_dir.choose_spec.right
  rw[Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_wb_encap_dir
  have hsucc_wb_encap_dir' := hsucc_wb_encap_dir.satisfyP
  rw[Event.PropOnEvent] at hsucc_wb_encap_dir'

  case intro.intro.intro.intro.intro.intro.intro =>
  cases hweak_req_lin_dir
  . case previousGlobalCacheGotPerms hweak_has_gperm hweak_cdir_eq_gen_cmp_lin =>
    rw[hweak_cdir_eq_gen_cmp_lin]

    cases hsucc_wb_before_or_eq_e_rel_wb
    . case inl hsucc_wb_eq_e₃_wb =>
      simp [Event.finishesBefore]
      have hsucc_eq_e₃_wb_end : hsucc_encap_dir.choose.oEnd = e₃_wb.oEnd := by rw[hsucc_wb_eq_e₃_wb]
      calc
        e_weak_req_generated_dir.oEnd < hsucc_encap_dir.choose.oEnd := hsucc_wb_encap_dir'.encapCorresponding.reqEncapDir.right
        hsucc_encap_dir.choose.oEnd = e₃_wb.oEnd := hsucc_eq_e₃_wb_end
        e₃_wb.oEnd < e₃_downgrade.oEnd := he₃_wb_encapsulated_by_e₃_downgrade.right
        e₃_downgrade.oEnd < e₃_dir.oEnd := he₃_down_spec.dirEncapDowngrade.right
    . case inr hsucc_wb_ob_e₃_wb =>
      calc
        e_weak_req_generated_dir.oEnd < hsucc_encap_dir.choose.oEnd := hsucc_wb_encap_dir'.encapCorresponding.reqEncapDir.right
        hsucc_encap_dir.choose.oEnd < e₃_wb.oStart := hsucc_wb_ob_e₃_wb
        e₃_wb.oStart < e₃_wb.oEnd := e₃_wb.oWellFormed
        e₃_wb.oEnd < e₃_downgrade.oEnd := he₃_wb_encapsulated_by_e₃_downgrade.right
        e₃_downgrade.oEnd < e₃_dir.oEnd := he₃_down_spec.dirEncapDowngrade.right
  . case getGlobalCachePerms hno_gperms hweak_cdir_translate_gcache =>
    have he_pred_encap_cmp_lin : hsucc_encap_dir.choose.Encapsulates n e_generated_weak_req_cmplin := by
      apply CompoundProtocol.request_encapsulates_compound_linearization_event n
      . case hgenerated_cdir_is_dir => exact hweak_req_cluster_lin_at_dir.isDir
      . case he_encap_corr_dir => exact hsucc_wb_encap_dir'.encapCorresponding
      . case hcdir_requests_gcache => exact hweak_cdir_translate_gcache

    cases hsucc_wb_before_or_eq_e_rel_wb
    . case inl hsucc_wb_eq_e₃_wb =>
      simp [Event.finishesBefore]
      have hsucc_eq_e₃_wb_end : hsucc_encap_dir.choose.oEnd = e₃_wb.oEnd := by rw[hsucc_wb_eq_e₃_wb]
      calc
        e_generated_weak_req_cmplin.oEnd < hsucc_encap_dir.choose.oEnd := he_pred_encap_cmp_lin.right
        hsucc_encap_dir.choose.oEnd = e₃_wb.oEnd := hsucc_eq_e₃_wb_end
        e₃_wb.oEnd < e₃_downgrade.oEnd := he₃_wb_encapsulated_by_e₃_downgrade.right
        e₃_downgrade.oEnd < e₃_dir.oEnd := he₃_down_spec.dirEncapDowngrade.right
    . case inr hsucc_wb_ob_e₃_wb =>
      calc
        e_generated_weak_req_cmplin.oEnd < hsucc_encap_dir.choose.oEnd := he_pred_encap_cmp_lin.right
        hsucc_encap_dir.choose.oEnd < e₃_wb.oStart := hsucc_wb_ob_e₃_wb
        e₃_wb.oStart < e₃_wb.oEnd := e₃_wb.oWellFormed
        e₃_wb.oEnd < e₃_downgrade.oEnd := he₃_wb_encapsulated_by_e₃_downgrade.right
        e₃_downgrade.oEnd < e₃_dir.oEnd := he₃_down_spec.dirEncapDowngrade.right

lemma CompoundProtocol.lazy_coherent_release_ordering
  {cmp : CompoundProtocol n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁cid_eq_e₂cid : e₁.cid = e₂.cid)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := true, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (hweak_req_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_weak_req_generated_dir e_generated_weak_req_cmplin)
  (hweak_req_cluster_lin_at_dir : Behaviour.requestLinearizesAtDirectory n b init e₁ e_weak_req_generated_dir e_generated_weak_req_cluster_lin)
  (hweak_req_on_vd : Behaviour.ncWeakReqOnVd n b init e₁)
  (hsucc_encap_dir : Behaviour.immBottomSuccOnVdEncapCorrDir n b init e₁ e_weak_req_generated_dir)
  : lazyCompoundLinearizationOrder n b init e₂ e_generated_weak_req_cmplin := by
  simp[lazyCompoundLinearizationOrder]
  intro e₃ he₃_in_b e₂_alt_dir e₂_alt_dir_in_b he₂_alt_dir_spec e₃_dir he₃_dir_in_b he₃_dir_spec
  intro he₂_dir_imm_pred_e₃_dir
  intro he₂_eq_e₃_addr he₂_dir_eq_e₃_dir_addr

  by_cases e₃_dir.req.NonCoherent
  . case pos he₃_dir_non_coherent =>
    have he₃_dir_downgrade := cmp.cluster1.reqAxioms.nonCohReqDowngrades b init e₃ he₃_in_b e₃_dir he₃_dir_in_b
    -- obtain ⟨e₃_downgrade, he₃_down_in_b, he₃_down_spec⟩ := he₃_dir_downgrade.fwdPrevOwner

    apply CompoundProtocol.lazy_coherent_release_ordering'
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁cid_eq_e₂cid => exact he₁cid_eq_e₂cid
    . case hdiff_addr => exact hdiff_addr
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
    . case hweak_req_lin_dir => exact hweak_req_lin_dir
    . case hweak_req_cluster_lin_at_dir => exact hweak_req_cluster_lin_at_dir
    . case hweak_req_on_vd => exact hweak_req_on_vd
    . case hsucc_encap_dir => exact hsucc_encap_dir
    . case he₃_in_b => exact he₃_in_b
    . case e₂_alt_dir_in_b => exact e₂_alt_dir_in_b
    . case he₂_alt_dir_spec => exact he₂_alt_dir_spec
    . case he₃_dir_spec => exact he₃_dir_spec
    . case he₂_dir_imm_pred_e₃_dir => exact he₂_dir_imm_pred_e₃_dir
    . case he₂_eq_e₃_addr => exact he₂_eq_e₃_addr
    . case he₂_dir_eq_e₃_dir_addr => exact he₂_dir_eq_e₃_dir_addr
    . case he₃_dir_downgrade => exact he₃_dir_downgrade.fwdPrevOwner

  . case neg he₃_dir_coherent =>
    have he₃_dir_downgrade := cmp.cluster1.reqAxioms.coherentWriteDowngrades b init e₃ he₃_in_b e₃_dir he₃_dir_in_b
    obtain ⟨he₃_dir_state_before_sw, e₃_downgrade, he₃_down_in_b, he₃_down_spec_with_grant⟩ := he₃_dir_downgrade.downgradeOtherCaches
    . case cWriteOnSW.mk.intro.intro =>
      obtain ⟨_,_,he₃_down_spec⟩ := he₃_down_spec_with_grant

      have he₃_req_downgrade_prev_owner : ∃ e_down ∈ b, Behaviour.requestDowngradePrevOwner n b init e₃ e₃_dir e_down := by
        use e₃_downgrade
        apply And.intro
        . case left =>
          exact he₃_down_in_b
        . case right =>
          exact he₃_down_spec.downgradePrevOwner

      apply CompoundProtocol.lazy_coherent_release_ordering'
      . case he₁_ob_e₂ => exact he₁_ob_e₂
      . case hsame_protocol => exact hsame_protocol
      . case he₁cid_eq_e₂cid => exact he₁cid_eq_e₂cid
      . case hdiff_addr => exact hdiff_addr
      . case he₁_cache => exact he₁_cache
      . case he₂_cache => exact he₂_cache
      . case he₁_req => exact he₁_req
      . case he₂_req => exact he₂_req
      . case he₁_not_down => exact he₁_not_down
      . case he₂_not_down => exact he₂_not_down
      . case hweak_req_lin_dir => exact hweak_req_lin_dir
      . case hweak_req_cluster_lin_at_dir => exact hweak_req_cluster_lin_at_dir
      . case hweak_req_on_vd => exact hweak_req_on_vd
      . case hsucc_encap_dir => exact hsucc_encap_dir
      . case he₃_in_b => exact he₃_in_b
      . case e₂_alt_dir_in_b => exact e₂_alt_dir_in_b
      . case he₂_alt_dir_spec => exact he₂_alt_dir_spec
      . case he₃_dir_spec => exact he₃_dir_spec
      . case he₂_dir_imm_pred_e₃_dir => exact he₂_dir_imm_pred_e₃_dir
      . case he₂_eq_e₃_addr => exact he₂_eq_e₃_addr
      . case he₂_dir_eq_e₃_dir_addr => exact he₂_dir_eq_e₃_dir_addr
      . case he₃_dir_downgrade => exact he₃_req_downgrade_prev_owner
    . case cWriteOnMR hfwd_to_sharers =>
      have he₃_stateBefore_mr := hfwd_to_sharers.cWriteOnMR

      simp[Behaviour.stateBefore] at he₃_stateBefore_mr
      rw[Behaviour.upTo_immediatePredecessor_eq n he₂_dir_imm_pred_e₃_dir] at he₃_stateBefore_mr
      rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore] at he₃_stateBefore_mr
      simp[List.stateAfter] at he₃_stateBefore_mr
      simp[Event.SucceedingState] at he₃_stateBefore_mr
      cases e₂_alt_dir
      . case cacheEvent _ =>
        have he₂_dir := he₂_alt_dir_spec.isDir
        simp [Event.isDirectoryEvent] at he₂_dir
      . case directoryEvent de₂_alt_dir =>
        simp [DirectoryEvent.SucceedingState] at he₃_stateBefore_mr
        have he₂_alt_dir_of_e₂ := he₂_alt_dir_spec.dirCorresponds
        have he₂_alt_dir_down := he₂_alt_dir_of_e₂.sameDown
        simp [Event.down] at he₂_alt_dir_down
        simp [he₂_alt_dir_down] at he₃_stateBefore_mr
        cases e₂
        . case cacheEvent ce₂ =>
          simp[Event.down] at he₂_not_down
          simp [he₂_not_down] at he₃_stateBefore_mr

          have he₂_alt_dir_req := he₂_alt_dir_of_e₂.dirReq
          simp [Event.req, Behaviour.reqToDirOfRequestEvent] at he₂_alt_dir_req
          simp [Event.req] at he₂_req
          simp [he₂_req] at he₂_alt_dir_req
          simp[Event.reqToDirOfRequestEvent, Event.req, Event.down, he₂_not_down] at he₂_alt_dir_req
          simp [he₂_req] at he₂_alt_dir_req

          simp [he₂_alt_dir_req, EntryState.state, DirectoryState.toState, ] at he₃_stateBefore_mr
        . case directoryEvent _ =>
          simp[Event.isCacheEvent] at he₂_cache

lemma CompoundProtocol.weak_request_to_directory_and_coherent_release_at_cache
  {cmp : CompoundProtocol n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁cid_eq_e₂cid : e₁.cid = e₂.cid)
  /-
  (he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁) =
    ClusterRequestLinearizationEvent.clusterDirLin hcluster_dir_lin_e₁)
  (he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂) =
    ClusterRequestLinearizationEvent.clusterCacheLin hcluster_cache_lin_e₂)-/
  -- (he₂_lin_cache : e_generated_c_rel_cmplin = e₂)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := true, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  -- (hcrel_lin_at_cache : Behaviour.eventCompoundLinearizes.atCache n b init e₂ e_generated_c_rel_cmplin (cmp.linearizationOfEvent b init e₂))
  (hweak_req_lin_dir : Behaviour.eventCompoundLinearizes.atDirectoryOrBeyond n cmp.shimAxioms b init e₁ e_generated_weak_req_cmplin
    (cmp.linearizationOfEvent b init e₁))
  (hweak_req_cluster_lin : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e₁ e_generated_weak_req_cluster_lin)
  (hweak_req_cluster_lin_at_dir : Behaviour.requestLinearizesAtDirectory n b init e₁ e_weak_req_generated_dir e_generated_weak_req_cluster_lin)
  (hweak_req_lin_dir : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_weak_req_generated_dir e_generated_weak_req_cmplin)
  : Event.OrderedBefore n e_generated_weak_req_cmplin e₂ ∨
  lazyCompoundLinearizationOrder n b init e₂ e_generated_weak_req_cmplin
  := by
  /- Weak Request linearizes at Directory; Coherent Release linearizes at Cache -/
  /- Start by identifying where does e₁ linearize with respect to itself? -/

  cases hweak_req_cluster_lin_at_dir.reqCorrespondsToDir
  . case encapDir hweak_req_missing_perms hweak_req_encap_dir =>
    cases rw
    . case r =>
      apply Or.intro_left
      cases hweak_req_lin_dir
      . case previousGlobalCacheGotPerms hweak_has_gperm hweak_cdir_eq_gen_cmp_lin =>
        rw[hweak_cdir_eq_gen_cmp_lin]
        calc e_weak_req_generated_dir.EncapsulatedBy n e₁ := hweak_req_encap_dir.reqEncapDir
          e₁.OrderedBefore n e₂ := he₁_ob_e₂
      . case getGlobalCachePerms hno_gperms hweak_cdir_translate_gcache =>
        have he_weak_read_encap_cmp_lin : e₁.Encapsulates n e_generated_weak_req_cmplin := by
          apply CompoundProtocol.request_encapsulates_compound_linearization_event n
          . case hgenerated_cdir_is_dir => exact hweak_req_cluster_lin_at_dir.isDir
          . case he_encap_corr_dir => exact hweak_req_encap_dir
          . case hcdir_requests_gcache => exact hweak_cdir_translate_gcache
        calc e_generated_weak_req_cmplin.EncapsulatedBy n e₁ := he_weak_read_encap_cmp_lin
          e₁.OrderedBefore n e₂ := he₁_ob_e₂
    . case w =>
      exfalso
      apply CompoundProtocol.contradiction_of_weak_write_encapsulating_corresponding_directory_event
      . case he_cache => exact he₁_cache
      . case he_req => exact he₁_req
      . case he_not_down => exact he₁_not_down
      . case hreq_missing_perms => exact hweak_req_missing_perms
  . case orderBeforeDir hweak_has_perms hexists_pred_get_perms hpred_corr_dir _ _ =>
    cases rw
    . case r =>
      apply Or.intro_left
      simp [Behaviour.reqHasPermsSoDirPred] at hexists_pred_get_perms
      have hpred_spec := hexists_pred_get_perms.choose_spec.right
      simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast, Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_spec

      cases hweak_req_lin_dir
      . case previousGlobalCacheGotPerms hweak_has_gperm hweak_cdir_eq_gen_cmp_lin =>
        rw[hweak_cdir_eq_gen_cmp_lin]
        calc e_weak_req_generated_dir.EncapsulatedBy n hexists_pred_get_perms.choose := hpred_corr_dir.reqEncapDir
          hexists_pred_get_perms.choose.OrderedBefore n e₁ := hpred_spec.isImmPred.bPred.isPred
          e₁.OrderedBefore n e₂ := he₁_ob_e₂
      . case getGlobalCachePerms hno_gperms hweak_cdir_translate_gcache =>
        have he_pred_encap_cmp_lin : hexists_pred_get_perms.choose.Encapsulates n e_generated_weak_req_cmplin := by
          apply CompoundProtocol.request_encapsulates_compound_linearization_event n
          . case hgenerated_cdir_is_dir => exact hweak_req_cluster_lin_at_dir.isDir
          . case he_encap_corr_dir => exact hpred_corr_dir
          . case hcdir_requests_gcache => exact hweak_cdir_translate_gcache
        calc e_generated_weak_req_cmplin.EncapsulatedBy n hexists_pred_get_perms.choose := he_pred_encap_cmp_lin
          hexists_pred_get_perms.choose.OrderedBefore n e₁ := hpred_spec.isImmPred.bPred.isPred
          e₁.OrderedBefore n e₂ := he₁_ob_e₂
    . case w =>
      exfalso
      apply Event.contradiction_of_weak_write_request_has_perms_and_no_perms
      . case he_req => exact he₁_req
      . case he_not_down => exact he₁_not_down
      . case he_has_perms => exact hweak_has_perms
      . case he_no_perms => exact hweak_req_cluster_lin.reqHasNoPerms
  . case orderAfterDir hweak_req_on_vd hsucc_encap_dir _ =>
    apply Or.intro_right
    case h =>
    apply CompoundProtocol.lazy_coherent_release_ordering
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁cid_eq_e₂cid => exact he₁cid_eq_e₂cid
    . case hdiff_addr => exact hdiff_addr
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
    . case hweak_req_lin_dir => exact hweak_req_lin_dir
    . case hweak_req_cluster_lin_at_dir => exact hweak_req_cluster_lin_at_dir
    . case hweak_req_on_vd => exact hweak_req_on_vd
    . case hsucc_encap_dir => exact hsucc_encap_dir

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁cid_eq_e₂cid : e₁.cid = e₂.cid)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := true, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  match he₁_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁)
    , he₂_lin : cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂)
    with
  | .clusterCacheLin hcluster_cache_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
    apply CompoundProtocol.compound_linearization_order_of_events_ordered_before_and_linearizes_at_cache
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_lin => exact he₁_lin
    . case he₂_lin => exact he₂_lin
  | .clusterDirLin hcluster_dir_lin_e₁, .clusterCacheLin hcluster_cache_lin_e₂ =>
    simp[CompoundLinearizationOrder]
    -- apply Or.intro_left
    simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

    have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
    have he₂_lin_cache := hcluster_cache_lin_e₂.choose_spec.right.e_creq_is_e_glin

    simp[he₂_lin_cache]

    rw[compoundLinearization.OfReqEncapDirAccess.eq_def] at he₁_lin_dir
    split at he₁_lin_dir
    . case h_1 _ _ => exfalso; exact he₁_lin_dir
    . case h_2 _ hdir_lin_weak _ =>
      --
      intro hppo
      apply CompoundProtocol.weak_request_to_directory_and_coherent_release_at_cache
      . case he₁_ob_e₂ => exact he₁_ob_e₂
      . case hsame_protocol => exact hsame_protocol
      . case hdiff_addr => exact hdiff_addr
      -- . case he₂_lin_cache => exact he₂_lin_cache
      . case he₁cid_eq_e₂cid => exact he₁cid_eq_e₂cid
      . case he₁_cache => exact he₁_cache
      . case he₂_cache => exact he₂_cache
      . case he₁_req => exact he₁_req
      . case he₂_req => exact he₂_req
      . case he₁_not_down => exact he₁_not_down
      . case he₂_not_down => exact he₂_not_down
      -- . case hcrel_lin_at_cache => exact hcluster_cache_lin_e₂.choose_spec.right
      . case hweak_req_lin_dir => exact hcluster_dir_lin_e₁.choose_spec.right
      . case hweak_req_cluster_lin => exact hdir_lin_weak.choose_spec.right
      . case hweak_req_cluster_lin_at_dir => exact hdir_lin_weak.choose_spec.right.reqLinearizeAtDir.choose_spec.right
      . case hweak_req_lin_dir => exact he₁_lin_dir
  | .clusterCacheLin hcluster_cache_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
    simp[CompoundLinearizationOrder]
    intro hppo
    apply Or.intro_left
    simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

    have he₁_lin_cache := hcluster_cache_lin_e₁.choose_spec.right.e_creq_is_e_glin
    have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

    simp[he₁_lin_cache]

    simp[compoundLinearization.OfReqEncapDirAccess] at he₂_lin_dir
    split at he₂_lin_dir
    . case h_1 _ _ => exfalso; exact he₂_lin_dir
    . case h_2 _ hdir_lin_rel _ =>
      /- Weak Request linearizes before Coherent Release linearizes. -/
      have he_rel_without_perms_lin_at_dir := hdir_lin_rel.choose_spec.right
      have he_rel_lin_at_dir := hdir_lin_rel.choose_spec.right.reqLinearizeAtDir.choose_spec.right
      have he_rel_encap_e_rel_cmp_lin : e₂.Encapsulates n hcluster_dir_lin_e₂.choose := by
        apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n
        . case he_req => simp[ValidRequest.isCoherent, Request.isCoherent, he₂_req]
        . case he_not_down => exact he₂_not_down
        . case hdir_lin => exact he_rel_without_perms_lin_at_dir
        . case he_has_no_perms => exact he_rel_without_perms_lin_at_dir.reqHasNoPerms
        . case he_req_at_cdir => exact he_rel_lin_at_dir
        . case he_lin_dir => exact he₂_lin_dir

      calc e₁.OrderedBefore n e₂ := he₁_ob_e₂
        e₂.Encapsulates n hcluster_dir_lin_e₂.choose := he_rel_encap_e_rel_cmp_lin
  | .clusterDirLin hcluster_dir_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
    simp[CompoundLinearizationOrder]
    -- apply Or.intro_left
    -- case h =>
    simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

    have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
    have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

    simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir he₂_lin_dir
    split at he₁_lin_dir
    . case h_1 _ h _ => exfalso; exact he₁_lin_dir
    . case h_2 _ hdir_lin₁_weak _ =>
      split at he₂_lin_dir
      . case h_1 _ h _ => exfalso; exact he₂_lin_dir
      . case h_2 _ hdir_lin₂ _ =>
        have hreq₁_lin_at_dir := hdir_lin₁_weak.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        have hreq₂_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right

        have he_rel_without_perms_lin_at_dir := hdir_lin₂.choose_spec.right
        have he_rel_lin_at_dir := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right
        have he_rel_encap_e_rel_cmp_lin : e₂.Encapsulates n hcluster_dir_lin_e₂.choose := by
          apply CompoundProtocol.coherent_request_encapsulates_compound_linearization_event n
          . case he_req => simp[ValidRequest.isCoherent, Request.isCoherent, he₂_req]
          . case he_not_down => exact he₂_not_down
          . case hdir_lin => exact he_rel_without_perms_lin_at_dir
          . case he_has_no_perms => exact he_rel_without_perms_lin_at_dir.reqHasNoPerms
          . case he_req_at_cdir => exact he_rel_lin_at_dir
          . case he_lin_dir => exact he₂_lin_dir

        have he₁_lin_before_e₂_or_lazy_cmp_lin : Event.OrderedBefore n hcluster_dir_lin_e₁.choose e₂ ∨
          lazyCompoundLinearizationOrder n b init e₂ hcluster_dir_lin_e₁.choose
          := by
          apply CompoundProtocol.weak_request_to_directory_and_coherent_release_at_cache
          . case he₁_ob_e₂ => exact he₁_ob_e₂
          . case hsame_protocol => exact hsame_protocol
          . case hdiff_addr => exact hdiff_addr
          . case he₁cid_eq_e₂cid => exact he₁cid_eq_e₂cid
          -- . case he₂_lin_cache => exact he₂_lin_cache
          . case he₁_cache => exact he₁_cache
          . case he₂_cache => exact he₂_cache
          . case he₁_req => exact he₁_req
          . case he₂_req => exact he₂_req
          . case he₁_not_down => exact he₁_not_down
          . case he₂_not_down => exact he₂_not_down
          -- . case hcrel_lin_at_cache => exact hcluster_cache_lin_e₂.choose_spec.right
          . case hweak_req_lin_dir => exact hcluster_dir_lin_e₁.choose_spec.right
          . case hweak_req_cluster_lin => exact hdir_lin₁_weak.choose_spec.right
          . case hweak_req_cluster_lin_at_dir => exact hdir_lin₁_weak.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          . case hweak_req_lin_dir => exact he₁_lin_dir

        cases he₁_lin_before_e₂_or_lazy_cmp_lin
        . case inl he₁_lin_before_e₂ =>
          intro hppo
          apply Or.intro_left
          calc hcluster_dir_lin_e₁.choose.OrderedBefore n e₂ := he₁_lin_before_e₂
            e₂.Encapsulates n hcluster_dir_lin_e₂.choose := he_rel_encap_e_rel_cmp_lin
        . case inr hlazy_cmp_lin =>
          intro hppo
          apply Or.intro_right
          exact hlazy_cmp_lin

/- Acquire: Acquire ordered before a Weak Request -/

/-- Lemma 11 (thm 1)-/
lemma CompoundProtocol.ppo_cluster_events_satisfy_CompoundLinearizationOrder
  {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
  (cmp : CompoundProtocol n) (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_in_b : e₁ ∈ b) (he₂_in_b : e₂ ∈ b)
  (hsame_cid : e₁.sameCid n e₂)
  (hsame_cid' : e₁.cid = e₂.cid)
  (hdiff_addr : e₁.addr ≠ e₂.addr)
  : e₁.OrderedBefore n e₂ → e₁.isPPOPair n e₂ → cmp.CompoundLinearizationOrder n b init e₁ e₂ := by
  intro he₁_ob_e₂ he₁_ppo_e₂_cache_ppo
  -- Work through the cases of all PPO Pairs, and show that `e₁` and `e₂` linearize in order.
  have he₁_ppo_e₂_constraint := he₁_ppo_e₂_cache_ppo.requestPPO

  match he₁_req : e₁.req, he₂_req : e₂.req with
  | ⟨⟨rw₁,true,.SC⟩,_⟩, ⟨⟨rw₂,true,.SC⟩,_⟩ => -- All SC requests are ordered
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp [ValidRequest.isCoherent, Request.isCoherent, he₁_req]
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp [ValidRequest.isCoherent, Request.isCoherent, he₂_req]
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨_,false,.Weak⟩,_⟩, ⟨⟨.w,false,.Rel⟩,_⟩ => -- Weak requests are ordered before a Non-Coherent Release
    apply CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_non_coherent_release
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁_in_b => exact he₁_in_b
    . case he₂_in_b => exact he₂_in_b
    . case hsame_cid => exact hsame_cid
    . case hdiff_addr => exact hdiff_addr
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
    . case hweak_write_and_non_coherent_rel_cannot_linearize_at_cache => exact cmp.weakWriteAndNonCoherentRelCannotLinearizeAtCache b init e₁ he₁_in_b e₂ he₂_in_b
  | ⟨⟨_,false,.Weak⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => -- Weak requests are ordered before a Coherent Release
    apply CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_coherent_release
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁cid_eq_e₂cid => exact hsame_cid'
    . case hdiff_addr => exact hdiff_addr
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.w,true,.Weak⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => -- a Coherent Weak Write is ordered before a Coherent Release
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp [ValidRequest.isCoherent, Request.isCoherent, he₁_req]
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp [ValidRequest.isCoherent, Request.isCoherent, he₂_req]
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.w,false,.Rel⟩,_⟩, ⟨⟨.r,false,.Acq⟩,_⟩ => -- a Non-Coherent Release is ordered before an Acquire
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.ncRelease
      exact he₁_req
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.acquire
      exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.w,true,.Rel⟩,_⟩, ⟨⟨.r,false,.Acq⟩,_⟩ => -- a Coherent Release is ordered before an Acquire
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp[ValidRequest.isCoherent, Request.isCoherent, he₁_req]
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.acquire
      exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,false,.Rel⟩,_⟩ => -- an Acquire is ordered before a Non-Coherent Release
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.acquire
      exact he₁_req
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.ncRelease
      exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => -- an Acquire is ordered before a Coherent Release
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.acquire
      exact he₁_req
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp[ValidRequest.isCoherent, Request.isCoherent, he₂_req]
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨_,false,.Weak⟩,_⟩ => -- an Acquire is ordered before a weak non-coherent request
    apply CompoundProtocol.CompoundLinearizationOrder_of_acquire_and_weak_request
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁_in_b => exact he₁_in_b
    . case he₂_in_b => exact he₂_in_b
    . case hsame_cid => exact hsame_cid'
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case hdiff_addr => exact hdiff_addr
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
    . case hno_consistency_of_acq_on_sw => exact cmp.noConsistencyOfAcqOnSw b init e₁ he₁_in_b e₂ he₂_in_b
  | ⟨⟨.r,false,.Acq⟩,_⟩, ⟨⟨.w,true,.Weak⟩,_⟩ => -- an Acquire is ordered before a weak non-coherent request
    apply CompoundProtocol.CompoundLinearizationOrder_of_two_events_that_encapsulate_their_cmp_linearization_event
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case he₁_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.acquire
      exact he₁_req
    . case he₂_req =>
      apply Event.ncReleaseOrAcquireOrCoherent.coherent
      simp[ValidRequest.isCoherent, Request.isCoherent, he₂_req]
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
  | (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
    =>
    simp[he₁_req, he₂_req, ValidRequest.isPPOPair] at he₁_ppo_e₂_constraint
