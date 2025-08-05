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

def CompoundProtocol.CompoundLinearizationOrder (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e₁ e₂ : Event n) -- (cmp_lin : Behaviour.clusterRequestLinearizationEvent.wrapper n)
  : Prop :=
  let e_lin₁ := cmp.compoundLinearizationEvent cmp.shimAxioms b init e₁ (cmp.linearizationOfEvent b init e₁) |>.linearizationEvent
  let e_lin₂ := cmp.compoundLinearizationEvent cmp.shimAxioms b init e₂ (cmp.linearizationOfEvent b init e₂) |>.linearizationEvent
  e_lin₁.OrderedBefore n e_lin₂
  ∨ ∀ e₃ ∈ b,
    match cmp.compoundLinearizationEvent cmp.shimAxioms b init e₃ (cmp.linearizationOfEvent b init e₃) with
    | .clusterCacheLin _ => False -- Cannot have another request `e₃` linearize with cache permissions
    | .clusterDirLin e_lin₃ =>
      e_lin₂.OrderedBefore n e_lin₃.choose → e_lin₁.lazyLinearizationOrder n e_lin₂ e_lin₃.choose

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
  . case orderBeforeDir hgreq_has_perms _ _ =>
    exfalso
    apply Event.contradiction_of_has_perms_and_no_perms
    . case he_req => exact htranslation.gReqOfCDir.matchingOp
    . case he_not_down => exact htranslation.gReqOfCDir.notDowngrade
    . case he_has_perms => exact hgreq_has_perms
    . case he_no_perms => exact hgreq_encap_corr_gdir.reqHasNoPerms
  . case orderAfterDir hweak_read_vd himm_successor =>
    have hweak_req := hweak_read_vd.weakReq
    have hgreq_req := htranslation.gReqOfCDir.matchingOp
    simp[Event.isNcWeak, Event.isNonCoherent, Event.isWeak] at hweak_req
    match e_translated_greq with
    | .cacheEvent ce =>
      simp[Event.req] at hgreq_req
      simp[hgreq_req] at hweak_req
    | .directoryEvent _ => simp[] at hweak_req

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
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir =>
    exfalso
    apply Event.contradiction_of_nc_release_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir =>
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
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir =>
    exfalso
    apply Event.contradiction_of_acquire_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir =>
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
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir =>
    exfalso
    apply Event.contradiction_of_coherent_request_has_perms_and_no_perms
    . case he_req => exact he_req
    . case he_not_down => exact he_not_down
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms
  . case orderAfterDir hweak_read hsuccessor_dir =>
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

lemma Behaviour.lllll
  (hhead_bottom : IsBottomEvent n b head)
  : (¬ImmediateBottomSuccSatisfyingProp n b e_ww head fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  → ¬ (head.isAcqNcRelCRelVdWB ∧ ((stateBefore n b (InitialSystemState.stateAt n init head) head).cache = Vd)) := by
  intro hnot hacq_rel_etc
  obtain ⟨l, hmade_on_vd⟩ := hacq_rel_etc
  apply hnot
  constructor
  . case isImmBottomSucc =>
    constructor
    . case isSucc =>
      -- carry this fwd from previous Lemmas
      sorry
    . case noIntermediateSatP =>
      simp[NoIntermediatePredecessorSatisfyingProp]
      simp[noBottomIntermediatePredecessorAtSuccSatisfyingProp]
      simp[succOnVdWithCorrespondingDir]

      intro e he_in_b he_bottom_same he_btn_sat
      have := he_btn_sat
      sorry
    . case sameEntry =>
      sorry
    . case predInB =>
      sorry
    . case succInB =>
      sorry
  . case isBottom =>
    exact hhead_bottom
  . case satisfyP =>
    simp[Event.PropOnEvent]
    constructor
    . case stateBeforeAsVd =>
      exact hmade_on_vd
    . case isRelAcqOrVdWB =>
      sorry
    . case encapCorresponding =>
      -- holds by axiom 6
      sorry

lemma Behaviour.llll
  (hall_cache : ∀ e ∈ l_tail, Event.isCacheEvent n e)
  (hall_not : ∀ e ∈ l_tail,
    ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  : (match List.stateAfter n l_tail (Sum.inl Vd) with
  | Sum.inl cache_state => cache_state
  | Sum.inr val => default) =
  Vd := by
  induction l_tail with
  | nil =>
    simp[List.stateAfter]
  | cons head l_tail' ih' =>
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    have hhead_cache := hall_cache head (by simp[])
    match hhead : head with
    | .cacheEvent ce_head =>
      -- apply ih'
      simp[CacheEvent.SucceedingState]
      have := hall_not head (by simp[hhead])
      --
      sorry
    | .directoryEvent _ =>
      simp[Event.isCacheEvent] at hhead_cache

lemma Behaviour.lll
  (e_ww : Event n)
  (hww : e_ww.isNcWeakWrite)
  (hww_not_down : ¬ e_ww.down)
  (hww_in_es_upto : e_ww ∈ l)
  (hinit_i : init_state = IEntry n)
  (hall_cache : ∀ e ∈ l, e.isCacheEvent)
  (hall_not : ∀ e ∈ l,
    ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  : EntryState.cache n (List.stateAfter n l init_state) = Vd := by
  induction l generalizing init_state with
  | nil =>
    simp[] at hww_in_es_upto
    -- sorry
  | cons head l_tail ih =>
    simp[List.stateAfter]
    -- simp
    simp at hww_in_es_upto
    cases hww_in_es_upto
    . case cons.inl hww_head =>
      --
      simp [Event.SucceedingState]
      match hhead : head with
      | .cacheEvent ce_head =>
        --
        simp[CacheEvent.SucceedingState]
        simp[hww_head, Event.down] at hww_not_down
        simp[hww_not_down]
        simp[ValidRequest.RequestState]

        simp[hww_head, Event.isNcWeakWrite, CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at hww
        simp[hww]
        simp[hinit_i]
        simp[EntryState.cache]
        -- simp[List.stateAfter]
        sorry
      | .directoryEvent _ =>
        have hhead_is_cache := hall_cache head (by simp[hhead])
        simp[Event.isCacheEvent, hhead] at hhead_is_cache
    . case cons.inr hww_tail =>
      apply ih
      . case hww_in_es_upto =>
        exact hww_tail
      . case hinit_i => sorry
      . case hall_cache => sorry
      . case hall_not =>
        intro e he_in_tail
        apply hall_not
        . case a =>
          simp[he_in_tail]

lemma Behaviour.ll
  : (stateBefore n b init_state/-(InitialSystemState.stateAt n init e_wb)-/ e_wb).cache = Vd := by
  simp[stateBefore]

  sorry

lemma Behaviour.all_predecessors_do_not_write_back_or_get_coherent_perms
  -- (hl : l = head :: l_tail)
  {l_tail : List (Event n)}
  (e_wb : Event n)
  (hww : e_ww.isNcWeakWrite)
  (hww_is_head : e_ww = head)
  /-
  (hno_tail_sat : ∀ e ∈ l_tail,
    ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)-/
  -- maybe try adding the fact that the state after all of them is Vd?
  (hno_tail_sat : ∀ e ∈ b, e.OrderedBefore n e_wb →
    ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)

  (hno_tail_sat : ∀ e ∈ b, e.OrderedBefore n e_wb →
    (stateAfter n b some_init e = VdEntry n) →
    ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  -- all predecessors to `e_wb` are in hno_tail_sat
  : ImmediateBottomSuccSatisfyingProp n b e_ww e_wb
      fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww := by
  /- because no predecessor to `e_wb` satisfies -/
  constructor
  . case isImmBottomSucc =>
    constructor
    . case isSucc =>
      simp[Event.Successor, Event.Predecessor]
      sorry
    . case noIntermediateSatP =>
      simp[NoIntermediatePredecessorSatisfyingProp]
      simp[noBottomIntermediatePredecessorAtSuccSatisfyingProp]
      sorry
    . case sameEntry =>
      sorry
    . case predInB =>
      sorry
    . case succInB =>
      sorry
  . case isBottom =>
    simp[IsBottomEvent]
    simp[IsNotEncapAtSameStruct]
    sorry
  . case satisfyP =>
    simp[Event.PropOnEvent]
    constructor
    . case stateBeforeAsVd =>
      sorry
    . case isRelAcqOrVdWB =>
      sorry
    . case encapCorresponding =>
      sorry

lemma Behaviour.weak_write_succ_wb_in_eventsUpToEvent_wb
  {cmp : CompoundProtocol n}
  {b : Behaviour n}
  {l : List (Event n)}
  (e_wb : Event n)
  (hsucc_wb : -- ∃ e_succ ∈ b.es,
  Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e_succ_wb fun x =>
    Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  (hww_ob_wb : e_ww.OrderedBefore n e_wb)
  (hww_is_weak_write : e_ww.isNcWeakWrite)
  (hwb_is_vdwb : e_wb.isVdWriteBack)
  (hww_same_entry_wb : e_ww.sameEntry n e_wb)
  (hww_in_es_upto_wb : e_ww ∈ l)
  -- (hes_not_empty : (eventsUpToEvent n b e_wb) ≠ [])
  : e_succ_wb ∈ l ∨ e_succ_wb = e_wb := by
  -- simp[eventsUpToEvent]
  -- have : l ≠ [] := by
  --   by_contra h_empty
  --   absurd hww_in_es_upto_wb
  --   simp [h_empty]
  induction l with
  | nil =>
    simp at hww_in_es_upto_wb
  | cons head l_tail ih =>
    --
    have hsucc_not_head : e_succ_wb ≠ head := by
      /- Strategy: 1. e_ww is in head, 2. all list elements are Sorted by OrderedBefore,
      3. eww.OrderedBefore e_succ_wb from "ImmediateBottomSucc".
      so e_succ_wb must be after head (because head = e_ww) -/
      sorry
    simp[hsucc_not_head]
    simp at hww_in_es_upto_wb
    cases hww_in_es_upto_wb
    . case cons.inl hww_is_head =>
      /-
      by_cases hno_tail_sat : ∀ e ∈ b, e.OrderedBefore n e_wb →
        ¬ImmediateBottomSuccSatisfyingProp n b e_ww e
          fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww
      . case pos =>
        sorry
      . case neg =>
        simp at hno_tail_sat
        sorry-/
      --
      by_cases hno_tail_sat : ∀ e ∈ l_tail, ¬(
        Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e fun x =>
        Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
      . case pos =>
        /- None of the entries in `l_tail` satisfy the Prop. so `e_wb` -/
        have hsucc_wb_not_in_tail : e_succ_wb ∉ l_tail := by
          by_contra hsucc_wb_in_l_tail
          apply hno_tail_sat
          . case a =>
            exact hsucc_wb_in_l_tail
          . case a =>
            exact hsucc_wb
        simp[hsucc_wb_not_in_tail]
        /- Hard part, so all the events in l_tail don't satsify this property.
        Now show that e_wb is the only one that satisfies this property. -/
        have hwb_is_imm_succ : ImmediateBottomSuccSatisfyingProp n b e_ww e_wb
          fun x => succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww :=
          sorry
          -- Behaviour.all_predecessors_do_not_write_back_or_get_coherent_perms n
          --   e_wb hww_is_weak_write hww_is_head sorry -- hno_tail_sat
        rw [show e_succ_wb = e_wb from
          Behaviour.immediate_bottom_successor_satisfying_p_unique
          n b e_ww e_succ_wb e_wb (fun x =>
            Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
          hsucc_wb hwb_is_imm_succ
          ]
      . case neg =>
        simp at hno_tail_sat
        obtain ⟨x, hx_in_tail, hx_succ_wb⟩ := hno_tail_sat
        apply Or.intro_left
        /- x is e_succ_wb, because "immediate Successor" is a unique relation. -/
        rw [show e_succ_wb = x from
          Behaviour.immediate_bottom_successor_satisfying_p_unique
          n b e_ww e_succ_wb x (fun x =>
            Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
          hsucc_wb hx_succ_wb
          ]
        exact hx_in_tail
    . case cons.inr hww_is_tail =>
      apply ih
      show e_ww ∈ l_tail
      exact hww_is_tail

lemma CompoundProtocol.weak_write_OrderedBefore_vd_write_back
  {b : Behaviour n}
  (hsucc_wb : -- ∃ e_succ ∈ b.es,
  Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e_succ_wb fun x =>
    Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww)
  (hww_ob_wb : e_ww.OrderedBefore n e_wb)
  (hww_is_weak_write : e_ww.isNcWeakWrite)
  (hwb_is_vdwb : e_wb.isVdWriteBack)
  (hww_same_entry_wb : e_ww.sameEntry n e_wb)
  : e_succ_wb = e_wb ∨ e_succ_wb.OrderedBefore n e_wb := by
  /- Strategy:
  1. consider eventsUpToEvent `e_wb`. reverse induction on the list -/
  -- have hsucc_wb_in_eventsUpToEvent_wb : e_succ_wb ∈ (Behaviour.eventsUpToEvent n b e_wb) ∨ e_succ_wb = e_wb := by
  --   sorry

  by_contra hnot_eq_or_ordered_before
  simp at hnot_eq_or_ordered_before
  have hsucc_wb_after_e_wb : e_wb.OrderedBefore n e_succ_wb := by
    by_contra hnot_ordered_after
    simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq] at hnot_ordered_after
    obtain ⟨hsucc_wb_ne_wb, hsucc_wb_not_ob_wb⟩ := hnot_eq_or_ordered_before
    case intro =>
    cases hnot_ordered_after
    . case inl hsucc_ob_wb =>
      sorry
    . case inr h =>
      sorry

  let es_upto_wb := Behaviour.eventsUpToEvent n b e_wb
  simp[Behaviour.eventsUpToEvent] at es_upto_wb
  induction Behaviour.eventsUpToEvent n b e_wb with
  | nil =>
    --
    sorry
  | cons h t ih =>
    sorry

-- END attempt to prove that a weak write `e_ww` linearizes before or at a VdWriteBack where `e_ww.OrderedBefore e_wb`

lemma CompoundProtocol.weak_write_and_nc_release_linearize_at_directory
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  -- {e_generated_lin : Event n} -- ∃ linearization event of e₁ (not compound linearization event)
  -- {e_generated_cdir : Event n} -- ∃ cluster Directory Event, that connects request `e₁` to the directory
  (hww_addr_ne_rel : e_ww.addr ≠ e_nc_rel.addr)
  (hww_eq_rel_cid : e_ww.sameCid n e_nc_rel)
  (he_ww_ob_e_nc_rel : e_ww.OrderedBefore n e_nc_rel)

  (he_ww_in_b : e_ww ∈ b)
  (he_ww_cache : e_ww.isCacheEvent)
  (he_req_ww : Event.req n e_ww = ⟨{ rw := .w, coherent := false, consistency := Consistency.Weak }, property_ww⟩)
  (he_not_down_ww : ¬ e_ww.down)
  (hdir_lin_ww : Behaviour.requestWithoutCoherentPermsLinearizesAtDir n b init e_ww e_generated_lin_ww)
  (he_has_no_perms_ww : Behaviour.reqMissingPerms n b init e_ww)
  (he_req_at_cdir_ww : Behaviour.requestLinearizesAtDirectory n b init e_ww e_generated_cdir_ww e_generated_lin_ww)
  (he_lin_dir_ww : clusterDirectoryLinearizationEvent n cmp.shimAxioms b init e_generated_cdir_ww e_generated_cmp_lin_ww)

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

  have hww_cdir_spec := he_req_at_cdir_ww.reqCorrespondsToDir
  cases hww_cdir_spec
  . case encapDir hww_missing_perms hww_encap_corr_dir =>
    -- a Weak Write Cache Request Event (`e_ww`) do not encap a directory event. show a contradiction
    cases hww_missing_perms
    . case downgrade hww_is_down hww_evict_on_mrs => contradiction
    . case noPermsForNonNcRelAcqWeakWrite hww_not_down hww_not_rel_acq_ww hww_no_perms =>
      simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
        Event.isNcRelease, Event.isAcquire, Event.isNcWeakWrite] at hww_not_rel_acq_ww
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
  . case orderBeforeDir he_has_perms hexists_pred_get_perms hpred_encap_dir =>
    exfalso
    apply Event.contradiction_of_weak_write_request_has_perms_and_no_perms
    . case he_req => exact he_req_ww
    . case he_not_down => exact he_not_down_ww
    . case he_has_perms => exact he_has_perms
    . case he_no_perms => exact he_has_no_perms_ww
  . case orderAfterDir hweak_read hsuccessor_dir =>
    simp[Behaviour.immBottomSuccOnVdEncapCorrDir] at hsuccessor_dir
    have hww_successor_wb := hsuccessor_dir.choose_spec.right
    simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hww_successor_wb
    simp [Behaviour.succOnVdWithCorrespondingDir, ] at hww_successor_wb

    -- have hww := hww_successor_wb.isImmBottomSucc.noIntermediateSatP

    have hww_successor_sat_p := hww_successor_wb.satisfyP
    simp[Event.PropOnEvent] at hww_successor_sat_p
    have := hww_successor_sat_p.encapCorresponding

    /- A release has WBs to other addresses, so the successor is either the WB, or an event before. -/

    have hrel_ax := cmp.cluster1.reqAxioms.relAcqSelfBroadcast.ncReleaseWBs b init e_nc_rel hnc_rel_in_b
    let hrel_wb_template := hrel_ax.choose
    have hrel_wb_ax := hrel_ax.choose_spec.right e_generated_cdir_nc_rel hnc_rel_cdir_in_b
    have hrel_wb_cast := hrel_wb_ax.broadcastWB.broadcast.broadcastToEntries e_ww.addr hww_addr_ne_rel
    have hrel_wb_cast_spec := hrel_wb_cast.choose_spec.right

    /- We know that `e_ww.OrderedBefore e_wb` -/
    have hww_ob_wb : e_ww.OrderedBefore n hrel_wb_cast.choose := by
      calc e_ww.OrderedBefore n e_nc_rel := he_ww_ob_e_nc_rel
        e_nc_rel.Encapsulates n hrel_wb_cast.choose := hrel_wb_cast_spec.broadcastEncapInBase.baseEncapCast

    /- We know that `e_wb.OrderedBefore e_rel_lin` -/
    have hwb_ob_rel_lin : hrel_wb_cast.choose.OrderedBefore n e_generated_cdir_nc_rel := hrel_wb_cast.choose_spec.right.beforeDir

    /- Then do cases, either `e_wb` is the `immediate successor`-/

    /- At the end, use `e_generated_cdir_nc_rel` to state that the `cdir` are the `e_generated_cmp_lin`. -/
    sorry

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_write_and_non_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_cache : e₁.isCacheEvent)
  (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := .w, coherent := false, consistency := .Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := .w, coherent := false, consistency := .Rel }, property_rel⟩)
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
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_dir := hcluster_dir_lin_e₁.choose_spec.right.e_glin_deeper
      have he₂_lin_cache := hcluster_cache_lin_e₂.choose_spec.right.e_creq_is_e_glin

      simp[he₂_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₁_lin_dir
      split at he₁_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₁_lin_dir
      . case h_2 hcreq_lin hdir_lin hrequest_lin =>
        /- Show this is bogus; Weak Write on SW, and SW isn't a state in the protocol. -/
        sorry
    | .clusterCacheLin hcluster_cache_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
      apply Or.intro_left
      simp[ClusterRequestLinearizationEvent.linearizationEvent, he₁_lin, he₂_lin]

      have he₁_lin_cache := hcluster_cache_lin_e₁.choose_spec.right.e_creq_is_e_glin
      have he₂_lin_dir := hcluster_dir_lin_e₂.choose_spec.right.e_glin_deeper

      simp[he₁_lin_cache]

      simp[compoundLinearization.OfReqEncapDirAccess] at he₂_lin_dir
      split at he₂_lin_dir
      . case h_1 hcreq_lin h hrequest_lin => exfalso; exact he₂_lin_dir
      . case h_2 hcreq_lin hdir_lin hrequest_lin =>
        /- Show this is bogus; Weak Write on SW, and SW isn't a state in the protocol. -/
        sorry
    | .clusterDirLin hcluster_dir_lin_e₁, .clusterDirLin hcluster_dir_lin_e₂ =>
      simp[CompoundLinearizationOrder]
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
            sorry

          have hreq_without_perms_lin_at_dir₂ := hdir_lin₂.choose_spec.right
          have hreq_lin_at_dir₂ := hdir_lin₂.choose_spec.right.reqLinearizeAtDir.choose_spec.right
          have he₂_encap_e₂_cmp_lin : e₂.Encapsulates n hcluster_dir_lin_e₂.choose := by
            sorry

          sorry

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_non_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := false, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  cases rw
  . case r =>
    apply CompoundProtocol.CompoundLinearizationOrder_of_weak_read_and_non_coherent_release
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  . case w =>
    apply CompoundProtocol.CompoundLinearizationOrder_of_weak_write_and_non_coherent_release
    . case he₁_ob_e₂ => exact he₁_ob_e₂
    . case hsame_protocol => exact hsame_protocol
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down

/- Coherent Release: Weak request ordered before a release -/

lemma CompoundProtocol.CompoundLinearizationOrder_of_weak_request_and_coherent_release
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_req : Event.req n e₁ = ⟨{ rw := rw, coherent := false, consistency := Consistency.Weak }, property_weak⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := ReadWrite.w, coherent := true, consistency := Consistency.Rel }, property_rel⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  sorry

/- Acquire: Acquire ordered before a Weak Request -/

lemma CompoundProtocol.CompoundLinearizationOrder_of_acquire_and_weak_request
  {b : Behaviour n}{init : InitialSystemState n}
  {cmp : CompoundProtocol n} {e₁ e₂ : Event n}
  {he₁_ob_e₂ : e₁.OrderedBefore n e₂}
  (he₁_cache : e₁.isCacheEvent)
  (he₂_cache : e₂.isCacheEvent)
  (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_req : Event.req n e₁ = ⟨{ rw := .r, coherent := false, consistency := .Acq }, property_acq⟩)
  (he₂_req : Event.req n e₂ = ⟨{ rw := rw, coherent := false, consistency := .Weak }, property_weak⟩)
  (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  : CompoundLinearizationOrder n cmp b init e₁ e₂ := by
  sorry

/-- Lemma 11 (thm 1)-/
lemma CompoundProtocol.ppo_cluster_events_satisfy_CompoundLinearizationOrder {b : Behaviour n} {init : InitialSystemState n}
  (cmp : CompoundProtocol n) (e₁ e₂ : Event n) (hsame_protocol : e₁.sameProtocol n e₂) (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
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
    . case he₁_cache => exact he₁_cache
    . case he₂_cache => exact he₂_cache
    . case he₁_req => exact he₁_req
    . case he₂_req => exact he₂_req
    . case he₁_not_down => exact he₁_not_down
    . case he₂_not_down => exact he₂_not_down
  | ⟨⟨_,false,.Weak⟩,_⟩, ⟨⟨.w,true,.Rel⟩,_⟩ => -- Weak requests are ordered before a Coherent Release
    sorry
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
    sorry
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
  | _, _ => -- Ordering is not required in all other cases
    -- simp at he₁_ppo_e₂_constraint
    sorry
    /-
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.w false Consistency.Rel) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ true Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.Rel) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) _), (Subtype.mk (Request.mk _ false Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.w false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Weak) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.w true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.r true Consistency.SC) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
(Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) _), (Subtype.mk (Request.mk ReadWrite.r false Consistency.Acq) (And.intro _ (And.intro _ (And.intro _ (And.intro _ _)))))
-/

  -- simp[CompoundProtocol.CompoundLinearizationOrder]
  -- sorry
