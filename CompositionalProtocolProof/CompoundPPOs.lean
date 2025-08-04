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

/-- Lemma 11 (thm 1)-/
lemma CompoundProtocol.ppo_cluster_events_satisfy_CompoundLinearizationOrder {b : Behaviour n} {init : InitialSystemState n}
  (cmp : CompoundProtocol n) (e₁ e₂ : Event n) (hsame_protocol : e₁.sameProtocol n e₂) (he₁_not_down : ¬ e₁.down) (he₂_not_down : ¬ e₂.down)
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
    sorry
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
