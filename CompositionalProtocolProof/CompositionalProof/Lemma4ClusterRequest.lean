import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourHelpers
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.ProofBasicHelperLemmas

import CompositionalProtocolProof.CompositionalProof.Lemma5GlobalRequest

variable (n : Nat)

lemma Behaviour.translated_global_request_of_cluster_directory_event_state_greater_than_directory
  (htranslation_spec : Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_greq)
  : (Event.req n e_cdir).MRS ≤ EntryState.state n
  (stateAfter n b (InitialSystemState.stateAt n init e_greq) e_greq) := by
  -- by the translation, the global cache always gets permissions.
  have hgreq_matches_cdir_req := htranslation_spec.gReqOfCDir.matchingOp
  -- simp[Event.req, ValidRequest.MRS]
  simp [stateAfter]

  rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]

  have hinit_state_cache_state : (InitialSystemState.stateAt n init e_greq).isCacheState := InitialSystemState.stateAt_event_isCacheEvent_EntryState_is_cache_state
    n htranslation_spec.gReqOfCDir.reqGlobalCache.reqAtCache
  have hstate_before_cache_state : (stateBefore n b (InitialSystemState.stateAt n init e_greq) e_greq).isCacheState :=
    Behaviour.stateBefore_cache_event_is_cache_state n htranslation_spec.gReqOfCDir.reqGlobalCache.reqAtCache hinit_state_cache_state
  match hstate_before : (stateBefore n b (InitialSystemState.stateAt n init e_greq) e_greq) with
  | Sum.inl s =>
    -- show the conclusion holds for any state
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    have hgreq_cache := htranslation_spec.gReqOfCDir.reqGlobalCache.reqAtCache
    match e_greq with
    | .cacheEvent cgreq =>
      simp
      -- Show for all Directory Requests, we do have permissions at the global cache.
      match hcdir_req : (Event.req n e_cdir) with
      | ⟨⟨.w,true,.SC⟩,_⟩
      | ⟨⟨.r,true,.SC⟩,_⟩
      | ⟨⟨.w,true,.Rel⟩,_⟩
      | ⟨⟨.w,true,.Weak⟩,_⟩
      | ⟨⟨.w,false,.Rel⟩,_⟩
      | ⟨⟨.w,false,.Weak⟩,_⟩
      | ⟨⟨.r,false,.Acq⟩,_⟩
      | ⟨⟨.r,false,.Weak⟩,_⟩
        =>
        -- unravel the SucceedingState hairball
        simp[CacheEvent.SucceedingState]
        have hcgreq_not_down : ¬ cgreq.down := by
          have := htranslation_spec.gReqOfCDir.notDowngrade
          simp[Event.down] at this; simp[this]
        simp[hcgreq_not_down]

        -- unravel the RequestState hairball
        simp[ValidRequest.RequestState]

        -- pull out the `e_greq` request
        simp[hcdir_req] at hgreq_matches_cdir_req
        simp[Event.req] at hgreq_matches_cdir_req
        simp[hgreq_matches_cdir_req]

        simp[ValidRequest.MRS]
        -- show that for any cache state `s` from `Sum.inl s`, the global cache permissions is greater or equal
        match s with
        | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .wr, false⟩ | ⟨some .r, false⟩ | ⟨none, true⟩ | ⟨none, false⟩ =>
          simp[EntryState.cache, LE.le, State.le, LT.lt, State.lt, Option.le, ReadWrite.toPerms, ReadWrite.toRWPerms, EntryState.state,
            ReadWritePermissions.le, ReadWritePermissions.lt]
    | .directoryEvent _ => simp [Event.isCacheEvent] at hgreq_cache
  | Sum.inr _ => simp[EntryState.isCacheState, hstate_before] at hstate_before_cache_state

lemma Behaviour.satisfies_compound_swmr_of_cluster_directory_with_no_global_perms_gets_global_perms
  {b : Behaviour n} (init : InitialSystemState n)
  (e_cdir : Event n) (hcdir_in_b : e_cdir ∈ b)
  (htranslation : Behaviour.existsGlobalCacheAccessOfDirEvent n b e_cdir)
  : Behaviour.dirEventStateLeGlobalCacheState n b init e_cdir := by
  simp[dirEventStateLeGlobalCacheState]

  simp[Behaviour.globalCacheStateOfDirEventState]
  simp[Behaviour.immediateFinishesBeforeAtGlobalCacheEvents]

  let htranslation_spec := htranslation.choose_spec.right
  let hgreq_in_b := htranslation.choose_spec.left

  -- The set of events at the corresponding Global Cache that finish immediately before `e_cdir` is singleton,
  -- the only element in the set is the translated `e_greq` (i.e. `Exists.choose htranslation`).
  have hgreq_imm_fin_before_cache := Behaviour.clusterToGlobal.global_cache_event_immediately_finish_before_of_cluster_directory n hcdir_in_b hgreq_in_b htranslation_spec
  rw[Behaviour.event_immediate_finish_before_greq_singleton n hgreq_in_b hgreq_imm_fin_before_cache]

  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToEntryState,]
  -- pop out the translated `e_greq` (i.e. `Exists.choose htranslation` from `.toOption`)

  have hcdir_fin_before_gdown_singleton :=
    Behaviour.immediateFinishesBeforeAtGlobalCacheEvents_is_greq_singleton n b e_cdir hgreq_imm_fin_before_cache
  have hsingleton := Set.toOption_singleton' htranslation.choose hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp

  apply Behaviour.translated_global_request_of_cluster_directory_event_state_greater_than_directory
  . case htranslation_spec => exact htranslation_spec

lemma Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap.mp {b e_cdir}
  (hno_encap : Event.clusterDirNotEncapCorrespondingGlobalCache n b e_cdir)
  {e : Event n}
  (he_in_not_encap_set : e ∈ {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCacheNotEncap n b e_pred e_cdir})
  : e ∈ {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCache n b e_pred e_cdir} := by
  simp_all --at he_in_not_encap_set
  obtain ⟨he_in_b, he_fin_before_not_encap⟩ := he_in_not_encap_set
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore => exact he_fin_before_not_encap.finishBefore.finBefore.endBefore
      . case sameAddr => exact he_fin_before_not_encap.finishBefore.finBefore.sameAddr
      . case predInB => exact he_fin_before_not_encap.finishBefore.finBefore.predInB
      . case succInB => exact he_fin_before_not_encap.finishBefore.finBefore.succInB
    . case gCacheOfCDir => exact he_fin_before_not_encap.finishBefore.gCacheOfCDir
  . case noIntermediate =>
    simp[noIntermediateFinishesBeforeOfSameEntry]
    intro e_inter hinter_in_b hinter_fin_before_btn
    /- Strategy: We know cache events are ordered, (`e` and `e_inter`) must be ordered, contradicting `hinter_fin_before_btn` -/

    have he_has_no_inter := he_fin_before_not_encap.noIntermediate
    simp[noIntermediateFinishesBeforeNotEncapOfSameEntry] at he_has_no_inter
    have hinter_not_inter_e := he_has_no_inter e_inter hinter_in_b
    apply he_has_no_inter

    . case a => exact hinter_in_b
    . case a =>
      constructor
      . case noInter => exact hinter_fin_before_btn
      . case noEncap =>
        simp[Event.clusterDirNotEncapCorrespondingGlobalCache] at hno_encap
        apply hno_encap
        . case a => exact hinter_in_b
        . case a =>
          apply Behaviour.same_struct_as_event_reqAtCorrespondingGCacheOfCDir_also_corresponds
          . case hsame_struct => exact hinter_fin_before_btn.sameCidInterPred
          . case hevent_corr => exact he_fin_before_not_encap.finishBefore.gCacheOfCDir
        . case a =>
          apply Behaviour.global_cache_event_of_same_struct_as_global_cache_event
          . case hsame_struct => exact hinter_fin_before_btn.sameCidInterPred
          . case he_global_cache =>
            apply Behaviour.global_cache_event_of_reqAtCorrespondingGCacheOfCDir_event_isGlobalCache
            . case he_corr_gcache => exact he_fin_before_not_encap.finishBefore.gCacheOfCDir

lemma Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap.mpr {b e_cdir}
  (hno_encap : Event.clusterDirNotEncapCorrespondingGlobalCache n b e_cdir)
  {e : Event n}
  (he_in_set : e ∈ {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCache n b e_pred e_cdir})
  : e ∈ {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCacheNotEncap n b e_pred e_cdir} := by
  simp_all --at he_in_not_encap_set
  obtain ⟨he_in_b, he_fin_before⟩ := he_in_set
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore => exact he_fin_before.finishBefore.finBefore.endBefore
      . case notEncap =>
        apply hno_encap
        . case a => exact he_in_b
        . case a => exact he_fin_before.finishBefore.gCacheOfCDir
        . case a =>
          apply Behaviour.global_cache_event_of_reqAtCorrespondingGCacheOfCDir_event_isGlobalCache
          . case he_corr_gcache => exact he_fin_before.finishBefore.gCacheOfCDir
      . case sameAddr => exact he_fin_before.finishBefore.finBefore.sameAddr
      . case predInB => exact he_fin_before.finishBefore.finBefore.predInB
      . case succInB => exact he_fin_before.finishBefore.finBefore.succInB
    . case gCacheOfCDir => exact he_fin_before.finishBefore.gCacheOfCDir
  . case noIntermediate =>
    simp[noIntermediateFinishesBeforeNotEncapOfSameEntry]
    intro e_inter hinter_in_b hinter_fin_before_btn
    /- Strategy: We know cache events are ordered, (`e` and `e_inter`) must be ordered, contradicting `hinter_fin_before_btn` -/

    have he_has_no_inter := he_fin_before.noIntermediate
    simp[noIntermediateFinishesBeforeOfSameEntry] at he_has_no_inter
    have hinter_not_inter_e := he_has_no_inter e_inter hinter_in_b
    apply he_has_no_inter

    . case a => exact hinter_in_b
    . case a =>
      constructor
      . case sameCidInterPred => exact hinter_fin_before_btn.noInter.sameCidInterPred
      . case sameAddr => exact hinter_fin_before_btn.noInter.sameAddr
      . case interPred => exact hinter_fin_before_btn.noInter.interPred
      . case interSucc => exact hinter_fin_before_btn.noInter.interSucc


lemma Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap
  {b : Behaviour n} {e_cdir : Event n}
  (hno_encap : Event.clusterDirNotEncapCorrespondingGlobalCache n b e_cdir)
  : {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCacheNotEncap n b e_pred e_cdir} =
  {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtGlobalCache n b e_pred e_cdir} := by
  apply Set.ext
  case h =>
  intro e
  apply Iff.intro
  . case mp =>
    apply Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap.mp
    . case hno_encap => exact hno_encap
  . case mpr =>
    apply Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap.mpr
    . case hno_encap => exact hno_encap

lemma Behaviour.global_cache_lastest_state_of_event_not_encap_eq_global_cache_lastest_state_of_event_if_no_encap
  {b : Behaviour n} (init : InitialSystemState n)
  (e_cdir : Event n) (hno_encap : Event.clusterDirNotEncapCorrespondingGlobalCache n b e_cdir)
  : EntryState.state n (globalCacheStateOfDirectoryEvent n b init e_cdir) = EntryState.state n (globalCacheStateOfDirEventState n b init e_cdir) := by
  simp [globalCacheStateOfDirectoryEvent, globalCacheStateOfDirEventState]

  -- This is true because events in both sets satisfy the same condition `p` (not encap,)
  simp[immediateFinishesBeforeAtGlobalCacheNotEncapEvents]
  simp[immediateFinishesBeforeAtGlobalCacheEvents]

  rw[Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap_eq_immediateFinishesBeforeAtGlobalCache_if_no_encap n
    hno_encap]

lemma Behaviour.satisfies_compound_swmr_of_cluster_directory_with_global_perms
  {b : Behaviour n} (init : InitialSystemState n)
  (e_cdir : Event n) (hhas_global_perms : Behaviour.clusterDirHasPermsInGlobalCache n b init e_cdir)
  (hno_encap : Event.clusterDirNotEncapCorrespondingGlobalCache n b e_cdir)
  : Behaviour.dirEventStateLeGlobalCacheState n b init e_cdir := by
  simp[dirEventStateLeGlobalCacheState]

  rw[← Behaviour.global_cache_lastest_state_of_event_not_encap_eq_global_cache_lastest_state_of_event_if_no_encap n init e_cdir hno_encap]
  simp [ clusterDirHasPermsInGlobalCache] at hhas_global_perms
  simp[hhas_global_perms]

/-- Lemma 4: A global downgrade `e_gdown` leaves it's corresponding cluster directory
in state `s` ≤ `e_gdown.MRS` -/
lemma CompoundProtocol.clusterDirectoryEvent.satisfies_compound_swmr
  (cmp : CompoundProtocol n)
  {b : Behaviour n} {e_cdir : Event n}
  (init : InitialSystemState n)
  (hcdir_in_b : e_cdir ∈ b)
  (hcdir_cluster_dir : e_cdir.isClusterDir)
  : CompoundSWMR n b init e_cdir := by
  apply CompoundSWMR.cDir
  . case cdir_satisfies_cmp_swmr =>
    simp [Behaviour.clusterDirEvent.satisfiesCompoundSWMR]
    intro haux_is_gcache
    constructor
    exact haux_is_gcache
    . case stateAfterLeGlobalCache =>
      -- simp[Behaviour.dirEventStateLeGlobalCacheState']
      /- Strategy: Show the latest event is the one corresponding to
      lower state to I (for fwd SW) or going to S (for fwd MR).-/
      /- NOTE: must know the state before this `e_gdown` satisfies Compound SWMR;
      how should I transfer the def of events before `e_creq` satisfiy Compound SWMR to `e_gdown`.
      Maybe not needed. Let's try the proof first. -/
      -- show the latest directory event `e_cdir_down` before `e_gdown` always produces state ≤ state after `e_gdown`
      have hcluster_translation_to_global_cache := cmp.shimAxioms.clusterToGlobal b init e_cdir (hcdir_cluster_dir.dirAtDir)

      -- Get the corresponding cluster to the global cache;
      -- cases hgdown_translation_to_cluster
      cases hcluster_translation_to_global_cache
      . case encapGlobalCache hno_global_perms htranslation =>
        apply Behaviour.satisfies_compound_swmr_of_cluster_directory_with_no_global_perms_gets_global_perms
        . case hcdir_in_b => exact hcdir_in_b
        . case htranslation => exact htranslation
      . case noGlobalCache hhas_global_perms hno_encap =>
        apply Behaviour.satisfies_compound_swmr_of_cluster_directory_with_global_perms
        . case hhas_global_perms => exact hhas_global_perms
        . case hno_encap => exact hno_encap

/-
/-- Lemma 4 : A Cluster Request Event leaves a protocol in Compound SWMR. -/
lemma Behaviour.cluster_request_enforces_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n)
  (cmp : CompoundProtocol n)
  (e : Event n) (he_in_b : e ∈ b)
  -- Initial or Current state just before Event `e` in Compound SWMR
  (hpred_cdir_cmp_swmr : ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.clusterDirFinishBeforeUnrelated n init e e_cdir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir)
  (hpred_gcache_cmp_swmr : ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBeforeUnrelated n init e e_gcache → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e_gcache)
  : b.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR n init e := by
  sorry
-/
