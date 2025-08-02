import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourHelpers
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.CompositionalProof.ProofBasic

variable (n : Nat)

/- Contain lemmas used in Compound SWMR and PPO proofs -/

lemma Behaviour.same_corresponding_gcache_same_struct {b : Behaviour n} {e_cdir e_gdown e : Event n}
  (he_cdir_satisfies : immediateFinishesBeforeAtClusterDirectory n b e_cdir e_gdown)
  (he_is_imm_pred : immediateFinishesBeforeAtClusterDirectory n b e e_gdown)
  : Event.struct n e = Event.struct n e_cdir := by
      have hcdir_at_gcache := he_cdir_satisfies.finishBefore.gCacheOfCDir
      have he_at_gcache := he_is_imm_pred.finishBefore.gCacheOfCDir
      simp[Event.reqAtCorrespondingGCacheOfCDir] at hcdir_at_gcache he_at_gcache
      simp[Event.protocol] at hcdir_at_gcache he_at_gcache
      simp [Event.struct]
      match he : e, hecdir : e_cdir, hegdown : e_gdown with
      | .directoryEvent de, .directoryEvent de_c, .cacheEvent ce =>
        simp
        match hde : de.pInst, hde_c : de_c.pInst with
        | .global, .global
        | .cluster1, .cluster1
        | .cluster2, .cluster2 => simp
        | .global, .cluster1
        | .global, .cluster2
        | .cluster1, .cluster2
        | .cluster2, .cluster1
        | .cluster2, .global
        | .cluster1, .global =>
          match hcid : ce.cid with
          | .proxy pi =>
            simp [hde, hde_c, Event.reqAtGlobalCacheCid, hcid] at hcdir_at_gcache he_at_gcache
          | .cache pci =>
            match pci with
            | .globalP fin2 =>
              simp_all [hde, hde_c, Event.reqAtGlobalCacheCid, hcid]
            | .cluster1 fin | .cluster2 fin =>
              simp [hde, hde_c, Event.reqAtGlobalCacheCid, hcid] at hcdir_at_gcache he_at_gcache
      | .cacheEvent ce_e, .directoryEvent de_c, .cacheEvent ce_g
      | .cacheEvent ce_e, .cacheEvent ce_c, .cacheEvent ce_g
      | .directoryEvent de_e, .cacheEvent ce_c, .cacheEvent ce_g
      | .cacheEvent ce_e, .directoryEvent de_c, .directoryEvent de_g
      | .cacheEvent ce_e, .cacheEvent ce_c, .directoryEvent de_g
      | .directoryEvent de_e, .cacheEvent ce_c, .directoryEvent de_g
      | .directoryEvent de_e, .directoryEvent de_c, .directoryEvent de_g
        =>
        all_goals simp [he, hecdir, Event.reqAtGlobalCacheCid, hegdown] at hcdir_at_gcache he_at_gcache
        all_goals try simp
        try
        match hde_e : de_e.pInst, hde_c : de_c.pInst with
        | .global, .global
        | .cluster1, .cluster1
        | .cluster2, .cluster2
        | .global, .cluster1
        | .global, .cluster2
        | .cluster1, .cluster2
        | .cluster2, .cluster1
        | .cluster2, .global
        | .cluster1, .global =>
          all_goals simp [hde_e, hde_c, Event.reqAtGlobalCacheCid] at hcdir_at_gcache he_at_gcache

/- BEGIN added for Lemma 4 -/

lemma Behaviour.event_immediate_finish_before_greq_singleton
  {b : Behaviour n} {e_cdir e_greq : Event n} (he_greq_in_b : e_greq ∈ b) (he_greq_satisfies : immediateFinishesBeforeAtGlobalCache n b e_greq e_cdir)
  : {e_gpred | e_gpred ∈ b ∧ Behaviour.immediateFinishesBeforeAtGlobalCache n b e_gpred e_cdir} = {e_greq} := by
  apply Set.ext
  intro e
  apply Iff.intro
  . case h.mp =>
    simp
    intro he_in_b he_is_imm_pred
    by_contra he_ne_greq
    have hgreq_no_inter := he_greq_satisfies.noIntermediate
    simp[Behaviour.noIntermediateFinishesBeforeOfSameEntry] at hgreq_no_inter
    have he_no_inter := he_is_imm_pred.noIntermediate
    simp[Behaviour.noIntermediateFinishesBeforeOfSameEntry] at he_no_inter

    -- start by showing `e_cdir` has no intermediate
    have he_not_inter_cdir := hgreq_no_inter e he_in_b
    apply he_not_inter_cdir
    constructor
    . case sameCidInterPred =>
      apply Behaviour.same_corresponding_cdir_same_struct
      . case he_greq_satisfies => exact he_greq_satisfies
      . case he_is_imm_pred => exact he_is_imm_pred
    . case sameAddr =>
      have hcdir_addr := he_greq_satisfies.finishBefore.finBefore.sameAddr
      have he_addr := he_is_imm_pred.finishBefore.finBefore.sameAddr
      simp[Event.sameAddr] at hcdir_addr he_addr
      simp[hcdir_addr, he_addr]
    . case interPred =>
      by_contra hcdir_not_finish_before_e
      simp[Event.finishesBefore] at hcdir_not_finish_before_e
      simp[Nat.le_iff_lt_or_eq] at hcdir_not_finish_before_e
      cases hcdir_not_finish_before_e
      . case inl he_lt_cdir_end =>
        have hcdir_not_inter_e := he_no_inter e_greq he_greq_in_b
        apply hcdir_not_inter_e
        constructor
        . case sameCidInterPred =>
          apply Eq.symm
          apply Behaviour.same_corresponding_cdir_same_struct
          . case he_greq_satisfies => exact he_greq_satisfies
          . case he_is_imm_pred => exact he_is_imm_pred
        . case sameAddr =>
          have hcdir_addr := he_greq_satisfies.finishBefore.finBefore.sameAddr
          have he_addr := he_is_imm_pred.finishBefore.finBefore.sameAddr
          simp[Event.sameAddr] at hcdir_addr he_addr
          simp[hcdir_addr, he_addr]
        . case interPred => simp[Event.finishesBefore, he_lt_cdir_end]
        . case interSucc => simp[he_greq_satisfies.finishBefore.finBefore.endBefore]
      . case inr he_eq_greq_end =>
        -- Contradiction, all directory events are ordered.
        match he : e, hgreq : e_greq with
        | .cacheEvent ce, .cacheEvent ce_greq =>
          simp[Event.oEnd] at he_eq_greq_end
          have hordered := b.orderedAtEntry.cache_ordered ce ce_greq |>.ordered
          simp[DirectoryEvent.Ordered] at hordered
          cases hordered
          . case inl hce_ob_greq =>
            apply Event.contradiction_of_cache_event_ends_eq
            . case he_eq_greq_end => exact he_eq_greq_end
            . case hce_ob_greq => exact hce_ob_greq
          . case inr hgreq_ob_de =>
            apply Event.contradiction_of_cache_event_ends_eq
            . case he_eq_greq_end =>
              apply Eq.symm
              exact he_eq_greq_end
            . case hce_ob_greq => exact hgreq_ob_de
        | .cacheEvent ce, .directoryEvent de_cdir
        | .directoryEvent de, .cacheEvent ce_cdir
        | .directoryEvent de, .directoryEvent de_greq
          =>
          have hgreq_at_gcache := he_greq_satisfies.finishBefore.gCacheOfCDir
          have he_at_gcache := he_is_imm_pred.finishBefore.gCacheOfCDir
          simp[Event.reqAtCorrespondingGCacheOfCDir] at hgreq_at_gcache he_at_gcache

          match e_cdir with
          | .directoryEvent dcdir =>
            simp[Event.protocol] at hgreq_at_gcache he_at_gcache
            match hcdir_protocol : dcdir.pInst with
            | .cluster1 | .cluster2 =>
              simp[hcdir_protocol, Event.reqAtGlobalCacheCid] at hgreq_at_gcache he_at_gcache
            | .global => simp[hcdir_protocol] at hgreq_at_gcache he_at_gcache
          | .cacheEvent _ => simp at hgreq_at_gcache he_at_gcache
    . case interSucc => exact he_is_imm_pred.finishBefore.finBefore.endBefore
  . case h.mpr =>
    simp
    intro he_eq_e_cdir
    simp[he_eq_e_cdir, he_greq_in_b]
    exact he_greq_satisfies

/- Checkpoint -/

lemma Behaviour.global_request_cache_translation_encap_corresponding_request
  {b : Behaviour n} {e_cdir e_greq : Event n}
  (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_greq)
  : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e_greq := by
  have hdir_of_corr_greq := htranslation.gReqOfCDir.gReq
  simp[Event.reqAtCorrespondingGCacheOfCDir, Event.protocol] at hdir_of_corr_greq
  exact hdir_of_corr_greq

lemma Behaviour.same_struct_as_event_reqAtCorrespondingGCacheOfCDir_also_corresponds
  (hsame_struct : Event.struct n e' = Event.struct n e)
  (hevent_corr : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e)
  : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e' := by
  have hsame_struct := hsame_struct
  have hevent_corr := hevent_corr
  simp_all[Event.reqAtCorrespondingGCacheOfCDir]
  match e_cdir with
  | .directoryEvent de_cdir =>
    simp_all[Event.protocol]
    match hcdir_protocol : de_cdir.pInst with
    | .cluster1 | .cluster2 =>
      simp_all[Event.reqAtGlobalCacheCid]
      match e, e' with
      | .cacheEvent ce, .cacheEvent ce' =>
        simp_all[Event.struct]
      | .directoryEvent ce, .cacheEvent ce'
      | .cacheEvent ce, .directoryEvent ce'
      | .directoryEvent ce, .directoryEvent ce' =>
        simp_all[Event.struct]
    | .global => simp_all[]
  | .cacheEvent _ => simp_all[]

lemma Behaviour.global_cache_event_of_same_struct_as_global_cache_event
  (hsame_struct : Event.struct n e' = Event.struct n e)
  (he_global_cache : Event.isGlobalCache n e)
  : e'.isGlobalCache := by
  constructor
  . case reqAtCache =>
    have := he_global_cache.reqAtCache
    simp_all[Event.isCacheEvent, Event.struct]
    match e, e' with
    | .cacheEvent ce, .cacheEvent ce'
    | .directoryEvent ce, .cacheEvent ce'
    | .cacheEvent ce, .directoryEvent ce'
    | .directoryEvent ce, .directoryEvent ce' => simp_all
  . case notAtGProxy =>
    have := he_global_cache.notAtGProxy
    simp_all[Event.reqAtGlobalCache, Event.struct]
    match e, e' with
    | .cacheEvent ce, .cacheEvent ce'
    | .directoryEvent ce, .cacheEvent ce'
    | .cacheEvent ce, .directoryEvent ce'
    | .directoryEvent ce, .directoryEvent ce' => simp_all
  . case reqGlobal =>
    have := he_global_cache.reqGlobal
    simp_all[Event.protocol, Event.struct]
    match e, e' with
    | .cacheEvent ce, .cacheEvent ce'
    | .directoryEvent ce, .cacheEvent ce'
    | .cacheEvent ce, .directoryEvent ce'
    | .directoryEvent ce, .directoryEvent ce' => simp_all

lemma Event.cdir_encap_inter_of_inter_encap_or_before_cache
  (he'_fin_before_e : Event.finishesBefore n e' e)
  -- (hsame_struct : Event.struct n e' = Event.struct n e)
  (he : e = Event.cacheEvent ce)
  (he' : e' = Event.cacheEvent ce')
  (hcdir_encap_e' : Event.Encapsulates n e_cdir e')
  (hce_encap_or_before_ce' : CacheEvent.encapsulatedOrBefore n ce ce')
  : Event.Encapsulates n e_cdir (Event.cacheEvent ce) := by
  cases hce_encap_or_before_ce'
  . case inl hce_encap_by_ce' =>
    simp[CacheEvent.EncapsulatedBy, CacheEvent.Encapsulates] at hce_encap_by_ce'
    simp[Encapsulates]
    apply And.intro
    . case left =>
      calc e_cdir.oStart < e'.oStart := hcdir_encap_e'.left
        _ < (Event.cacheEvent ce).oStart := (by simp [he', oStart, hce_encap_by_ce'.left])
    . case right =>
      calc (Event.cacheEvent ce).oEnd < (Event.cacheEvent ce').oEnd := by simp[oEnd, hce_encap_by_ce'.right]
        _ < e_cdir.oEnd := by simp[← he', hcdir_encap_e'.right]
  . case inr hce_ob_ce' =>
    simp [finishesBefore, he, he', oEnd] at he'_fin_before_e
    absurd he'_fin_before_e
    simp [Nat.le_iff_lt_or_eq]
    apply Or.intro_left
    . case h =>
      simp [CacheEvent.OrderedBefore] at hce_ob_ce'
      calc ce.oEnd < ce'.oStart := hce_ob_ce'
        _ < ce'.oEnd := ce'.oWellFormed

lemma Event.cdir_encap_inter_of_cache_encap_or_before_inter
  (b : Behaviour n)
  (he_fin_before_cdir : Event.finishesBefore n e e_cdir)
  (he'_not_down : ¬Event.down n e' = true)
  -- (hsame_struct : Event.struct n e' = Event.struct n e)
  -- (he'_fin_before_e : Event.finishesBefore n e_greq e_inter)
  -- (hcdir_encap_greq : Event.Encapsulates n e_cdir e_greq)
  (he : e = Event.cacheEvent ce)
  (he' : e' = Event.cacheEvent ce')
  (hcdir_encap_e' : Event.Encapsulates n e_cdir e')
  (hce'_encap_or_before_ce : CacheEvent.encapsulatedOrBefore n ce' ce)
  : Event.Encapsulates n e_cdir (Event.cacheEvent ce) := by
  cases hce'_encap_or_before_ce
  . case inl hce'_encap_by_ce =>
    simp[CacheEvent.EncapsulatedBy,] at hce'_encap_by_ce
    have hce'_is_downgrade := b.orderedAtEntry.cache_encap_rule ce ce' hce'_encap_by_ce
    absurd hce'_is_downgrade
    simp[he', down] at he'_not_down
    simp [he'_not_down]
  . case inr hce'_ob_ce =>
    simp[Encapsulates]
    apply And.intro
    . case left =>
      simp [CacheEvent.OrderedBefore, ] at hce'_ob_ce
      calc e_cdir.oStart < e'.oStart := hcdir_encap_e'.left
        _ < e'.oEnd := e'.oWellFormed
        _ < (Event.cacheEvent ce).oStart := (by simp [he', oEnd, oStart, hce'_ob_ce])
    . case right =>
      simp[finishesBefore] at he_fin_before_cdir
      calc (Event.cacheEvent ce).oEnd < e_cdir.oEnd := by simp[← he, he_fin_before_cdir]

lemma Behaviour.encapsulates_of_same_struct
  (b : Behaviour n)
  (he'_not_down : ¬Event.down n e' = true)
  (he_fin_before_cdir : Event.finishesBefore n e e_cdir)
  (he'_fin_before_e : Event.finishesBefore n e' e)
  (hsame_struct : Event.struct n e' = Event.struct n e)
  (hcdir_encap_e' : Event.Encapsulates n e_cdir e')
  (he_global_cache : Event.isGlobalCache n e)
  (he'_global_cache : Event.isGlobalCache n e')
  : Event.Encapsulates n e_cdir e := by
  have he_cache := he_global_cache.reqAtCache
  have he'_cache := he'_global_cache.reqAtCache
  match he : e, he' : e' with
  | .cacheEvent ce, .cacheEvent ce' =>
    have hordered := b.orderedAtEntry.cache_ordered ce ce' |>.ordered
    cases hordered
    . case inl hce_encap_or_before_ce' =>
      apply Event.cdir_encap_inter_of_inter_encap_or_before_cache
      . case he'_fin_before_e => exact he'_fin_before_e
      . case he => rfl
      . case he' => rfl
      . case hcdir_encap_e' => exact hcdir_encap_e'
      . case hce_encap_or_before_ce' => exact hce_encap_or_before_ce'
    . case inr hce'_encap_or_before_ce =>
      apply Event.cdir_encap_inter_of_cache_encap_or_before_inter
      . case b => exact b
      . case he_fin_before_cdir => exact he_fin_before_cdir
      . case he'_not_down => exact he'_not_down
      . case he => rfl
      . case he' => rfl
      . case hcdir_encap_e' => exact hcdir_encap_e'
      . case hce'_encap_or_before_ce => exact hce'_encap_or_before_ce
  | .directoryEvent ce, .cacheEvent ce'
  | .cacheEvent ce, .directoryEvent ce'
  | .directoryEvent ce, .directoryEvent ce' =>
    simp_all[Event.isCacheEvent]

lemma Behaviour.contradiction_of_intermediate_finishes_before_event_and_translation_encaps_one_global_cache_event
  (e_inter : Event n)
  (hinter_in_b : e_inter ∈ b)
  (hinter_imm_fin_btn : Event.intermediateFinishesBeforeOfSameEntry n e_inter e_greq e_cdir)
  (hcdir_encap_greq : Event.Encapsulates n e_cdir e_greq)
  (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_greq)
  : False := by
  have hinter_corr_cdir : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e_inter := by
    apply Behaviour.same_struct_as_event_reqAtCorrespondingGCacheOfCDir_also_corresponds
    . case hsame_struct => exact hinter_imm_fin_btn.sameCidInterPred
    . case hevent_corr => exact htranslation.gReqOfCDir.gReq
  have hinter_is_global_cache : Event.isGlobalCache n e_inter := by
    apply Behaviour.global_cache_event_of_same_struct_as_global_cache_event
    . case hsame_struct => exact hinter_imm_fin_btn.sameCidInterPred
    . case he_global_cache => exact htranslation.gReqOfCDir.reqGlobalCache
  have hcdir_encap_inter : Event.Encapsulates n e_cdir e_inter := by
    apply Behaviour.encapsulates_of_same_struct
    . case b => exact b
    . case he'_not_down => exact htranslation.gReqOfCDir.notDowngrade
    . case he_fin_before_cdir => exact hinter_imm_fin_btn.interSucc
    . case he'_fin_before_e => exact hinter_imm_fin_btn.interPred
    . case hsame_struct => simp[Eq.symm, hinter_imm_fin_btn.sameCidInterPred]
    . case hcdir_encap_e' => exact hcdir_encap_greq
    . case he_global_cache => exact hinter_is_global_cache
    . case he'_global_cache => exact htranslation.gReqOfCDir.reqGlobalCache
  have hinter_eq_greq := htranslation.onlyGlobalReq e_inter (by simp[hinter_in_b])
    hinter_corr_cdir hinter_is_global_cache hcdir_encap_inter

  absurd hinter_imm_fin_btn.interPred
  simp[Event.finishesBefore]
  simp[Nat.le_iff_lt_or_eq]
  apply Or.intro_right
  -- rw [show e_inter = e_greq from (htranslation.onlyGlobalReq e_inter sorry sorry sorry sorry)]
  rw[hinter_eq_greq]

lemma Behaviour.clusterToGlobal.global_req_noIntermediateFinishesBeforeOfSameEntry_from_cluster_dir_translation
  {b : Behaviour n} {e_cdir e_greq : Event n}
  (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_greq)
  : noIntermediateFinishesBeforeOfSameEntry n b e_greq e_cdir := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  intro e_inter hinter_in_b hinter_imm_fin_btn
  apply Behaviour.contradiction_of_intermediate_finishes_before_event_and_translation_encaps_one_global_cache_event
  . case hinter_in_b => exact hinter_in_b
  . case hinter_imm_fin_btn => exact hinter_imm_fin_btn
  . case hcdir_encap_greq => exact htranslation.encapGlobalCache
  . case htranslation => exact htranslation

lemma Behaviour.clusterToGlobal.global_cache_event_immediately_finish_before_of_cluster_directory
  {b : Behaviour n} {e_cdir e_greq : Event n}
  (hcdir_in_b : e_cdir ∈ b) (hgreq_in_b : e_greq ∈ b)
  (htranslation : Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_greq)
  : immediateFinishesBeforeAtGlobalCache n b e_greq e_cdir := by
  -- have := htranslation.gReqOfCDir.notDowngrade
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore => simp[Event.finishesBefore, htranslation.encapGlobalCache.right]
      . case sameAddr => simp[Event.sameAddr, htranslation.gReqOfCDir.sameAddr]
      . case predInB => exact hgreq_in_b
      . case succInB => exact hcdir_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_request_cache_translation_encap_corresponding_request
      . case htranslation => exact htranslation
  . case noIntermediate =>
    apply Behaviour.clusterToGlobal.global_req_noIntermediateFinishesBeforeOfSameEntry_from_cluster_dir_translation
    . case htranslation => exact htranslation

/- END added for Lemma 4 -/

lemma Behaviour.event_immediate_finish_before_gdown_singleton
  {b : Behaviour n} {e_cdir e_gdown : Event n} (he_cdir_in_b : e_cdir ∈ b) (he_cdir_satisfies : immediateFinishesBeforeAtClusterDirectory n b e_cdir e_gdown)
  : {e_pred | e_pred ∈ b ∧ Behaviour.immediateFinishesBeforeAtClusterDirectory n b e_pred e_gdown} = {e_cdir} := by
  apply Set.ext
  intro e
  apply Iff.intro
  . case h.mp =>
    simp
    intro he_in_b he_is_imm_pred
    by_contra he_ne_e_cdir
    have hcdir_no_inter := he_cdir_satisfies.noIntermediate
    simp[Behaviour.noIntermediateFinishesBeforeOfSameEntry] at hcdir_no_inter
    have he_no_inter := he_is_imm_pred.noIntermediate
    simp[Behaviour.noIntermediateFinishesBeforeOfSameEntry] at he_no_inter

    -- start by showing `e_cdir` has no intermediate
    have he_not_inter_cdir := hcdir_no_inter e he_in_b
    apply he_not_inter_cdir
    constructor
    . case sameCidInterPred =>
      apply Behaviour.same_corresponding_gcache_same_struct
      . case he_cdir_satisfies => exact he_cdir_satisfies
      . case he_is_imm_pred => exact he_is_imm_pred
    . case sameAddr =>
      have hcdir_addr := he_cdir_satisfies.finishBefore.finBefore.sameAddr
      have he_addr := he_is_imm_pred.finishBefore.finBefore.sameAddr
      simp[Event.sameAddr] at hcdir_addr he_addr
      simp[hcdir_addr, he_addr]
    . case interPred =>
      by_contra hcdir_not_finish_before_e
      simp[Event.finishesBefore] at hcdir_not_finish_before_e
      simp[Nat.le_iff_lt_or_eq] at hcdir_not_finish_before_e
      cases hcdir_not_finish_before_e
      . case inl he_lt_cdir_end =>
        have hcdir_not_inter_e := he_no_inter e_cdir he_cdir_in_b
        apply hcdir_not_inter_e
        constructor
        . case sameCidInterPred =>
          apply Eq.symm
          apply Behaviour.same_corresponding_gcache_same_struct
          . case he_cdir_satisfies => exact he_cdir_satisfies
          . case he_is_imm_pred => exact he_is_imm_pred
        . case sameAddr =>
          have hcdir_addr := he_cdir_satisfies.finishBefore.finBefore.sameAddr
          have he_addr := he_is_imm_pred.finishBefore.finBefore.sameAddr
          simp[Event.sameAddr] at hcdir_addr he_addr
          simp[hcdir_addr, he_addr]
        . case interPred => simp[Event.finishesBefore, he_lt_cdir_end]
        . case interSucc => simp[he_cdir_satisfies.finishBefore.finBefore.endBefore]
      . case inr he_eq_cdir_end =>
        -- Contradiction, all directory events are ordered.
        match he : e, hcdir : e_cdir with
        | .directoryEvent de, .directoryEvent de_cdir =>
          simp[Event.oEnd] at he_eq_cdir_end
          have hordered := b.orderedAtEntry.dir_ordered de de_cdir |>.ordered
          simp[DirectoryEvent.Ordered] at hordered
          cases hordered
          . case inl hde_ob_cdir =>
            apply Event.contradiction_of_directory_event_ends_eq
            . case he_eq_cdir_end => exact he_eq_cdir_end
            . case hde_ob_cdir => exact hde_ob_cdir
          . case inr hcdir_ob_de =>
            apply Event.contradiction_of_directory_event_ends_eq
            . case he_eq_cdir_end =>
              apply Eq.symm
              exact he_eq_cdir_end
            . case hde_ob_cdir => exact hcdir_ob_de
        | .cacheEvent ce, .directoryEvent de_cdir
        | .directoryEvent de, .cacheEvent ce_cdir
        | .cacheEvent ce, .cacheEvent ce_cdir
          =>
          have hcdir_at_gcache := he_cdir_satisfies.finishBefore.gCacheOfCDir
          have he_at_gcache := he_is_imm_pred.finishBefore.gCacheOfCDir
          simp[Event.reqAtCorrespondingGCacheOfCDir] at hcdir_at_gcache he_at_gcache
    . case interSucc => exact he_is_imm_pred.finishBefore.finBefore.endBefore
  . case h.mpr =>
    simp
    intro he_eq_e_cdir
    simp[he_eq_e_cdir, he_cdir_in_b]
    exact he_cdir_satisfies

lemma Behaviour.global_downgrade_cache_translation_encap_corresponding_request
  {e_gdown e_shim_coh_request e_dir_shim_coh_request : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hrequest_protocol : Event.correspondingClusterOfGlobalCache n e_gdown e_shim_coh_request (Event.protocol n))
  (hdir_req_same_protocol_req : Event.protocol n e_shim_coh_request = e_dir_shim_coh_request.protocol)
  (hdir_is_dir : e_dir_shim_coh_request.isDirectoryEvent)
  : Event.reqAtCorrespondingGCacheOfCDir n e_dir_shim_coh_request e_gdown := by
  simp[Event.reqAtCorrespondingGCacheOfCDir]
  match hread_dir : e_dir_shim_coh_request with
  | .directoryEvent de =>
    simp
    simp[Event.protocol]
    -- have hread_protocol := hfwd_mr_down_translation.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
    simp[Event.correspondingClusterOfGlobalCache] at hrequest_protocol

    have hgdown_cache := hgdown.isGlobal.notAtGProxy
    simp[Event.reqAtGlobalCache] at hgdown_cache
    match e_gdown with
    | .cacheEvent ce =>
      simp[] at hgdown_cache
      simp at hrequest_protocol
      match hcid : ce.cid with
      | .cache pci =>
        simp[hcid] at hgdown_cache hrequest_protocol
        match pci with
        | .globalP gcid2 =>
          simp at hgdown_cache hrequest_protocol
          match gcid2 with
          | 0 | 1 =>
            simp at hrequest_protocol
            -- have hdir_read_same_protocol_read := hfwd_mr_down_translation.cohReadDir.sameProtocol
            match hdir_request_protocol : de.pInst with
            | .cluster1 | .cluster2 | .global =>
              simp[Event.reqAtGlobalCacheCid, hcid]
              try (
                rw[hrequest_protocol] at hdir_req_same_protocol_req
                absurd hdir_req_same_protocol_req
                simp[Event.protocol]
                rw[hdir_request_protocol]
                simp)
        | .cluster1 _ | .cluster2 _ => simp at hgdown_cache
      | .proxy _ => simp[hcid] at hgdown_cache
    | .directoryEvent _ => simp[Event.reqAtGlobalCache] at hgdown_cache
  | .cacheEvent _ =>
    -- have hdir_is_dir := hfwd_mr_down_translation.cohReadDir.isDir
    simp[Event.isDirectoryEvent,] at hdir_is_dir

lemma Behaviour.global_sw_downgrade_dir_evict_has_no_intermediate {b : Behaviour n} {init : InitialSystemState n}
  {e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Behaviour.encapCorrespondingGetSWAndEvict n b init e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_coh_evict e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  have honly_encap_get_put_dir := hfwd_sw_down_translation.onlyWriteEvictDir
  intro e_inter hinter_in_b hinter_finishes_btn_evict_and_gdown
  have hdir_evict_same_struct_inter := hinter_finishes_btn_evict_and_gdown.sameCidInterPred
  match hdir_evict : e_dir_shim_coh_evict, hinter : e_inter with
  | .directoryEvent de_dir_evict , .directoryEvent de_inter =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_evict de_inter
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_evict_ob_inter =>
      -- can't have another event between dir_evict and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        constructor
        . case clusterMatch =>
          constructor
          . case sameAddr =>
            simp[Event.sameAddr]
            rw[hinter, hinter_finishes_btn_evict_and_gdown.sameAddr]
            rw[← hfwd_sw_down_translation.cohEvictDir.dirCorresponds.sameAddr]
            simp[← Event.sameAddr.eq_1, hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.clusterMatch.sameAddr]
          . case atCorrCluster =>
            have hdir_evict_corr_cluster := Behaviour.global_downgrade_cache_translation_encap_corresponding_request n hgdown
              hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.clusterMatch.atCorrCluster
              hfwd_sw_down_translation.cohEvictDir.sameProtocol
              hfwd_sw_down_translation.cohEvictDir.isDir
            simp[Event.reqAtCorrespondingGCacheOfCDir] at hdir_evict_corr_cluster
            simp[Event.correspondingClusterOfGlobalCache]

            simp[Event.protocol] at hdir_evict_corr_cluster
            match hdir_evict_pi : de_dir_evict.pInst with
            | .global | .cluster2 | .cluster1 =>
              simp[hdir_evict_pi] at hdir_evict_corr_cluster
              try (
              simp[Event.reqAtGlobalCacheCid] at hdir_evict_corr_cluster
              match e_gdown with
              | .cacheEvent ce_gdown =>
                simp_all
                match hcegdown_cid : ce_gdown.cid with
                | .cache pci =>
                  simp_all []
                  match pci with
                  | .cluster1 _ | .cluster2 _ | .globalP fin2 =>
                    simp_all
                    try (
                    simp[Event.protocol]
                    simp[Event.struct] at hdir_evict_same_struct_inter
                    rw[hdir_evict_same_struct_inter]
                    exact hdir_evict_pi)
                | .proxy pi => simp[hcegdown_cid] at hdir_evict_corr_cluster
              | .directoryEvent _ => simp at hdir_evict_corr_cluster
              )
        . case atDir => simp [Event.isDirectoryEvent, hinter]
        . case globalEncap =>
          simp[Event.Encapsulates]
          apply And.intro
          . case left =>
            simp [DirectoryEvent.OrderedBefore] at hdir_evict_ob_inter
            calc e_gdown.oStart < e_shim_coh_evict.oStart := hfwd_sw_down_translation.cohEvict.globalEncap.left
                _ < e_dir_shim_coh_evict.oStart := by simp[hdir_evict, hfwd_sw_down_translation.cohEvictDir.reqEncapDir.left]
                _ < e_dir_shim_coh_evict.oEnd := e_dir_shim_coh_evict.oWellFormed
                _ < e_inter.oStart := by simp[hdir_evict, hinter, Event.oEnd, Event.oStart, hdir_evict_ob_inter]
          . case right => simp[← Event.finishesBefore.eq_def, hinter, hinter_finishes_btn_evict_and_gdown.interSucc]
      have hinter_is_dir_evict_or_dir_get := honly_encap_get_put_dir e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      cases hinter_is_dir_evict_or_dir_get
      . case inl hinter_eq_dir_write =>
        -- contradiction, hinter is coh get SW dir event, that's immediately before coh put SW dir event.
        rw[hinter] at hinter_eq_dir_write
        absurd hinter_finishes_btn_evict_and_gdown.interPred
        rw[hinter_eq_dir_write]
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hinter_imm_pred_dir_evict := hfwd_sw_down_translation.cohWriteImmBeforeEvict
        simp[ImmediateBottomPredecessor,] at hinter_imm_pred_dir_evict
        have hinter_pred_dir_evict := hinter_imm_pred_dir_evict.isImmPred.bPred.isPred
        simp[Event.Predecessor, Event.OrderedBefore,] at hinter_pred_dir_evict
        match e_dir_shim_coh_write with
        | .directoryEvent de_dir_write =>
          simp[Event.oEnd, Event.oStart] at hinter_pred_dir_evict
          simp[Event.oEnd]
          calc de_dir_write.oEnd < de_dir_evict.oStart := hinter_pred_dir_evict
            _ < de_dir_evict.oEnd := de_dir_evict.oWellFormed
        | .cacheEvent _ =>
          have hwrite_dir_is_dir := hfwd_sw_down_translation.cohWriteDir.isDir
          simp[Event.isDirectoryEvent] at hwrite_dir_is_dir
      . case inr hinter_eq_dir_evict =>
        -- contradiction, dir evict event can't finish before itself!
        absurd hinter_finishes_btn_evict_and_gdown.interPred
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_right
        rw[hinter] at hinter_eq_dir_evict
        rw[hinter_eq_dir_evict]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_finishes_btn_evict_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc de_inter.oEnd < de_dir_evict.oStart := hinter_ob_dir_evict
        _ < de_dir_evict.oEnd := de_dir_evict.oWellFormed
  | .cacheEvent ce_dir_evict , .directoryEvent de_inter
  | .directoryEvent de_dir_evict , .cacheEvent ce_inter
  | .cacheEvent ce_dir_evict , .cacheEvent ce_inter =>
    have hdir_evict_dir := hfwd_sw_down_translation.cohEvictDir.isDir
    simp[Event.struct] at hdir_evict_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_evict_dir

lemma Behaviour.cluster_dir_event_immediately_finish_before_of_global_downgrade {b : Behaviour n} {init : InitialSystemState n}
  {e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Behaviour.encapCorrespondingGetSWAndEvict n b init e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_coh_evict e_gdown := by
  /- `e_shim_coh_evict` must be the last event finishing before `e_gdown` finishes.
  Proof by contradiction:
  Assume there is another event `e_dir_other` that finishes before `e_shim_coh_evict`, it requires another directory event to be
  ordered after `e_shim_coh_evict`.
  Another event `e_dir_other` can only come from another cache request or global cache event + shim axiom.
  This shim axiom contains no other directory events, so `e_dir_other` must be from a cache request.
  However, a cache request will not finish before `e_gdown`, because a cache request to increase permissions
  greater than `e_shim_coh_evict` will need to encapsulate a Global Cache Event, which will need to be
  ordered with respect to `e_gdown`, and so it will need to be ordered after.
  Therefore, `e_dir_other` cannot finish before `e_gdown`, after `e_shim_coh_evict`, a contradiction with `e_dir_other`.
  -/
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore =>
        simp[Event.finishesBefore,]
        calc e_dir_shim_coh_evict.oEnd < e_shim_coh_evict.oEnd := hfwd_sw_down_translation.cohEvictDir.reqEncapDir.right
          _ < e_gdown.oEnd := hfwd_sw_down_translation.cohEvict.globalEncap.right
      . case sameAddr =>
        simp[Event.sameAddr, Eq.comm]
        calc e_gdown.addr = e_shim_coh_evict.addr := hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.clusterMatch.sameAddr
          _ = e_dir_shim_coh_evict.addr := hfwd_sw_down_translation.cohEvictDir.dirCorresponds.sameAddr
      . case predInB => simp[hfwd_sw_down_translation.cohEvictDir.dirInB]
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => exact hfwd_sw_down_translation.cohEvictDir.sameProtocol
      . case hdir_is_dir => exact hfwd_sw_down_translation.cohEvictDir.isDir
  . case noIntermediate =>
    apply Behaviour.global_sw_downgrade_dir_evict_has_no_intermediate
    . case hgdown => exact hgdown
    . case hfwd_sw_down_translation => exact hfwd_sw_down_translation

lemma Behaviour.cluster_dir_events_same_requester_of_global_sc_downgrade {b : Behaviour n} {init : InitialSystemState n}
  {e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Behaviour.encapCorrespondingGetSWAndEvict n b init e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict)
  : e_dir_shim_coh_write.directoryEventSameRequester n e_dir_shim_coh_evict
    := by
    simp[Event.directoryEventSameRequester]
    have hget_dir := hfwd_sw_down_translation.cohWriteDir.isDir
    have hput_dir := hfwd_sw_down_translation.cohEvictDir.isDir
    match hwrite : e_dir_shim_coh_write, hevict : e_dir_shim_coh_evict with
    | .directoryEvent get_dir, .directoryEvent put_dir
      =>
      simp
      simp[DirectoryEvent.sameRequester]
      have hget_proxy := hfwd_sw_down_translation.cohWrite.atCorrClusterProxy.atProxy
      have hput_proxy := hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.atProxy
      simp[Event.atProxy] at hget_proxy hput_proxy
      match hwrite : e_shim_coh_write, hevict : e_shim_coh_evict with
      | .cacheEvent ce_write, .cacheEvent ce_evict =>
        simp at hget_proxy hput_proxy
        match hwrite_cid : ce_write.cid, hevict_cid : ce_evict.cid with
        | .proxy pi_write, .proxy pi_evict =>
          simp[hwrite_cid, hevict_cid] at hget_proxy hput_proxy
          -- both at proxy. now show both at same Protocol Instance `pi`
          have hget_pi := hfwd_sw_down_translation.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
          have hput_pi := hfwd_sw_down_translation.cohEvict.atCorrClusterProxy.clusterMatch.atCorrCluster
          simp[Event.correspondingClusterOfGlobalCache] at hget_pi hput_pi
          match e_gdown with
          | .cacheEvent cgdown =>
            simp at hget_pi hput_pi
            match hgdown_cid : cgdown.cid with
            | .cache pci =>
              simp[hgdown_cid] at hget_pi hput_pi
              match pci with
              | .globalP fin2 =>
                simp[] at hget_pi hput_pi
                match fin2 with
                | 0 | 1 =>
                  simp[] at hget_pi hput_pi
                  simp[Event.protocol] at hget_pi hput_pi
                  simp[hwrite_cid, hevict_cid] at hget_pi hput_pi
                  -- same protocol
                  -- the dir events have corresponding rids
                  have hget_dir_proxy := hfwd_sw_down_translation.cohWriteDir.dirOfReq
                  have hput_dir_proxy := hfwd_sw_down_translation.cohEvictDir.dirOfReq
                  simp[Event.dirEventOfReqEvent] at hget_dir_proxy hput_dir_proxy
                  have hget_dir_of_cget := hget_dir_proxy.correspondingCE
                  have hput_dir_of_cput := hput_dir_proxy.correspondingCE
                  rw[hget_dir_of_cget, hput_dir_of_cput]

                  rw[hwrite_cid, hevict_cid, hget_pi, hput_pi]
              | .cluster1 _ | .cluster2 _ => simp[] at hget_pi hput_pi
            | .proxy _ => simp[hgdown_cid] at hget_pi hput_pi
          | .directoryEvent _ => simp at hget_pi hput_pi
        | .cache _, .proxy _ | .proxy _, .cache _ | .cache _, .cache _
          => simp [hwrite_cid, hevict_cid] at hget_proxy hput_proxy
      | .directoryEvent _, .directoryEvent _ | .cacheEvent _, .directoryEvent _ | .directoryEvent _, .cacheEvent _
        => simp at hget_proxy hput_proxy
    | .cacheEvent get_dir, .directoryEvent put_dir | .directoryEvent get_dir, .cacheEvent put_dir | .cacheEvent get_dir, .cacheEvent put_dir
      => simp[Event.isDirectoryEvent] at hget_dir hput_dir

lemma Set.toOption_singleton'' {α} {s : Set α} (e : α) {hsingleton : s = {e}} : s.toOption = some e := by
  simp only [toOption, Option.dite_none_right_eq_some,]
  have hs_nonempty' : Nonempty s := by
    simp []
    use e
    simp[Set.eq_singleton_iff_unique_mem] at hsingleton
    obtain ⟨hsingle_in_s, helem_of_s⟩ := hsingleton
    simp[hsingle_in_s]
  use hs_nonempty'
  obtain ⟨_,hxs_eq_singleton⟩ := Set.eq_singleton_iff_unique_mem.mp hsingleton
  simp
  apply hxs_eq_singleton
  . case h.intro.a =>
    apply Nonempty.some_mem
    . case h =>
      use e

lemma Behaviour.event_immediate_finish_before_gdown_singleton'
  {b : Behaviour n} {e_cdir e_gdown : Event n} (he_cdir_in_b : e_cdir ∈ b)
  (he_cdir_satisfies : immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_cdir e_gdown)
  (himm_finish_before_subsingleton : (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).Subsingleton)
  : {e_pred | e_pred ∈ b ∧ Behaviour.immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown} = {e_cdir} := by
  simp [immediateFinishesBeforeAtClusterDirectoryEventsNotEncap] at himm_finish_before_subsingleton
  simp [Set.Subsingleton] at himm_finish_before_subsingleton
  apply Set.ext
  intro e
  apply Iff.intro
  . case h.mp =>
    simp
    -- intro he_in_set
    intro he_in_b he_is_imm_pred
    apply himm_finish_before_subsingleton
    . case a => exact he_in_b
    . case a => exact he_is_imm_pred
    . case a => exact he_cdir_in_b
    . case a => exact he_cdir_satisfies
  . case h.mpr =>
    simp
    intro he_eq_e_cdir
    simp[he_eq_e_cdir, he_cdir_in_b]
    exact he_cdir_satisfies

lemma Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_directory_state
  {b e_gdown} (init : InitialSystemState n) (hgdown_cache : e_gdown.isCacheEvent)
  (hgdown : e_gdown.isGlobalDowngrade)
  : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))).isDirectoryState
  := by
  simp[eventToEntryState]
  by_cases h_nonempty : Nonempty (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown)
  . case pos =>
    simp[immediateFinishesBeforeAtClusterDirectoryEventsNotEncap]
    simp[immediateFinishesBeforeAtClusterDirectoryEventsNotEncap] at h_nonempty
    have himm_finish_subsingleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_subsingleton n b e_gdown
    rw[Behaviour.event_immediate_finish_before_gdown_singleton' n
      h_nonempty.choose_spec.left
      h_nonempty.choose_spec.right
      himm_finish_subsingleton
      ]
    rw[Set.toOption_singleton'' h_nonempty.choose]

    simp[]
    have h_is_dir : h_nonempty.choose.isDirectoryEvent := by
      have h := h_nonempty.choose_spec.right.finishBefore.gCacheOfCDir
      simp[Event.reqAtCorrespondingGCacheOfCDir] at h
      match hevent : h_nonempty.choose with
      | .directoryEvent _ => simp[Event.isDirectoryEvent]
      | .cacheEvent _ => simp [hevent] at h
    apply Behaviour.stateAfter_directory_event_is_directory_state
    . case hdir_is_dir =>
      exact h_is_dir
    . case hinit_dir =>
      simp[InitialSystemState.stateAt]
      match hevent : h_nonempty.choose with
      | .directoryEvent _ => simp[EntryState.isDirectoryState]
      | .cacheEvent _ => simp [Event.isDirectoryEvent, hevent] at h_is_dir
    . case hall_dir =>
      have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b h_nonempty.choose
      simp
      intro e' he'
      cases he'
      . case inl he'_in_upto =>
        apply hall_dir
        . case a => exact he'_in_upto
      . case inr he'_eq_nonempty =>
        constructor
        . case eInB =>
          have hchoose_in_b := h_nonempty.choose_spec.left
          simp[he'_eq_nonempty, hchoose_in_b]
        . case eAtStruct => simp[he'_eq_nonempty]
        . case eAtAddr => simp[he'_eq_nonempty]
    rfl
  . case neg =>
    simp [Set.toOption]
    simp [ h_nonempty ]
    simp[Event.clusterDirProtocolCorrespondingToGlobalCache]

    match e_gdown with
    | .cacheEvent ce =>
      match hcid : ce.cid with
      | .cache pci =>
        match pci with
        | .globalP gcid2 =>
          match gcid2 with
          | 0 | 1 =>
            simp[hcid]
            simp[InitialSystemState.entryStateAtStruct]
            simp[EntryState.isDirectoryState]
        | .cluster1 _ | .cluster2 _ =>
          have h := hgdown.isGlobal.reqGlobal
          simp[Event.protocol] at h
          simp[hcid] at h
      | .proxy _ =>
        have h := hgdown.isGlobal.notAtGProxy
        simp[Event.reqAtGlobalCache] at h
        simp[hcid] at h
    | .directoryEvent _ => simp[Event.isCacheEvent] at hgdown_cache

/-- Helper Lemma: An event `e` at the corresponding Cluster Directory to `e_gdown`, (`Event.reqAtCorrespondingGCacheOfCDir`)
satisfies a similar definition `Event.correspondingClusterOfGlobalCache` -/
lemma Behaviour.event_reqAtCorrespondingGCacheOfCDir_is_correspondingClusterOfGlobalCache
  (he_req_corr_gcache : Event.reqAtCorrespondingGCacheOfCDir n event e_gdown)
  : Event.correspondingClusterOfGlobalCache n e_gdown event (Event.protocol n) := by
  simp [Event.reqAtCorrespondingGCacheOfCDir] at he_req_corr_gcache
  simp [Event.correspondingClusterOfGlobalCache]

  match event with
  | .directoryEvent de =>
    simp[Event.protocol] at he_req_corr_gcache
    match hde_inst : de.pInst with
    | .cluster1 | .cluster2 =>
      simp[hde_inst] at he_req_corr_gcache
      simp[Event.reqAtGlobalCacheCid] at he_req_corr_gcache

      -- now match on e_gdown
      match e_gdown with
      | .cacheEvent cgdown =>
        simp_all
        match hgcid : cgdown.cid with
        | .cache pci =>
          simp_all [hgcid]
          match pci with
          | .globalP fin2 =>
            match fin2 with
            | 0 | 1 => simp_all[hde_inst, Event.protocol]
          | .cluster1 _ | .cluster2 _ =>
            simp at he_req_corr_gcache
        | .proxy _ =>
          simp [hgcid] at he_req_corr_gcache
      | .directoryEvent _ =>
        simp at he_req_corr_gcache
    | .global =>
      simp[hde_inst] at he_req_corr_gcache
  | .cacheEvent _ => simp[] at he_req_corr_gcache

/-- Helper Lemma: an event `e` satisfying `Event.reqAtCorrespondingGCacheOfCDir` at `e_gdown`
is a DirectoryEvent. -/
lemma Behaviour.reqAtCorrespondingGCacheOfCDir_is_directory_event
  (he_req_corr_gcache : Event.reqAtCorrespondingGCacheOfCDir n e e_gdown)
  : e.isDirectoryEvent := by
  simp[Event.isDirectoryEvent]
  simp[Event.reqAtCorrespondingGCacheOfCDir] at he_req_corr_gcache

  match e with
  | .directoryEvent de => simp
  | .cacheEvent _ => simp[] at he_req_corr_gcache

lemma Behaviour.event_in_eventsUpToEvent_correspond_to_egdown_also_at_gCacheOfCDir
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (hes_upto : eventsUpToEvent n b e_cdir = l ++ [tail])
  : Event.reqAtCorrespondingGCacheOfCDir n tail e_gdown := by
  simp[Event.reqAtCorrespondingGCacheOfCDir]
  have hall_es_same_entry : ∀ e' ∈ b.eventsUpToEvent n e_cdir, b.eventAtEntry n e' e_cdir.struct e_cdir.addr := Behaviour.eventsUpToEntry_at_e_entry' n
  have htail_at_entry := hall_es_same_entry tail (by rw[hes_upto]; simp)
  have htail_at_struct := htail_at_entry.eAtStruct
  -- have htail_at_ := htail_at_entry.

  simp [Event.correspondingClusterOfGlobalCache] at hcdir_corr_gdown
  match e_gdown with
  | .cacheEvent ce_gdown =>
    simp at hcdir_corr_gdown
    match hgcid : ce_gdown.cid with
    | .cache pci =>
      simp [hgcid] at hcdir_corr_gdown
      match pci with
      | .globalP fin2 =>
        match fin2 with
        | 0 | 1 =>
          simp [] at hcdir_corr_gdown
          match e_cdir, tail with
          | .directoryEvent de_cdir, .directoryEvent de_tail =>
            simp[Event.struct] at htail_at_struct
            simp
            simp[Event.protocol]
            rw[htail_at_struct]
            simp[Event.protocol] at hcdir_corr_gdown
            simp[hcdir_corr_gdown]
            simp[Event.reqAtGlobalCacheCid]
            simp[hgcid]
          | .cacheEvent _, .cacheEvent _
          | .directoryEvent _, .cacheEvent _
          | .cacheEvent _, .directoryEvent _ =>
            simp[Event.isDirectoryEvent] at hcdir_is_dir
            try simp[Event.struct] at htail_at_struct
      | .cluster1 _ | .cluster2 _ =>
        simp [] at hcdir_corr_gdown
    | .proxy _ =>
      simp [hgcid] at hcdir_corr_gdown
  | .directoryEvent _ => simp [] at hcdir_corr_gdown

lemma Behaviour.eventsUpToEvent_tail_finishes_immediately_before {b e_cdir l tail}
  (e_gdown : Event n)
  (hcdir_in_b : e_cdir ∈ b)
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_same_addr_gdown : e_cdir.sameAddr n e_gdown)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (h : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (hgdown_in_b : e_gdown ∈ b)
  (hgdown_encap_cdir : e_gdown.Encapsulates n e_cdir)
  : eventsUpToEvent n b e_cdir = l ++ [tail] → immediateFinishesBeforeAtClusterDirectoryNotEncap n b tail e_gdown := by
  intro hes_upto
  have hdir_bottom := Behaviour.directory_event_is_bottom n b e_cdir (by simp[hcdir_is_dir])
  have htail_pred_cdir := Behaviour.eventsUpToEvent_are_pred_to_e n b e_cdir hcdir_in_b hdir_bottom tail (by rw[hes_upto]; simp)
  have htail_correspond_gdown : Event.reqAtCorrespondingGCacheOfCDir n tail e_gdown := by
    apply Behaviour.event_in_eventsUpToEvent_correspond_to_egdown_also_at_gCacheOfCDir n hcdir_is_dir
    . case hcdir_corr_gdown => exact hcdir_corr_gdown
    . case hes_upto => exact hes_upto
  have hall_es_same_entry : ∀ e' ∈ b.eventsUpToEvent n e_cdir, b.eventAtEntry n e' e_cdir.struct e_cdir.addr := Behaviour.eventsUpToEntry_at_e_entry' n
  rw[hes_upto] at hall_es_same_entry
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      have htail_same_struct_cdir := hall_es_same_entry tail (by simp)
      constructor
      . case endBefore =>
        simp[Event.finishesBefore]
        have := htail_pred_cdir.isPred
        simp[Event.Encapsulates] at hgdown_encap_cdir
        calc tail.oEnd < e_cdir.oStart := htail_pred_cdir.isPred
          _ < e_cdir.oEnd := e_cdir.oWellFormed
          _ < e_gdown.oEnd := hgdown_encap_cdir.right
      . case sameAddr =>
        have test := htail_same_struct_cdir.eAtAddr
        simp_all[Event.sameAddr]
      . case predInB => exact Behaviour.eventsUpToEvent_in_b n b e_cdir tail (by rw[hes_upto]; simp)
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.event_in_eventsUpToEvent_correspond_to_egdown_also_at_gCacheOfCDir n hcdir_is_dir
      . case hcdir_corr_gdown => exact hcdir_corr_gdown
      . case hes_upto => exact hes_upto
  . case notEncap =>
    intro hgdown_encap_tail
    have htail_same_addr_cdir : tail.sameAddr n e_gdown := by
      have := hall_es_same_entry tail (by simp) |>.eAtAddr
      simp_all[Event.sameAddr]
    have htail_not_ob_e_cdir := h tail htail_pred_cdir.predInB htail_same_addr_cdir htail_correspond_gdown hgdown_encap_tail
    have htail_pred_e_cdir := htail_pred_cdir.isPred
    simp[Event.Predecessor] at htail_pred_e_cdir
    contradiction
  . case noIntermediate =>
    simp[noIntermediateFinishesBeforeOfSameEntryNotEncap]
    intro e_inter hinter_in_b hinter

    have hbefore_cdir := Behaviour.eventsUpToEvent_are_pred_to_e n b e_cdir
    have := hinter.interFinish.interSucc
    have hinter_not_encap := hinter.notEncap
    -- intermediate must be ordered before `e_cdir`

    -- anything ordered before e_cdir, is in `eventsUpToEvent of e_cdir`
    -- so it's in l, before tail, since it's not tail.
    -- but then it doesn't finish after `tail` does, so contradiction.

    match hcdir : e_cdir with
    | .directoryEvent de_cdir =>
      -- have hes_in_b := (Behaviour.eventsUpToEvent_in_b n b e_cdir) tail (by simp[hcdir, hes_upto])
      have hes_at_dir := (Behaviour.eventsUpToEvent_are_at_entry n b e_cdir) tail (by simp[hcdir, hes_upto])
      have htail_at_dir := hes_at_dir.eAtStruct
      match htail : tail with
      | .directoryEvent de_tail =>
        have hsame_struct_as_tail := hinter.interFinish.sameCidInterPred
        match h_dinter : e_inter with
        | .directoryEvent de_inter =>
          -- Now say `e_inter` is ordered with `e_cdir`
          have hinter_ordered_cdir := b.orderedAtEntry.dir_ordered de_inter de_cdir |>.ordered
          simp[DirectoryEvent.Ordered] at hinter_ordered_cdir
          cases hinter_ordered_cdir
          . case inl hinter_ob_cdir =>
            have hinter_before_cdir : e_inter.OrderedBefore n e_cdir := by
              simp[Event.OrderedBefore]
              simp[DirectoryEvent.OrderedBefore] at hinter_ob_cdir
              simp[h_dinter, hcdir, Event.oEnd, Event.oStart, hinter_ob_cdir]

            have hdir_bottom := Behaviour.directory_event_is_bottom n b e_cdir (by simp[hcdir, hcdir_is_dir])

            have hinter_pred_cdir : b.Predecessor n e_inter e_cdir := by
              have hall_es_same_entry : ∀ e' ∈ b.eventsUpToEvent n e_cdir, b.eventAtEntry n e' e_cdir.struct e_cdir.addr := Behaviour.eventsUpToEntry_at_e_entry' n
              rw[← htail, ← hcdir] at hes_upto
              rw[hes_upto] at hall_es_same_entry
              have htail_same_struct_cdir := hall_es_same_entry tail (by simp)
              constructor
              . case sameEntry =>
                constructor
                . case sameStruct =>
                  simp[Event.sameStructure,]
                  have hinter_same_struct_tail := hinter.interFinish.sameCidInterPred
                  rw[← htail, ← h_dinter] at hinter_same_struct_tail
                  rw[hinter_same_struct_tail]

                  rw[← htail_same_struct_cdir.eAtStruct]
                . case sameAddr =>
                  have hinter_same_addr_tail := hinter.interFinish.sameAddr
                  simp[Event.sameAddr]
                  rw[← htail, ← h_dinter] at hinter_same_addr_tail
                  rw[hinter_same_addr_tail]

                  rw[← htail_same_struct_cdir.eAtAddr]
              . case isPred =>
                simp[Event.Predecessor, Event.OrderedBefore]
                simp[h_dinter, hcdir, Event.oEnd, Event.oStart, ← DirectoryEvent.OrderedBefore.eq_def, hinter_ob_cdir]
              . case predInB => simp [h_dinter, hinter_in_b]
              . case succInB => simp [hcdir, hcdir_in_b]
            have hinter_in_es : e_inter ∈ eventsUpToEvent n b e_cdir :=
              Behaviour.predecessor_of_e_in_eventsUpToEvent_e n b e_cdir (by simp[hcdir, hcdir_in_b]) hdir_bottom
              (by simp[hcdir,hcdir_is_dir]) hinter_pred_cdir

            rw[hcdir] at hinter_in_es
            rw[hes_upto] at hinter_in_es
            simp at hinter_in_es

            cases hinter_in_es
            . case inl hinter_in_l =>
              -- eventsUptoEvent is sorted, so `e_inter` finishes after `e_cdir` is a contradiction
              have hes_sorted := Behaviour.eventsUpToEvent_ordered_before_sorted n b e_cdir
              simp[List.Sorted] at hes_sorted
              simp[List.pairwise_iff_getElem] at hes_sorted

              let idx_of_inter := List.idxOf (e_inter) (eventsUpToEvent n b e_cdir)
              let idx_of_tail := List.idxOf (tail) (eventsUpToEvent n b e_cdir)

              -- simp [eventsUpToEvent] at hes_upto

              have hinter_in_es : e_inter ∈ (eventsUpToEvent n b e_cdir) := by
                rw[← hcdir] at hes_upto
                rw[← htail] at hes_upto
                rw[hes_upto]
                simp[hinter_in_l]
              have hidx_inter_lt_len := List.idxOf_lt_length_of_mem (hinter_in_es)
              have hcdir_in_es : tail ∈ (eventsUpToEvent n b e_cdir) := by
                rw[← hcdir] at hes_upto
                rw[hes_upto]
                simp[]
                apply Or.intro_right
                simp[htail]
              have hidx_tail_lt_len := List.idxOf_lt_length_of_mem (hcdir_in_es)

              have hidx_inter_lt_tail : List.idxOf (e_inter) (eventsUpToEvent n b e_cdir) < List.idxOf (tail) (eventsUpToEvent n b e_cdir) := by
                rw[← hcdir] at hes_upto
                rw[hes_upto]
                simp[List.idxOf_append_of_mem hinter_in_l]
                simp[← htail,]
                have htail_not_in_l : tail ∉ l := by
                  have hnodups := Behaviour.eventsUpToEvent_no_dups n b e_cdir
                  rw[← htail] at hes_upto
                  rw[hes_upto] at hnodups
                  grind only [List.length_cons, = List.contains_append, = List.nodup_iff_count, =
                    List.pairwise_append, List.getElem_append, = List.idxOf_append, usr
                    List.idxOf_lt_length_iff, =_ List.contains_iff_mem, List.contains_eq_mem, usr
                    List.idxOf_le_length, = List.nodup_cons, = List.nodup_append, =
                    List.nodup_iff_pairwise_ne, List.length_append, List.mem_cons_of_mem,
                    List.mem_cons_self, usr List.length_pos_of_mem, → List.eq_nil_of_append_eq_nil,
                    List.mem_append, = List.pairwise_iff_forall_sublist, = List.pairwise_middle]
                simp[List.idxOf_append_of_notMem htail_not_in_l]
                simp[List.idxOf_lt_length_of_mem hinter_in_l]

              subst idx_of_inter;
              subst idx_of_tail;
              have hinter_ob_tail := hes_sorted
                (List.idxOf (e_inter) (eventsUpToEvent n b e_cdir))
                (List.idxOf (tail) (eventsUpToEvent n b e_cdir))
                hidx_inter_lt_len hidx_tail_lt_len
                hidx_inter_lt_tail
              rw[List.getElem_idxOf] at hinter_ob_tail
              rw[List.getElem_idxOf] at hinter_ob_tail

              simp[Event.OrderedBefore] at hinter_ob_tail
              have hinter_finish_after_tail := hinter.interFinish.interPred
              simp[Event.finishesBefore, ← htail, ← h_dinter] at hinter_finish_after_tail

              absurd hinter_finish_after_tail
              simp[Nat.le_iff_lt_or_eq]
              apply Or.intro_left
              calc Event.oEnd n e_inter < Event.oStart n tail := hinter_ob_tail
                _ < tail.oEnd := tail.oWellFormed
            . case inr hinter_is_tail =>
              rw[h_dinter] at hinter_is_tail
              have hinter_finish_before_tail := hinter.interFinish.interPred
              absurd hinter_finish_before_tail
              simp[Event.finishesBefore,Nat.le_iff_lt_or_eq]
              apply Or.intro_right
              . case h =>
                rw[hinter_is_tail]
          . case inr hcdir_ob_inter =>
            have hcdir_lt_inter_start : e_cdir.oEnd < e_inter.oStart := by
              simp[DirectoryEvent.OrderedBefore] at hcdir_ob_inter
              simp[Event.oEnd, Event.oStart, hcdir, h_dinter, hcdir_ob_inter]
            have hinter_fin_before_gdown := hinter.interFinish.interSucc
            simp[Event.finishesBefore, ← h_dinter] at hinter_fin_before_gdown

            have hgdown_encap_inter : e_gdown.Encapsulates n e_inter := by
              simp[Event.Encapsulates]
              apply And.intro
              . case left =>
                simp[Event.Encapsulates] at hgdown_encap_cdir
                calc e_gdown.oStart < e_cdir.oStart := by simp[hcdir, hgdown_encap_cdir.left]
                  _ < e_cdir.oEnd := e_cdir.oWellFormed
                  _ < e_inter.oStart := hcdir_lt_inter_start
              . case right => exact hinter_fin_before_gdown
            rw[← h_dinter] at hinter_not_encap
            contradiction
        | .cacheEvent _ => simp [Event.struct] at hsame_struct_as_tail
      | .cacheEvent _ => simp[hcdir, Event.struct] at htail_at_dir
    | .cacheEvent _ => simp[Event.isDirectoryEvent] at hcdir_is_dir

lemma Behaviour.exists_immediate_finishes_before_of_non_empty_eventsUpToEvent {b e_cdir e_gdown}
  (hcdir_in_b : e_cdir ∈ b) (hcdir_is_dir : Event.isDirectoryEvent n e_cdir)
  (hcdir_same_addr_gdown : Event.sameAddr n e_cdir e_gdown)
  (h : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (hgdown_in_b : e_gdown ∈ b) (hgdown_encap_cdir : Event.Encapsulates n e_gdown e_cdir)
  : ¬eventsUpToEvent n b e_cdir = [] → ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown := by
  intro hupto_not_empty
  have hnot_empty' := hupto_not_empty
  simp[← List.isEmpty_eq_false_iff] at hupto_not_empty
  rw[List.isEmpty_eq_false_iff_exists_mem] at hupto_not_empty
  -- have h : ∀ e ∈ eventsUpToEvent n b e_cdir, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e e_gdown := Behaviour.placeholder' n

  have hupto_in_b := Behaviour.eventsUpToEvent_in_b n b e_cdir
  have hx_in_b := hupto_in_b hupto_not_empty.choose hupto_not_empty.choose_spec

  induction hes_upto : eventsUpToEvent n b e_cdir using List.reverseRecOn with
  | nil =>
    contradiction
  | append_singleton l tail ih =>
    have aux := Behaviour.eventsUpToEvent_tail_finishes_immediately_before n e_gdown hcdir_in_b hcdir_is_dir hcdir_same_addr_gdown hcdir_corr_gdown h hgdown_in_b hgdown_encap_cdir hes_upto
    use tail
    apply And.intro
    . case h.left =>
      apply Behaviour.eventsUpToEvent_in_b n b e_cdir
      . case a => simp[hes_upto]
    . case h.right => exact aux

lemma Behaviour.eventsUpToEvent_eq_nil_of_empty_finishes_before_events {b e_gdown e_cdir}
  (hcdir_in_b : e_cdir ∈ b) (hcdir_is_dir : Event.isDirectoryEvent n e_cdir)
  (hcdir_same_addr_gdown : Event.sameAddr n e_cdir e_gdown)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (hgdown_in_b : e_gdown ∈ b) (hgdown_encap_cdir : Event.Encapsulates n e_gdown e_cdir)
  (h : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (himm_finish_before_empty : immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown = ∅)
  : (eventsUpToEvent n b e_cdir) = [] := by
  simp [immediateFinishesBeforeAtClusterDirectoryEventsNotEncap] at himm_finish_before_empty

  have this := Set.mem_setOf.mp himm_finish_before_empty

  have hcdir_bottom : Behaviour.IsBottomEvent n b e_cdir :=
    Behaviour.directory_event_is_bottom n b e_cdir hcdir_is_dir
  have hupto_before_e := Behaviour.eventsUpToEvent_are_pred_to_e n b e_cdir hcdir_in_b hcdir_bottom

  by_contra hupto_not_empty
  have hnot_empty' := hupto_not_empty
  -- have hupto_not_empty' : eventsUpToEvent n b e_cdir ≠ [] := by simp[hupto_not_empty]
  simp[← List.isEmpty_eq_false_iff] at hupto_not_empty
  rw[List.isEmpty_eq_false_iff_exists_mem] at hupto_not_empty
  -- have h : ∀ e ∈ eventsUpToEvent n b e_cdir, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e e_gdown := Behaviour.placeholder' n

  have hupto_in_b := Behaviour.eventsUpToEvent_in_b n b e_cdir
  have hx_in_b := hupto_in_b hupto_not_empty.choose hupto_not_empty.choose_spec

  have hexists_imm_fin : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown := by
    by_contra hno_imm_fin
    have this' : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown :=
      Behaviour.exists_immediate_finishes_before_of_non_empty_eventsUpToEvent
        n hcdir_in_b hcdir_is_dir hcdir_same_addr_gdown h hcdir_corr_gdown hgdown_in_b hgdown_encap_cdir hnot_empty'
    contradiction

  have hexists_imm_fin_in_set :
    hexists_imm_fin.choose ∈ {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown} := by
    simp
    apply And.intro
    . case left => exact hexists_imm_fin.choose_spec.left
    . case right => exact hexists_imm_fin.choose_spec.right

  absurd hexists_imm_fin_in_set
  simp [himm_finish_before_empty]

lemma Behaviour.immediate_finishes_before_cluster_not_encap_singleton_of_nonempty_and_subsingleton
  (himm_finish_before_subsingleton : (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).Subsingleton)
  (himm_finish_nonempty : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown)
  : {e_pred | e_pred ∈ b ∧ immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown} = {himm_finish_nonempty.choose} := by
  simp [immediateFinishesBeforeAtClusterDirectoryEventsNotEncap] at himm_finish_before_subsingleton
  simp [Set.Subsingleton] at himm_finish_before_subsingleton
  apply Set.ext
  intro e
  apply Iff.intro
  . case h.mp =>
    simp
    -- intro he_in_set
    intro he_in_b he_is_imm_pred
    apply himm_finish_before_subsingleton
    . case a => exact he_in_b
    . case a => exact he_is_imm_pred
    . case a => exact himm_finish_nonempty.choose_spec.left
    . case a => exact himm_finish_nonempty.choose_spec.right
  . case h.mpr =>
    simp
    intro he_eq_e_cdir
    simp[he_eq_e_cdir, himm_finish_nonempty.choose_spec.left]
    exact himm_finish_nonempty.choose_spec.right

lemma Behaviour.InitialSystemState_eq_of_cluster_directory_corresponding_to_global_cache {e_gdown e_cdir init}
  (hdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
  : InitialSystemState.stateAt n init e_cdir =
  InitialSystemState.entryStateAtStruct n init
    (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))
  := by
  have hvd_cluster := hcdir_matching_cluster.atCorrCluster
  simp[Event.correspondingClusterOfGlobalCache] at hvd_cluster

  simp[Event.clusterDirProtocolCorrespondingToGlobalCache]

  match e_gdown with
  | .cacheEvent ce =>
    simp_all
    match hcid : ce.cid with
    | .cache pci =>
      simp_all[]
      match pci with
      | .globalP fin2 =>
        match fin2 with
        | 0 | 1 =>
          simp at hvd_cluster
          simp
          simp[InitialSystemState.entryStateAtStruct]
          -- [NOTE] update as needed;
          simp[InitialSystemState.stateAt]
          match e_cdir with
          | .directoryEvent de =>
            simp
            simp[Event.protocol] at hvd_cluster
            simp [hvd_cluster]
          | .cacheEvent ce => simp[Event.isDirectoryEvent] at hdir_is_dir
      | .cluster1 _ | .cluster2 _ => simp at hvd_cluster
    | .proxy _ => simp[hcid] at hvd_cluster
  | .directoryEvent _ => simp at hvd_cluster

lemma Behaviour.cluster_directory_matching_global_cache_same_entry {e_gdown e_cdir b}
  (hdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
  (hpred : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown)
  : hpred.choose.sameEntry n e_cdir := by
      constructor
      . case sameStruct =>
        simp[Event.sameStructure]

        have hcdir_cluster_of_gcache := hcdir_matching_cluster.atCorrCluster
        simp[Event.correspondingClusterOfGlobalCache] at hcdir_cluster_of_gcache

        have hpred_cluster_of_gcache := hpred.choose_spec.right.finishBefore.gCacheOfCDir
        simp[Event.reqAtCorrespondingGCacheOfCDir] at hpred_cluster_of_gcache

        match e_gdown with
        | .cacheEvent ce_g =>
          simp_all
          match hcid : ce_g.cid with
          | .cache pci =>
            simp_all[]
            match pci with
            | .globalP fin2 =>
              match fin2 with
              | 0 | 1 =>
                simp at hcdir_cluster_of_gcache
                match e_cdir with
                | .directoryEvent de =>
                  -- simp
                  simp[Event.protocol] at hcdir_cluster_of_gcache
                  nth_rw 1 [Event.struct]
                  simp [hcdir_cluster_of_gcache]
                  -- Now open up `hpred.choose`
                  match he_pred : hpred.choose with
                  | .directoryEvent de_pred =>
                    simp[he_pred] at hpred_cluster_of_gcache
                    match hpred_p : Event.protocol n (Event.directoryEvent de_pred) with
                    | .cluster1
                    | .cluster2 =>
                      simp[hpred_p] at hpred_cluster_of_gcache
                      simp[Event.reqAtGlobalCacheCid] at hpred_cluster_of_gcache
                      match hgcid : ce_g.cid with
                      | .cache pci =>
                        simp[hgcid] at hpred_cluster_of_gcache
                        match pci with
                        | .globalP gfin2 =>
                          simp at hpred_cluster_of_gcache
                          rw[hpred_cluster_of_gcache] at hgcid

                          simp[Event.struct]
                          simp[Event.protocol] at hpred_p
                          rw[hpred_p]

                          -- second goal
                          try (
                            absurd hcid
                            simp[hgcid]
                          )
                        | .cluster1 _ | .cluster2 _=>
                          simp at hpred_cluster_of_gcache
                      | .proxy _ =>
                        simp[hgcid] at hpred_cluster_of_gcache
                      -- sorry
                    | .global =>
                      simp[hpred_p] at hpred_cluster_of_gcache
                  | .cacheEvent _ =>
                    simp[he_pred] at hpred_cluster_of_gcache
                | .cacheEvent ce => simp[Event.isDirectoryEvent] at hdir_is_dir
            | .cluster1 _ | .cluster2 _ => simp at hcdir_cluster_of_gcache
          | .proxy _ => simp[hcid] at hcdir_cluster_of_gcache
        | .directoryEvent _ => simp at hcdir_cluster_of_gcache
      . case sameAddr =>
        have hcdir_addr_eq_gcache := hcdir_matching_cluster.sameAddr
        have hpred_addr_eq_gcache := hpred.choose_spec.right.finishBefore.finBefore.sameAddr
        simp_all[Event.sameAddr]

/-- Helper Lemma: If an event `e` is at the same entry as `e_cdir`
and `e_cdir` is at the corresponding Cluster to `e_gdown`, then
`e` is also at the corresponding cluster to `e_gdown` -/
lemma Behaviour.event_at_same_entry_correspond_to_egdown_also_at_gCacheOfCDir {e : Event n}
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (he_same_entry_cdir : e.sameEntry n e_cdir)
  : Event.reqAtCorrespondingGCacheOfCDir n e e_gdown := by
  simp[Event.reqAtCorrespondingGCacheOfCDir]
  have he_same_struct_cdir := he_same_entry_cdir.sameStruct
  simp[Event.sameStructure] at he_same_struct_cdir

  simp [Event.correspondingClusterOfGlobalCache] at hcdir_corr_gdown
  match e_gdown with
  | .cacheEvent ce_gdown =>
    simp at hcdir_corr_gdown
    match hgcid : ce_gdown.cid with
    | .cache pci =>
      simp [hgcid] at hcdir_corr_gdown
      match pci with
      | .globalP fin2 =>
        match fin2 with
        | 0 | 1 =>
          simp [] at hcdir_corr_gdown
          match e_cdir, e with
          | .directoryEvent de_cdir, .directoryEvent de_tail =>
            simp[Event.struct] at he_same_struct_cdir
            simp
            simp[Event.protocol]
            rw[he_same_struct_cdir]
            simp[Event.protocol] at hcdir_corr_gdown
            simp[hcdir_corr_gdown]
            simp[Event.reqAtGlobalCacheCid]
            simp[hgcid]
          | .cacheEvent _, .cacheEvent _
          | .directoryEvent _, .cacheEvent _
          | .cacheEvent _, .directoryEvent _ =>
            simp[Event.isDirectoryEvent] at hcdir_is_dir
            try simp[Event.struct] at he_same_struct_cdir
      | .cluster1 _ | .cluster2 _ =>
        simp [] at hcdir_corr_gdown
    | .proxy _ =>
      simp [hgcid] at hcdir_corr_gdown
  | .directoryEvent _ => simp [] at hcdir_corr_gdown

/-- Helper Lemma : If an event `e` that's at the same entry as `e_cdir`,
and `e_cdir` is at the corresponding Cluster to `e_gdown`,
then `e` is a directory event. -/
lemma Behaviour.event_at_same_entry_as_cdir_correspond_to_gdown_is_directory_event
  {e : Event n}
  (hpred_corr_to_gdown : Event.reqAtCorrespondingGCacheOfCDir n e e_gdown)
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  : e.isDirectoryEvent := by
  simp[Event.reqAtCorrespondingGCacheOfCDir] at hpred_corr_to_gdown
  match hdpred : e, hdcdir : e_cdir with
  | .directoryEvent de_pred, .directoryEvent de_cdir => simp[Event.isDirectoryEvent]
  | .cacheEvent _, .cacheEvent _
  | .directoryEvent _, .cacheEvent _
  | .cacheEvent _, .directoryEvent _ =>
    simp [hdpred, Event.isDirectoryEvent] at hpred_corr_to_gdown hcdir_is_dir

lemma Behaviour.immediateBottomPredecessor_of_immediateFinishesBeforeAtClusterDirectoryNotEncap_and_matchingCluster_encap
  /- Will need a hypothesis that `e_cdir` is encapsulated by `e_gdown`,
  and no other Event `e` is encapsulated by `e_gdown` at the coresponding cluster directory -/
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_in_b : e_cdir ∈ b)
  (hcdir_same_addr_gdown : e_cdir.sameAddr n e_gdown)
  (h : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (hgdown_encap_cdir : e_gdown.Encapsulates n e_cdir)
  (hpred : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown)
  : ImmediateBottomPredecessor n b hpred.choose e_cdir := by
  have hpred_same_entry_cdir := Behaviour.cluster_directory_matching_global_cache_same_entry n hcdir_is_dir hcdir_matching_cluster hpred
  constructor
  . case isImmPred =>
    -- all directory events are ordered. in the `e_cdir`.OrderedBefore `e_pred` case, show a contradiction.
    -- have hpred_spec := himm_finish_nonempty.choose_spec.right
    constructor
    . case bPred =>
      constructor
      . case sameEntry => exact hpred_same_entry_cdir
      . case isPred =>
        simp[Event.Predecessor, Event.OrderedBefore]
        -- [] prove lemma to say that corresponding to a CDir as well means hpred.choose is a DirectoryEvent.
        have hpred_corr_to_gdown := hpred.choose_spec.right.finishBefore.gCacheOfCDir
        -- Need to unfold to get directory events, then use the fact that directory events are ordered
        simp[Event.reqAtCorrespondingGCacheOfCDir] at hpred_corr_to_gdown
        match hdpred : hpred.choose, hdcdir : e_cdir with
        | .directoryEvent de_pred, .directoryEvent de_cdir =>
          /- handle cases of the two events being ordered;
          Need `h` to state that the de_pred isn't ordered after de_cdir -/
          have hdordered := b.orderedAtEntry.dir_ordered de_pred de_cdir |>.ordered
          cases hdordered
          . case inl hpred_ob_cdir =>
            simp[DirectoryEvent.OrderedBefore] at hpred_ob_cdir
            simp[Event.oEnd, Event.oStart, hpred_ob_cdir]
          . case inr hcdir_ob_pred =>
            simp[DirectoryEvent.OrderedBefore] at hcdir_ob_pred
            have hgdown_encap_pred : e_gdown.Encapsulates n hpred.choose :=
              Behaviour.gdown_encap_finish_before_cdir n hdpred hdcdir hpred.choose_spec.right.finishBefore.finBefore.endBefore
                hcdir_ob_pred (by simp[hdcdir, hgdown_encap_cdir])
            have hgdown_not_encap_pred := hpred.choose_spec.right.notEncap
            contradiction
        | .cacheEvent _, .cacheEvent _
        | .directoryEvent _, .cacheEvent _
        | .cacheEvent _, .directoryEvent _ =>
          simp [hdpred, Event.isDirectoryEvent] at hpred_corr_to_gdown hcdir_is_dir
      . case predInB => exact hpred.choose_spec.left
      . case succInB => exact hcdir_in_b
    . case noIntermediate =>
      simp[NoIntermediatePredecessor]
      /- this implies there is another "immediate finishes before at cluster not encap" (`immediateFinishesBeforeAtClusterDirectoryNotEncap`)
      like `hpred.choose`, but `hpred.choose` is the immediate.
      -/
      simp[noBottomIntermediatePredecessorAtSucc]
      intro e_inter hinter_in_b hinter_bottom_same_entry hinter_ordered_btn_pred_cdir
      have hpred_no_inter := hpred.choose_spec.right.noIntermediate e_inter hinter_in_b
      -- simp [noIntermediateFinishesBeforeOfSameEntryNotEncap] at hpred_no_inter
      -- have hpred_inter_as_inter := hpred_no_inter e_inter hinter_in_b
      apply hpred_no_inter
      constructor
      . case interFinish =>
        constructor
        . case sameCidInterPred =>
          have hpred_same_struct_cdir := hpred_same_entry_cdir.sameStruct
          have hinter_same_struct_cdir := hinter_bottom_same_entry.sameEntry.sameStruct
          simp_all [Event.sameStructure]
        . case sameAddr =>
          have hpred_same_struct_cdir := hpred_same_entry_cdir.sameAddr
          have hinter_same_struct_cdir := hinter_bottom_same_entry.sameEntry.sameAddr
          simp_all[Event.sameAddr]
        . case interPred =>
          simp[Event.finishesBefore]
          calc hpred.choose.oEnd < e_inter.oStart := hinter_ordered_btn_pred_cdir.pred
            _ < e_inter.oEnd := e_inter.oWellFormed
        . case interSucc =>
          simp[Event.finishesBefore]
          calc e_inter.oEnd < e_cdir.oStart := hinter_ordered_btn_pred_cdir.succ
            _ < e_cdir.oEnd := e_cdir.oWellFormed
            _ < e_gdown.oEnd := hgdown_encap_cdir.right
      . case notEncap =>
        intro hgdown_encap_inter
        absurd hinter_ordered_btn_pred_cdir.succ
        apply h
        . case a => exact hinter_in_b
        . case a =>
          have := hinter_bottom_same_entry.sameEntry.sameAddr
          simp_all[Event.sameAddr]
        . case a =>
          apply Behaviour.event_at_same_entry_correspond_to_egdown_also_at_gCacheOfCDir
          . case hcdir_is_dir => exact hcdir_is_dir
          . case hcdir_corr_gdown => exact hcdir_corr_gdown
          . case he_same_entry_cdir => exact hinter_bottom_same_entry.sameEntry
        . case a => exact hgdown_encap_inter
  . case isBottomPred =>
    apply Behaviour.directory_event_is_bottom
    . case a =>
      apply Behaviour.event_at_same_entry_as_cdir_correspond_to_gdown_is_directory_event
      . case hpred_corr_to_gdown => exact hpred.choose_spec.right.finishBefore.gCacheOfCDir
      . case hcdir_is_dir => exact hcdir_is_dir
      . case hcdir_corr_gdown => exact hcdir_corr_gdown
  . case isBottomSucc => exact Behaviour.directory_event_is_bottom n b e_cdir (by simp[hcdir_is_dir])

-- consider the immediate successor event encapsulated in e_gdown.
lemma Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event {b init e_gdown}
  -- (hcdir_first_event_at_dir : )
  (e_cdir : Event n)
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_same_addr_gdown : e_cdir.sameAddr n e_gdown)
  (hcdir_in_b : e_cdir ∈ b)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
  (hcdir_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown e_cdir (Event.protocol n))
  (h : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (hgdown_in_b : e_gdown ∈ b) (hgdown_encap_cdir : Event.Encapsulates n e_gdown e_cdir)
  : stateBefore n b (InitialSystemState.stateAt n init e_cdir) e_cdir
    =
    eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
    (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))
  := by
  /- show the set of events from `immediateFinishesBeforeAtClusterDirectoryEventsNotEncap` is the same as the list of events before `e_cdir`.
  Need some assumptions;
  1. ∀ `e`, `e_gdown.Encapsulates e`, `e_cdir`.OrderedBefore `e`. (or anything equivalent to saying this `e_cdir` is the first encap'd dir event.)
  Then (likely in a few helper lemmas) show that if there are no events in set `immediateFinishesBeforeAtClusterDirectoryEventsNotEncap`, then
  the list of events before `e_cdir` is empty. -/
  simp[stateBefore]

  simp[immediateFinishesBeforeAtClusterDirectoryEventsNotEncap]
  have himm_finish_before_subsingleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_subsingleton n b e_gdown
  by_cases Nonempty (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown)
  . case pos himm_finish_nonempty =>
    simp[] at himm_finish_nonempty
    simp[immediateFinishesBeforeAtClusterDirectoryEventsNotEncap] at himm_finish_nonempty

    let e_pred := himm_finish_nonempty.choose
    have hpred_same_entry_cdir : e_pred.sameEntry n e_cdir :=
      Behaviour.cluster_directory_matching_global_cache_same_entry n hcdir_is_dir hcdir_matching_cluster himm_finish_nonempty
    -- show `e_pred` is the immediate predecessor to `e_cdir`
    have hpred_imm_pred_e_cdir : ImmediateBottomPredecessor n b e_pred e_cdir := by
      apply Behaviour.immediateBottomPredecessor_of_immediateFinishesBeforeAtClusterDirectoryNotEncap_and_matchingCluster_encap n
      . case hcdir_is_dir => exact hcdir_is_dir
      . case hcdir_in_b => exact hcdir_in_b
      . case hcdir_same_addr_gdown => exact hcdir_same_addr_gdown
      . case h => exact h
      . case hcdir_matching_cluster => exact hcdir_matching_cluster
      . case hcdir_corr_gdown => exact hcdir_corr_gdown
      . case hgdown_encap_cdir => exact hgdown_encap_cdir

    rw [Behaviour.upTo_immediatePredecessor_eq n hpred_imm_pred_e_cdir]

    rw[Behaviour.immediate_finishes_before_cluster_not_encap_singleton_of_nonempty_and_subsingleton n himm_finish_before_subsingleton himm_finish_nonempty]

    rw[Set.toOption_singleton'' himm_finish_nonempty.choose]
    (
    show {himm_finish_nonempty.choose} = {himm_finish_nonempty.choose}
    rfl)

    simp[eventToEntryState, stateAfter]

    have := InitialSystemState.same_entry_eq
    rw[InitialSystemState.same_entry_eq n hpred_same_entry_cdir]
  . case neg himm_finish_empty =>
    rw [Set.not_nonempty_iff_eq_empty'] at himm_finish_empty
    rw[← immediateFinishesBeforeAtClusterDirectoryEventsNotEncap]
    rw[himm_finish_empty]
    simp[eventToEntryState, Set.toOption]

    have hcdir_same_addr_gdown : Event.sameAddr n e_cdir e_gdown := by
      have := hcdir_matching_cluster.sameAddr
      simp_all[Event.sameAddr, ]
    rw[Behaviour.eventsUpToEvent_eq_nil_of_empty_finishes_before_events n
      hcdir_in_b hcdir_is_dir hcdir_same_addr_gdown hcdir_corr_gdown hgdown_in_b hgdown_encap_cdir h himm_finish_empty]
    simp [List.stateAfter]

    -- show initial states are the same
    apply Behaviour.InitialSystemState_eq_of_cluster_directory_corresponding_to_global_cache
    . case hdir_is_dir => exact hcdir_is_dir
    . case hcdir_matching_cluster => exact hcdir_matching_cluster
