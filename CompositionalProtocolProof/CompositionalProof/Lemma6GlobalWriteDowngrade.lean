import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompositionalProof.ProofBasic

variable (n : Nat)

/-
Assume the Initial State / Current State satisfies Compound SWMR.
  (Must define a version of Compound SWMR for InitialSystemState)
For any global SW downgrade cache event `e_gdown`:
1. the corresponding Cluster Directory state is ≤ the state after `e_gdown`.
2. the corresponding Cluster is in SWMR. (techinically have this by an Axiom)
-/

def CompoundProtocol.globalCidToProtocol (cmp : CompoundProtocol n) (g_cid : Fin 2) : Protocol n := match g_cid with
  | 0 => cmp.cluster1
  | 1 => cmp.cluster2

def ProtocolCacheInstance.globalCacheEventCid (pci : ProtocolCacheInstance n) : Fin 2 := match pci with
  | .globalP fin_2 => fin_2
  | .cluster1 _ => 3 -- Attempt to be smart; Using a value that's not a Fin 2 should produce an error.
  | .cluster2 _ => 3 -- panic! "Error: Expected a Global Cache Event, not a Cluster Cache Event!"

def CacheEvent.globalCacheEventCid (ce_greq : CacheEvent n) : Fin 2 := match ce_greq.cid with
  | .cache p_cache_inst => p_cache_inst.globalCacheEventCid
  | .proxy _ => 3

def Event.globalCacheEventCid (e_greq : Event n) : Fin 2 := match e_greq with
  | .cacheEvent ce => ce.globalCacheEventCid
  | .directoryEvent _ => 3

def CompoundProtocol.clusterProtocolCorrespondingToGlobalProtocol (cmp : CompoundProtocol n) (e_greq : Event n) : Protocol n :=
  cmp.globalCidToProtocol n (e_greq.globalCacheEventCid n)

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

lemma Behaviour.contradiction_of_directory_event_ends_eq {de de2}
  {he_eq_cdir_end : Event.oEnd n (Event.directoryEvent de) = Event.oEnd n (Event.directoryEvent de2) }
  {hde_ob_cdir : DirectoryEvent.OrderedBefore n de de2}
  : False := by
  simp[DirectoryEvent.OrderedBefore] at hde_ob_cdir
  have hde_before_cdir_end : de.oEnd < de2.oEnd := by
    calc de.oEnd < de2.oStart := hde_ob_cdir
      _ < de2.oEnd := de2.oWellFormed
  absurd hde_before_cdir_end
  simp[Nat.le_iff_lt_or_eq,]
  apply Or.intro_right
  simp[Event.oEnd] at he_eq_cdir_end
  simp[he_eq_cdir_end]

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
            apply Behaviour.contradiction_of_directory_event_ends_eq
            . case he_eq_cdir_end => exact he_eq_cdir_end
            . case hde_ob_cdir => exact hde_ob_cdir
          . case inr hcdir_ob_de =>
            apply Behaviour.contradiction_of_directory_event_ends_eq
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

/-- A coherent write downgrade at a cache will have a resulting state of I. -/
lemma Behaviour.stateAfter_fwd_sw_downgrade_eq_i {b init_entry_state}
  {e_gdown : Event n} (hcache : e_gdown.isCacheEvent) (hdown : e_gdown.down) (hsc_write : e_gdown.isSCWrite)
  : (Behaviour.stateAfter n b init_entry_state e_gdown) = Sum.inl I := by
  simp[Behaviour.stateAfter]
  /- Induct on the list, events up to event, unfold List.stateAfter.
  Show that the state after an `e_gdown` (fwded sc write downwgrade) is always I.  -/
  induction eventsUpToEvent n b e_gdown generalizing init_entry_state with
  | nil =>
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    match e_gdown with
    | .cacheEvent ce =>
      simp[Event.down] at hdown
      simp[CacheEvent.SucceedingState, hdown]
      /- Show the result of the global downgrade `e_gdown` is `I`. -/
      simp[ValidRequest.DowngradeState]

      simp[Event.isSCWrite, Event.req, ValidRequest.isSCWrite] at hsc_write
      simp only [hsc_write, ]
      simp only [ValidRequest.MRS, ReadWrite.toPerms, ReadWrite.toRWPerms]
      /- No matter what the previous state is, this fwd SC get SW `e_gdown` invalidates this cache. -/

      match EntryState.cache n init_entry_state with
      | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .wr, false⟩ | ⟨some .r, false⟩ | ⟨none, false⟩ | ⟨none, true⟩ =>
        all_goals simp [LE.le, State.le, LT.lt, Option.le]
    | .directoryEvent _ => simp[Event.isCacheEvent] at hcache
  | cons h tail ih => simp [List.stateAfter, ih]

lemma Behaviour.stateAfter_get_sw_immediately_put_sw_at_directory_eq_i {b : Behaviour n}
  {e_cdir_get_sw e_cdir_put_sw : Event n} (init_entry_state : EntryState n)
  (hget_put_same_requester : e_cdir_get_sw.directoryEventSameRequester n e_cdir_put_sw)
  (hget_then_immediate_put : b.ImmediateBottomPredecessor n e_cdir_get_sw e_cdir_put_sw)
  (hget_dir : e_cdir_get_sw.isDirectoryEvent) (hget_not_down : ¬ e_cdir_get_sw.down) (hget_sc_write : e_cdir_get_sw.isSCWrite)
  (hput_dir : e_cdir_put_sw.isDirectoryEvent) (hput_down : e_cdir_put_sw.down) (hput_sc_write : e_cdir_put_sw.isSCWrite)
  : (Behaviour.stateAfter n b init_entry_state e_cdir_put_sw) = Sum.inr (DirI n) := by
  simp[Behaviour.stateAfter]
  rw[Behaviour.upTo_immediatePredecessor_eq n hget_then_immediate_put]

  induction eventsUpToEvent n b e_cdir_get_sw generalizing init_entry_state with
  | nil =>
    simp[List.stateAfter]
    nth_rw 2 [Event.SucceedingState.eq_def]
    match e_cdir_get_sw with
    | .directoryEvent de_get =>
      simp -- show state at directory is SW, then downgrade/put sets it to I.
      simp[DirectoryEvent.SucceedingState]
      simp[Event.down] at hget_not_down
      simp[hget_not_down]
      simp [Event.isSCWrite, Event.req, ValidRequest.isSCWrite] at hget_sc_write
      simp[hget_sc_write]

      nth_rw 1 [Event.SucceedingState.eq_def]
      match e_cdir_put_sw with
      | .directoryEvent de_put =>
        simp [EntryState.directory]
        simp[DirectoryEvent.SucceedingState]
        simp[Event.down] at hput_down
        simp[hput_down]
        simp [Event.isSCWrite, Event.req, ValidRequest.isSCWrite] at hput_sc_write
        simp[hput_sc_write]

        simp[Event.directoryEventSameRequester, DirectoryEvent.sameRequester] at hget_put_same_requester
        simp [hget_put_same_requester]
      | .cacheEvent _ => simp[Event.isDirectoryEvent] at hput_dir
    | .cacheEvent _ => simp[Event.isDirectoryEvent] at hget_dir
  | cons head l_tail ih =>
    simp only [ List.cons_append, List.stateAfter ]
    apply ih

lemma CompoundProtocol.global_sc_write_downgrade_le_cluster_dir_state {cluster_p_of_gdown}
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_write_spec : Event.isSCWriteGlobalDowngrade n e_gdown)
  (hgdown_translation : Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper n b init cluster_p_of_gdown e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp [Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper] at hgdown_translation
  let hwrite_down_translation := hgdown_translation.scGDownTranslation
  simp[Behaviour.encapCorrespondingGetSWAndEvictWrapper] at hwrite_down_translation
  let htranslation_spec := hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose_spec.right
  let dir_coh_evict := hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose
  let hdir_coh_evict_in_b := hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose_spec.left
  have htrans_coherent_evict_sw := htranslation_spec.cohEvict
  /- Now, this Coherent SW Evict's corresponding Directory Event is the last Directory Event that finishes before `e_gdown`.
  There are no others, -/
  simp[Behaviour.dirEventStateLeGlobalCacheState']
  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  have hevict_imm_finish_before_gdown := b.cluster_dir_event_immediately_finish_before_of_global_downgrade n
    hgdown_in_b hgdown htranslation_spec

  rw[Behaviour.event_immediate_finish_before_gdown_singleton n hdir_coh_evict_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' dir_coh_evict hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp
  /- show the state after the evict `e_shim_coh_evict` (in the ⋯) is always ≤ the state after `e_gdown`.
  `e_shim_coh_evict` brings the Cluster Directory state down to `I` (get SW then evict SW to I).
  `e_gdown` is a downgrade at the Global Cache (fwd get M / SW), and will bring the Global cache to `I`. -/
  /- are the `Behaviour.stateAfter` definitions easy to work with? Maybe I need helper lemmas to make
  definitions like `stateAfter` easier to work with -/
  rw[Behaviour.stateAfter_fwd_sw_downgrade_eq_i n hgdown.isGlobal.reqAtCache hgdown.isDown hgdown_write_spec.isSCWrite]
  -- Now show the state after the Coherent Evict sent to the directory `e_shim_coh_evict` results in I state.
  have hcoh_write_immediate_evict := htranslation_spec.cohWriteImmBeforeEvict
  /- Coherent Write at Directory Event is a directory event-/
  have hcoh_write_dir := htranslation_spec.cohWriteDir.isDir

  let coh_write := hwrite_down_translation.choose
  have hcoh_write_not_down := htranslation_spec.cohWrite.downgrade
  have hcoh_write_dir_down_eq_coh_write_down := htranslation_spec.cohWriteDir.dirCorresponds.sameDown
  /- Coherent Write Directory Event is not a downgrade -/
  have hcoh_write_dir_not_down : ¬ hwrite_down_translation.choose_spec.right.choose.down := by
    simp[hcoh_write_dir_down_eq_coh_write_down, hcoh_write_not_down]

  have hcoh_write_dir_req_eq_coh_write_req := htranslation_spec.cohWriteDir.dirCorresponds.dirReq
  simp[Behaviour.reqToDirOfRequestEvent] at hcoh_write_dir_req_eq_coh_write_req
  have hcoh_write_req := htranslation_spec.cohWrite.reqTranslation
  simp[ValidRequest.isSCWrite] at hcoh_write_req
  simp[hcoh_write_req] at hcoh_write_dir_req_eq_coh_write_req
  simp [Event.reqToDirOfRequestEvent] at hcoh_write_dir_req_eq_coh_write_req
  simp[hcoh_write_req] at hcoh_write_dir_req_eq_coh_write_req
  /- Coherent Write Directory Event is a SC Write. -/
  have hcoh_write_dir_sc_write : hwrite_down_translation.choose_spec.right.choose.isSCWrite := by
    simp[Event.isSCWrite,ValidRequest.isSCWrite, hcoh_write_dir_req_eq_coh_write_req]

  /- Coherent Evict at Directory is a directory event-/
  have hcoh_evict_dir := htranslation_spec.cohEvictDir.isDir

  have hcoh_evict_down := htranslation_spec.cohEvict.downgrade
  have hcoh_evict_dir_down_eq_coh_evict_down := htranslation_spec.cohEvictDir.dirCorresponds.sameDown
  /- Coherent Evict at Directory is a downgrade -/
  have hcoh_evict_dir_down : hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose.down := by
    simp[hcoh_evict_dir_down_eq_coh_evict_down, hcoh_evict_down]

  /- Coherent Write Directory Event is a SC Write. -/
  have hcoh_evict_dir_req_eq_coh_evict_req := htranslation_spec.cohEvictDir.dirCorresponds.dirReq
  simp[Behaviour.reqToDirOfRequestEvent] at hcoh_evict_dir_req_eq_coh_evict_req
  have hcoh_evict_req := htranslation_spec.cohEvict.reqTranslation
  simp[ValidRequest.isSCWrite] at hcoh_evict_req
  simp[hcoh_evict_req] at hcoh_evict_dir_req_eq_coh_evict_req
  simp [Event.reqToDirOfRequestEvent] at hcoh_evict_dir_req_eq_coh_evict_req
  simp[hcoh_evict_req] at hcoh_evict_dir_req_eq_coh_evict_req
  /- Coherent Write Directory Event is a SC Write. -/
  have hcoh_evict_dir_sc_write : hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose.isSCWrite := by
    simp[Event.isSCWrite,ValidRequest.isSCWrite, hcoh_evict_dir_req_eq_coh_evict_req]

  -- have test := hwrite_down_translation.choose_spec.right.choose
  -- have test := hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose

  let hget_dir := hwrite_down_translation.choose_spec.right.choose -- .directoryEventSameRequester
  let hput_dir := hwrite_down_translation.choose_spec.right.choose_spec.choose_spec.right.choose

  have hget_dir_same_requester_put_dir : hget_dir.directoryEventSameRequester n hput_dir
    := Behaviour.cluster_dir_events_same_requester_of_global_sc_downgrade n hgdown_in_b hgdown htranslation_spec

  simp[Behaviour.eventToEntryState]

  rw[Behaviour.stateAfter_get_sw_immediately_put_sw_at_directory_eq_i
      n (InitialSystemState.stateAt n init dir_coh_evict) hget_dir_same_requester_put_dir htranslation_spec.cohWriteImmBeforeEvict hcoh_write_dir hcoh_write_dir_not_down hcoh_write_dir_sc_write
      hcoh_evict_dir hcoh_evict_dir_down hcoh_evict_dir_sc_write
    ]

  simp[EntryState.state,DirectoryState.toState, EntryState.cache, LE.le, State.le]

/- ---------------- Global SC Read Downgrade Specific cases. --------------- -/
--[Work in progress]!
lemma Behaviour.global_mr_downgrade_dir_evict_has_no_intermediate {cluster_p_of_gdown} {b : Behaviour n} {init : InitialSystemState n}
  {e_gdown e_shim_coh_read e_dir_shim_coh_read : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_mr_down_translation : Behaviour.encapCorrespondingGetMR n b init cluster_p_of_gdown e_gdown e_shim_coh_read e_dir_shim_coh_read)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_coh_read e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  have honly_encap_get_mr_dir := hfwd_mr_down_translation.onlyReadDir
  intro e_inter hinter_in_b hinter_finishes_btn_read_and_gdown
  have hdir_read_same_struct_inter := hinter_finishes_btn_read_and_gdown.sameCidInterPred
  match hdir_read : e_dir_shim_coh_read, hinter : e_inter with
  | .directoryEvent de_dir_read , .directoryEvent de_inter =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_read de_inter
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_read_ob_inter =>
      -- can't have another event between dir_read and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        constructor
        . case clusterMatch =>
          constructor
          . case sameAddr =>
            simp[Event.sameAddr]
            rw[hinter, hinter_finishes_btn_read_and_gdown.sameAddr]
            rw[← hfwd_mr_down_translation.cohReadDir.dirCorresponds.sameAddr]
            simp[← Event.sameAddr.eq_1, hfwd_mr_down_translation.cohRead.atCorrClusterProxy.clusterMatch.sameAddr]
          . case atCorrCluster =>
            have hdir_read_corr_cluster := Behaviour.global_downgrade_cache_translation_encap_corresponding_request n hgdown
              hfwd_mr_down_translation.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
              hfwd_mr_down_translation.cohReadDir.sameProtocol
              hfwd_mr_down_translation.cohReadDir.isDir
            simp[Event.reqAtCorrespondingGCacheOfCDir] at hdir_read_corr_cluster
            simp[Event.correspondingClusterOfGlobalCache]

            simp[Event.protocol] at hdir_read_corr_cluster
            match hdir_read_pi : de_dir_read.pInst with
            | .global | .cluster2 | .cluster1 =>
              simp[hdir_read_pi] at hdir_read_corr_cluster
              try (
              simp[Event.reqAtGlobalCacheCid] at hdir_read_corr_cluster
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
                    simp[Event.struct] at hdir_read_same_struct_inter
                    rw[hdir_read_same_struct_inter]
                    exact hdir_read_pi)
                | .proxy pi => simp[hcegdown_cid] at hdir_read_corr_cluster
              | .directoryEvent _ => simp at hdir_read_corr_cluster
              )
        . case atDir => simp [Event.isDirectoryEvent, hinter]
        . case globalEncap =>
          simp[Event.Encapsulates]
          apply And.intro
          . case left =>
            simp [DirectoryEvent.OrderedBefore] at hdir_read_ob_inter
            calc e_gdown.oStart < e_shim_coh_read.oStart := hfwd_mr_down_translation.cohRead.globalEncap.left
                _ < e_dir_shim_coh_read.oStart := by simp[hdir_read, hfwd_mr_down_translation.cohReadDir.reqEncapDir.left]
                _ < e_dir_shim_coh_read.oEnd := e_dir_shim_coh_read.oWellFormed
                _ < e_inter.oStart := by simp[hdir_read, hinter, Event.oEnd, Event.oStart, hdir_read_ob_inter]
          . case right => simp[← Event.finishesBefore.eq_def, hinter, hinter_finishes_btn_read_and_gdown.interSucc]
      have hinter_is_dir_read := honly_encap_get_mr_dir e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      /- by `hinter_is_dir_read`, we know the only encapsulated events in the downgrade at the corresponding cluster is the Get MR Access.
      Absurd that `e_inter` finishes before itself-/
      absurd hinter_finishes_btn_read_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_right
      rw[hinter] at hinter_is_dir_read
      rw[hinter_is_dir_read]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_finishes_btn_read_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc de_inter.oEnd < de_dir_read.oStart := hinter_ob_dir_evict
        _ < de_dir_read.oEnd := de_dir_read.oWellFormed
  | .cacheEvent ce_dir_evict , .directoryEvent de_inter
  | .directoryEvent de_dir_evict , .cacheEvent ce_inter
  | .cacheEvent ce_dir_evict , .cacheEvent ce_inter =>
    have hdir_read_dir := hfwd_mr_down_translation.cohReadDir.isDir
    simp[Event.struct] at hdir_read_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_read_dir

lemma Behaviour.cluster_dir_event_immediately_finish_before_of_global_read_downgrade
  {b : Behaviour n} {init : InitialSystemState n} {cluster_p_of_gdown} {e_gdown e_shim_coh_read e_dir_shim_coh_read : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_mr_down_translation : Behaviour.encapCorrespondingGetMR n b init cluster_p_of_gdown e_gdown e_shim_coh_read e_dir_shim_coh_read)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_coh_read e_gdown := by
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
        calc e_dir_shim_coh_read.oEnd < e_shim_coh_read.oEnd := hfwd_mr_down_translation.cohReadDir.reqEncapDir.right
          _ < e_gdown.oEnd := hfwd_mr_down_translation.cohRead.globalEncap.right
      . case sameAddr =>
        simp[Event.sameAddr, Eq.comm]
        calc e_gdown.addr = e_shim_coh_read.addr := hfwd_mr_down_translation.cohRead.atCorrClusterProxy.clusterMatch.sameAddr
          _ = e_dir_shim_coh_read.addr := hfwd_mr_down_translation.cohReadDir.dirCorresponds.sameAddr
      . case predInB => simp[hfwd_mr_down_translation.cohReadDir.dirInB]
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_mr_down_translation.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => exact hfwd_mr_down_translation.cohReadDir.sameProtocol
      . case hdir_is_dir => exact hfwd_mr_down_translation.cohReadDir.isDir
  . case noIntermediate =>
    -- [TODO] create version of `mr` instead of `sw` below.
    apply Behaviour.global_mr_downgrade_dir_evict_has_no_intermediate
    . case hgdown => exact hgdown
    . case hfwd_mr_down_translation => exact hfwd_mr_down_translation

lemma Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore {b e init_state}
  : (List.stateAfter n (eventsUpToEvent n b e ++ [e]) init_state) = ([e].stateAfter n (stateBefore n b init_state e))
  := by
  simp [stateBefore]
  induction eventsUpToEvent n b e generalizing init_state with
  | nil => simp[List.stateAfter]
  | cons head l_tail ih =>
    rw[List.cons_append]
    nth_rw 3 [List.stateAfter]
    nth_rw 1 [List.stateAfter]
    apply ih

lemma Behaviour.state_after_cluster_dir_sc_read_le_state_after_global_read_downgrade_of_cmp_swmr
  {state_before_e_dir state_before_gdown : EntryState n} {e_dir_coh_read : Event n}
  {e_gdown : Event n} (hsc_read : e_gdown.isSCRead)
  (hgdown : e_gdown.isGlobalDowngrade)
  -- (hgdown_in_b : e_gdown ∈ b)
  (hdir_is_dir : e_dir_coh_read.isDirectoryEvent)
  (hdir_not_down : ¬ e_dir_coh_read.down)
  (hdir_req : e_dir_coh_read.req.isSCRead)
  -- (hprev_cluster_state_le_gdown_state_before : EntryState.state n state_before_e_dir ≤ EntryState.cache n state_before_gdown)
  (hstate_before_e_dir_is_dir_state : state_before_e_dir.isDirectoryState)
  (hstate_before_gdown_is_cache_state : state_before_gdown.isCacheState)
  (hstate_before_gdown : state_before_gdown.cache = SW)
  : EntryState.state n (List.stateAfter n [e_dir_coh_read] state_before_e_dir) ≤ EntryState.cache n (List.stateAfter n [e_gdown] state_before_gdown)
  := by
  simp[List.stateAfter]
  have hgdown_cache := hgdown.isGlobal.reqAtCache
  match e_dir_coh_read, e_gdown with
  | .directoryEvent de, .cacheEvent ce =>
    match state_before_gdown with
    | .inl cache_s_before_gdown =>
      simp [EntryState.cache] at hstate_before_gdown
      rw[hstate_before_gdown]
      nth_rw 2 [Event.SucceedingState.eq_def]
      simp
      simp[CacheEvent.SucceedingState]
      -- rewrite so the state before `e_gdown` is SW

      have hgdown_down := hgdown.isDown
      simp [Event.down] at hgdown_down
      simp[hgdown_down]
      -- simp and get to the determine the (downgrade) succeeding state after `e_gdown`

      simp[ValidRequest.DowngradeState]

      have hgdown_sc_read := hsc_read
      simp[Event.isSCRead, Event.req, ValidRequest.isSCRead] at hgdown_sc_read

      simp [hgdown_sc_read]
      simp[EntryState.cache, ValidRequest.MRS, SW, ReadWrite.toPerms, ReadWrite.toRWPerms,]
      -- substitue in the downgrade request as a Fwd SC Read Downgrade

      match state_before_e_dir with
      | .inl s => simp [EntryState.isDirectoryState] at hstate_before_e_dir_is_dir_state
      | .inr ds =>
        nth_rw 1 [Event.SucceedingState.eq_def]
        simp[EntryState.directory]
        simp[DirectoryEvent.SucceedingState]
        simp[Event.down] at hdir_not_down
        simp[Event.req, ValidRequest.isSCRead] at hdir_req

        simp[hdir_not_down, hdir_req]
        simp[EntryState.state, DirectoryState.toState]
        simp[LE.le, State.le, I]
        simp[LT.lt, State.lt, LE.le, Option.le]
    | .inr _ => simp [EntryState.isCacheState] at hstate_before_gdown_is_cache_state
  | .cacheEvent _, .directoryEvent _
  | .directoryEvent _, .directoryEvent _
  | .cacheEvent _, .cacheEvent _
    => simp[Event.isDirectoryEvent, Event.isCacheEvent] at hdir_is_dir hgdown_cache

lemma Behaviour.stateAfter_directory_event_is_directory_state {b init_state e_dir_coh_read} {es : List (Event n)} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  (hall_dir : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e_dir_coh_read) (Event.addr n e_dir_coh_read))
  : (List.stateAfter n es init_state).isDirectoryState := by
  simp[EntryState.isDirectoryState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isDirectoryState.eq_def]
    exact hinit_dir
  | cons head tail ih =>
    apply ih
    . case cons.hinit_dir =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_dir head (by simp) |>.eAtStruct
      match head with
      | .directoryEvent de => simp[EntryState.isDirectoryState]
      | .cacheEvent _ =>
        match e_dir_coh_read with
        | .directoryEvent _ => simp [Event.struct] at hhead_of_dir
        | .cacheEvent _ => simp[Event.isDirectoryEvent] at hdir_is_dir
    . case cons.hall_dir =>
      intro e' he'_in_tail
      apply hall_dir
      . case a => simp[he'_in_tail]

lemma Behaviour.stateBefore_dir_event_is_dir_state {b init_state e_dir_coh_read} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  : (stateBefore n b init_state e_dir_coh_read).isDirectoryState := by
  simp[stateBefore]
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_coh_read
  apply Behaviour.stateAfter_directory_event_is_directory_state
  . case hdir_is_dir => exact hdir_is_dir
  . case hinit_dir => exact hinit_dir
  . case hall_dir => exact hall_dir

lemma Behaviour.stateAfter_cache_event_is_cache_state {b init_state e} {es : List (Event n)} (he_is_cache : e.isCacheEvent) (hinit_cache : init_state.isCacheState)
  (hall_at_entry : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e) (Event.addr n e))
  : (List.stateAfter n es init_state).isCacheState := by
  simp[EntryState.isCacheState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isCacheState.eq_def]
    exact hinit_cache
  | cons head tail ih =>
    apply ih
    . case cons.hinit_cache =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_at_entry head (by simp) |>.eAtStruct
      match head with
      | .cacheEvent _ => simp[EntryState.isCacheState]
      | .directoryEvent _ =>
        match e with
        | .directoryEvent _ => simp[Event.isCacheEvent] at he_is_cache
        | .cacheEvent _ => simp [Event.struct] at hhead_of_dir
    . case cons.hall_at_entry =>
      intro e' he'_in_tail
      apply hall_at_entry
      . case a => simp[he'_in_tail]

lemma Behaviour.stateBefore_cache_event_is_cache_state {b init_state e} (he_is_cache : e.isCacheEvent) (hinit_cache : init_state.isCacheState)
  : (stateBefore n b init_state e).isCacheState := by
  simp[stateBefore]
  have hall_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e
  apply Behaviour.stateAfter_cache_event_is_cache_state
  . case he_is_cache => exact he_is_cache
  . case hinit_cache => exact hinit_cache
  . case hall_at_entry => exact hall_at_entry

lemma Behaviour.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade {b : Behaviour n} {init : InitialSystemState n} {e_dir_coh_read : Event n}
  {e_gdown : Event n} (hsc_read : e_gdown.isSCRead) (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_in_b : e_gdown ∈ b)
  (hstateBefore_gdown_sw : b.cacheStateMadeOn n init e_gdown = SW)
  (hdir_is_dir : e_dir_coh_read.isDirectoryEvent)
  (hdir_not_down : ¬ e_dir_coh_read.down)
  (hdir_get_mr : e_dir_coh_read.req.isSCRead)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_coh_read) e_dir_coh_read) ≤
  EntryState.cache n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_gdown) e_gdown)
  -- EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_coh_read) e_dir_coh_read) ≤
  -- EntryState.cache n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_gdown) e_gdown)
  := by
  /-
  have hprev_cluster_state_satisfies_cmp_swmr := hprev_cluster_state_cmp_swmr e_gdown hgdown_in_b hgdown.isGlobal
  simp[Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR'] at hprev_cluster_state_satisfies_cmp_swmr
  have hprev_cluster_state_satisfies_cmp_swmr' := hprev_cluster_state_satisfies_cmp_swmr /-hgdown_in_b-/ hgdown.isGlobal
  have hprev_cluster_state_le_gdown_state_before := hprev_cluster_state_satisfies_cmp_swmr'.stateAfterLeGlobalCache
  simp[dirEventState.Before.LeGlobalCacheState', Behaviour.latestDirectoryState.Before.GlobalCache] at hprev_cluster_state_le_gdown_state_before
  simp[stateOfSubsingletonEventSet] at hprev_cluster_state_le_gdown_state_before

  -- something like this [TODO]: make it specific to e_dir_coh_read
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n e_dir_coh_read] at hprev_cluster_state_le_gdown_state_before
  -/

  simp[Behaviour.stateAfter]
  -- state after events up to event
  rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]
  rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]

  -- Now we can work through the cases. The state before `e_dir_coh_read` is always ≤ the state before `e_gdown`.
  apply Behaviour.state_after_cluster_dir_sc_read_le_state_after_global_read_downgrade_of_cmp_swmr
  . case hsc_read => exact hsc_read
  . case hgdown => exact hgdown
  . case hdir_is_dir => exact hdir_is_dir
  . case hdir_not_down => exact hdir_not_down
  . case hdir_req => exact hdir_get_mr
  . case hstate_before_e_dir_is_dir_state =>
    apply Behaviour.stateBefore_dir_event_is_dir_state
    . case hdir_is_dir => exact hdir_is_dir
    . case hinit_dir =>
      simp [InitialSystemState.stateAt]
      match e_dir_coh_read with
      | .directoryEvent _ => simp [EntryState.isDirectoryState]
      | .cacheEvent _ => simp[Event.isDirectoryEvent] at hdir_is_dir
  . case hstate_before_gdown_is_cache_state =>
    apply Behaviour.stateBefore_cache_event_is_cache_state
    . case he_is_cache => exact hgdown.isGlobal.reqAtCache
    . case hinit_cache =>
      simp [InitialSystemState.stateAt]
      match e_gdown with
      | .cacheEvent _ => simp [EntryState.isCacheState]
      | .directoryEvent _ =>
        have hgdown_is_cache := hgdown.isGlobal.reqAtCache
        simp[Event.isCacheEvent] at hgdown_is_cache
  . case hstate_before_gdown =>
    simp [cacheStateMadeOn] at hstateBefore_gdown_sw
    simp[hstateBefore_gdown_sw]

lemma CompoundProtocol.global_sc_read_downgrade_le_cluster_dir_state {cluster_p_of_gdown}
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_read_spec : Event.isSCReadGlobalDowngrade n e_gdown)
  (hgdown_on_sw : Behaviour.cacheStateMadeOn n b init e_gdown = SW)
  (hgdown_translation : Behaviour.Shim.Global.bothWriteRead.SCReadDownTranslation n b init cluster_p_of_gdown e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right

  -- use `Behaviour.cluster_dir_event_immediately_finish_before_of_global_read_downgrade` here.
  have hevict_imm_finish_before_gdown := b.cluster_dir_event_immediately_finish_before_of_global_read_downgrade n
    hgdown_in_b hgdown htranslation_spec
  let e_dir_coh_read := hgdown_translation.choose_spec.right.choose
  let e_dir_coh_get_mr_in_b := htranslation_spec.cohReadDir.dirInB
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_coh_get_mr_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]

  /- Simp into the state after the coherent read is ≤ the state after the coherent read downgrade. -/
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' e_dir_coh_read hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp

  /- State that Get MR Dir is not a downgrade and is a SC Read -/
  apply Behaviour.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade
  . case hsc_read => exact hgdown_read_spec.isSCWrite
  . case hgdown => exact hgdown
  . case hgdown_in_b => exact hgdown_in_b
  . case hstateBefore_gdown_sw => exact hgdown_on_sw
  . case hdir_is_dir => exact htranslation_spec.cohReadDir.isDir
  . case hdir_not_down =>
    simp[e_dir_coh_read, htranslation_spec.cohReadDir.dirCorresponds.sameDown]
    have hproxy_get_mr := htranslation_spec.cohRead.downgrade
    simp at hproxy_get_mr
    simp[hproxy_get_mr]
  . case hdir_get_mr =>
    have hget_mr_dir_same_req_as_proxy := htranslation_spec.cohReadDir.dirCorresponds.dirReq
    simp[e_dir_coh_read, htranslation_spec.cohReadDir.dirCorresponds.dirReq]
    simp[Behaviour.reqToDirOfRequestEvent]
    have hproxy_get_mr := htranslation_spec.cohRead.reqTranslation
    simp[ValidRequest.isSCRead] at hproxy_get_mr
    simp[hproxy_get_mr]

    simp[Event.reqToDirOfRequestEvent]
    simp[hproxy_get_mr]
    simp[ValidRequest.isSCRead]

/- adding lemmas for Case `noCoherentRead`, `SC Write Downgrade` on `SW` state. -/

lemma Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade {b : Behaviour n} {init : InitialSystemState n}
  {e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_vc_down e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  intro e_inter hinter_in_b hinter_btn_vcInval_and_gdown

  have hdir_vc_same_struct_inter := hinter_btn_vcInval_and_gdown.sameCidInterPred
  match hdir_vc : e_dir_shim_vc_down, hinter : e_inter with
  | .directoryEvent de_dir_vc_down , .directoryEvent de_inter =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_vc_down de_inter
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_vc_ob_inter =>
      -- can't have another event between dir_evict and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      -- have test : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := hfwd_sw_down_translation.
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        constructor
        . case clusterMatch =>
          constructor
          . case sameAddr =>
            simp[Event.sameAddr]
            rw[hinter, hinter_btn_vcInval_and_gdown.sameAddr]
            rw[← hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
          . case atCorrCluster =>
            have hdir_vcInval_corr_cluster := Behaviour.global_downgrade_cache_translation_encap_corresponding_request n hgdown
              hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
              (by rfl)
              hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
            simp[Event.reqAtCorrespondingGCacheOfCDir] at hdir_vcInval_corr_cluster
            simp[Event.correspondingClusterOfGlobalCache]

            simp[Event.protocol] at hdir_vcInval_corr_cluster
            match hdir_evict_pi : de_dir_vc_down.pInst with
            | .global => simp[hdir_evict_pi] at hdir_vcInval_corr_cluster
            | .cluster2 | .cluster1 =>
              simp[hdir_evict_pi] at hdir_vcInval_corr_cluster
              simp[Event.reqAtGlobalCacheCid] at hdir_vcInval_corr_cluster
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
                    simp[Event.struct] at hdir_vc_same_struct_inter
                    rw[hdir_vc_same_struct_inter]
                    exact hdir_evict_pi)
                | .proxy pi => simp[hcegdown_cid] at hdir_vcInval_corr_cluster
              | .directoryEvent _ => simp at hdir_vcInval_corr_cluster
        . case atDir => simp [Event.isDirectoryEvent, hinter]
        . case globalEncap =>
          simp[Event.Encapsulates]
          apply And.intro
          . case left =>
            simp [DirectoryEvent.OrderedBefore] at hdir_vc_ob_inter
            calc e_gdown.oStart < e_dir_shim_vc_down.oStart := by simp[hdir_vc, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.left]
                -- _ < e_dir_shim_vc_down.oStart := by simp[hdir_vc, hfwd_sw_down_translation.cohEvictDir.reqEncapDir.left]
                _ < e_dir_shim_vc_down.oEnd := e_dir_shim_vc_down.oWellFormed
                _ < e_inter.oStart := by simp[hdir_vc, hinter, Event.oEnd, Event.oStart, hdir_vc_ob_inter]
          . case right => simp[← Event.finishesBefore.eq_def, hinter, hinter_btn_vcInval_and_gdown.interSucc]
      have honly_encap_acq_vd_vc := hfwd_sw_down_translation.onlyAcqVdVcDir
      have hinter_is_dir_evict_or_dir_get := honly_encap_acq_vd_vc e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      cases hinter_is_dir_evict_or_dir_get
      . case inl hinter_eq_acq_dir =>
        -- contradiction, hinter is coh get SW dir event, that's immediately before coh put SW dir event.
        rw[hinter] at hinter_eq_acq_dir
        absurd hinter_btn_vcInval_and_gdown.interPred
        rw[hinter_eq_acq_dir]
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hinter_pred_dir_acq : Event.Predecessor n e_dir_shim_acq (Event.directoryEvent de_dir_vc_down) := by
          have hdir_acq_imm_pred_vd := hfwd_sw_down_translation.acqDirImmBeforeVdWBDir
          simp[ImmediateBottomPredecessor,] at hdir_acq_imm_pred_vd
          have hdir_acq_end_before_vd_start := hdir_acq_imm_pred_vd.isImmPred.bPred.isPred
          simp[Event.Predecessor, Event.OrderedBefore,] at hdir_acq_end_before_vd_start

          have hvd_imm_pred_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
          simp[ImmediateBottomPredecessor,] at hvd_imm_pred_vc
          have hvd_end_before_vc_start := hvd_imm_pred_vc.isImmPred.bPred.isPred
          simp[Event.Predecessor, Event.OrderedBefore,] at hvd_end_before_vc_start

          have := hdir_acq_end_before_vd_start
          simp[Event.Predecessor]
          calc e_dir_shim_acq.oEnd < e_dir_shim_vd_down.oStart := hdir_acq_end_before_vd_start
            _ < e_dir_shim_vd_down.oEnd := e_dir_shim_vd_down.oWellFormed
            _ < (Event.directoryEvent de_dir_vc_down).oStart := hvd_end_before_vc_start
        match e_dir_shim_acq with
        | .directoryEvent de_dir_acq =>
          simp[Event.Predecessor, Event.oEnd, Event.oStart] at hinter_pred_dir_acq
          simp[Event.oEnd]
          calc de_dir_acq.oEnd < de_dir_vc_down.oStart := hinter_pred_dir_acq
            _ < de_dir_vc_down.oEnd := de_dir_vc_down.oWellFormed
        | .cacheEvent _ =>
          have hacq_dir_is_dir := hfwd_sw_down_translation.acqDir.isDir
          simp[Event.isDirectoryEvent] at hacq_dir_is_dir
      . case inr hinter_eq_vd_or_vc =>
        cases hinter_eq_vd_or_vc
        . case inl hinter_eq_vd =>
          rw[hinter] at hinter_eq_vd
          absurd hinter_btn_vcInval_and_gdown.interPred
          rw[hinter_eq_vd]
          simp[Event.finishesBefore]
          simp[Nat.le_iff_lt_or_eq]
          apply Or.intro_left
          have hinter_imm_pred_dir_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
          simp[ImmediateBottomPredecessor,] at hinter_imm_pred_dir_vc
          have hinter_pred_dir_vc := hinter_imm_pred_dir_vc.isImmPred.bPred.isPred
          simp[Event.Predecessor, Event.OrderedBefore,] at hinter_pred_dir_vc
          match e_dir_shim_vd_down with
          | .directoryEvent de_dir_vd =>
            simp[Event.oEnd, Event.oStart] at hinter_pred_dir_vc
            simp[Event.oEnd]
            calc de_dir_vd.oEnd < de_dir_vc_down.oStart := hinter_pred_dir_vc
              _ < de_dir_vc_down.oEnd := de_dir_vc_down.oWellFormed
          | .cacheEvent _ =>
            have hvd_dir_is_dir := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
            simp[Event.isDirectoryEvent] at hvd_dir_is_dir
        . case inr hinter_eq_vc =>
        -- contradiction, dir evict event can't finish before itself!
        absurd hinter_btn_vcInval_and_gdown.interPred
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_right
        rw[hinter] at hinter_eq_vc
        rw[hinter_eq_vc]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_btn_vcInval_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc de_inter.oEnd < de_dir_vc_down.oStart := hinter_ob_dir_evict
        _ < de_dir_vc_down.oEnd := de_dir_vc_down.oWellFormed
  | .cacheEvent ce_dir_vc , .directoryEvent de_inter
  | .directoryEvent de_dir_vc , .cacheEvent ce_inter
  | .cacheEvent ce_dir_vc , .cacheEvent ce_inter =>
    have hdir_vc_dir := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
    simp[Event.struct] at hdir_vc_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_vc_dir

lemma Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_vc_down e_gdown := by
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore => simp[Event.finishesBefore, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.right]
      . case sameAddr =>
        simp[ Event.sameAddr,]
        apply Eq.symm
        simp[← Event.sameAddr.eq_def, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
      . case predInB => exact hvc_down_in_b
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => rfl
      . case hdir_is_dir => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
  . case noIntermediate =>
    apply Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade
    . case hgdown => exact hgdown
    . case hfwd_sw_down_translation => exact hfwd_sw_down_translation

/- Is there a better way to automate these 3 lemmas with similar conclusions? -/
lemma Behaviour.directory_vd_and_vc_downgrade_from_vd_state_le_i {b init e_gdown} {e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  : EntryState.state n
    (List.stateAfter n [e_dir_shim_vd_down, e_dir_shim_vc_down]
      (Sum.inr (DirectoryState.Vd ⟨Vd, DirectoryEvent.SucceedingState._proof_3⟩))) ≤
  EntryState.cache n (Sum.inl I) := by
  rw[List.stateAfter]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_vd_down with
  | .directoryEvent de_shim_vd_down =>
    simp [DirectoryEvent.SucceedingState]
    have hshim_vd_down_is_down := hfwd_sw_down_translation.gDownEncapVdWBDir.downgrade
    simp[Event.down] at hshim_vd_down_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hshim_vd_down_is_down]

    have hshim_vd_down_is_vd_req := hfwd_sw_down_translation.gDownEncapVdWBDir.reqTranslation
    simp[Event.req, ValidRequest.isNcWeakWrite] at hshim_vd_down_is_vd_req
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hshim_vd_down_is_vd_req]
    simp[EntryState.directory]

    -- Now resolve Shim Vc downgrade
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    match e_dir_shim_vc_down with
    | .directoryEvent de_shim_vc_down =>
      simp[DirectoryEvent.SucceedingState]
      have hshim_vc_down_is_down := hfwd_sw_down_translation.gDownEncapVcInvalDir.downgrade
      simp[Event.down] at hshim_vc_down_is_down
      -- resolve to the case that `e_vd_down` is indeed a downgrade
      simp[hshim_vc_down_is_down]

      have hshim_vc_down_is_vc_req := hfwd_sw_down_translation.gDownEncapVcInvalDir.reqTranslation
      simp[Event.req, ValidRequest.isNcWeakRead] at hshim_vc_down_is_vc_req
      -- resolve to case where we apply a Vd downgrade at the directory
      simp[hshim_vc_down_is_vc_req]
      simp[EntryState.directory]

      -- Now resolve Shim Vc downgrade
      simp[EntryState.state, EntryState.cache, DirectoryState.toState]
      simp[LE.le, State.le]
    | .cacheEvent _ =>
      have hshim_vc_down_is_dir := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
      simp[Event.isDirectoryEvent] at hshim_vc_down_is_dir
  | .cacheEvent _ =>
    have hshim_vd_down_is_dir := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    simp[Event.isDirectoryEvent] at hshim_vd_down_is_dir

lemma Behaviour.directory_vd_and_vc_downgrade_from_vd_state_le_i' {b init e_gdown} {e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  : EntryState.state n (List.stateAfter n [e_dir_shim_vd_down, e_dir_shim_vc_down] (Sum.inr (DirectoryState.Vd vd))) ≤
  EntryState.cache n (Sum.inl I) := by
  rw[List.stateAfter]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_vd_down with
  | .directoryEvent de_shim_vd_down =>
    simp [DirectoryEvent.SucceedingState]
    have hshim_vd_down_is_down := hfwd_sw_down_translation.gDownEncapVdWBDir.downgrade
    simp[Event.down] at hshim_vd_down_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hshim_vd_down_is_down]

    have hshim_vd_down_is_vd_req := hfwd_sw_down_translation.gDownEncapVdWBDir.reqTranslation
    simp[Event.req, ValidRequest.isNcWeakWrite] at hshim_vd_down_is_vd_req
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hshim_vd_down_is_vd_req]
    simp[EntryState.directory]

    -- Now resolve Shim Vc downgrade
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    match e_dir_shim_vc_down with
    | .directoryEvent de_shim_vc_down =>
      simp[DirectoryEvent.SucceedingState]
      have hshim_vc_down_is_down := hfwd_sw_down_translation.gDownEncapVcInvalDir.downgrade
      simp[Event.down] at hshim_vc_down_is_down
      -- resolve to the case that `e_vd_down` is indeed a downgrade
      simp[hshim_vc_down_is_down]

      have hshim_vc_down_is_vc_req := hfwd_sw_down_translation.gDownEncapVcInvalDir.reqTranslation
      simp[Event.req, ValidRequest.isNcWeakRead] at hshim_vc_down_is_vc_req
      -- resolve to case where we apply a Vd downgrade at the directory
      simp[hshim_vc_down_is_vc_req]
      simp[EntryState.directory]

      -- Now resolve Shim Vc downgrade
      simp[EntryState.state, EntryState.cache, DirectoryState.toState]
      simp[LE.le, State.le]
    | .cacheEvent _ =>
      have hshim_vc_down_is_dir := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
      simp[Event.isDirectoryEvent] at hshim_vc_down_is_dir
  | .cacheEvent _ =>
    have hshim_vd_down_is_dir := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    simp[Event.isDirectoryEvent] at hshim_vd_down_is_dir

lemma Behaviour.directory_vd_and_vc_downgrade_from_vc_state_le_i {b init e_gdown} {e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  : EntryState.state n
    (List.stateAfter n [e_dir_shim_vd_down, e_dir_shim_vc_down]
      (Sum.inr (DirectoryState.Vc ⟨Vc, DirectoryEvent.SucceedingState._proof_4⟩))) ≤
  EntryState.cache n (Sum.inl I) := by
  rw[List.stateAfter]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_vd_down with
  | .directoryEvent de_shim_vd_down =>
    simp [DirectoryEvent.SucceedingState]
    have hshim_vd_down_is_down := hfwd_sw_down_translation.gDownEncapVdWBDir.downgrade
    simp[Event.down] at hshim_vd_down_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hshim_vd_down_is_down]

    have hshim_vd_down_is_vd_req := hfwd_sw_down_translation.gDownEncapVdWBDir.reqTranslation
    simp[Event.req, ValidRequest.isNcWeakWrite] at hshim_vd_down_is_vd_req
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hshim_vd_down_is_vd_req]
    simp[EntryState.directory]

    -- Now resolve Shim Vc downgrade
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    match e_dir_shim_vc_down with
    | .directoryEvent de_shim_vc_down =>
      simp[DirectoryEvent.SucceedingState]
      have hshim_vc_down_is_down := hfwd_sw_down_translation.gDownEncapVcInvalDir.downgrade
      simp[Event.down] at hshim_vc_down_is_down
      -- resolve to the case that `e_vd_down` is indeed a downgrade
      simp[hshim_vc_down_is_down]

      have hshim_vc_down_is_vc_req := hfwd_sw_down_translation.gDownEncapVcInvalDir.reqTranslation
      simp[Event.req, ValidRequest.isNcWeakRead] at hshim_vc_down_is_vc_req
      -- resolve to case where we apply a Vd downgrade at the directory
      simp[hshim_vc_down_is_vc_req]
      simp[EntryState.directory]

      -- Now resolve Shim Vc downgrade
      simp[EntryState.state, EntryState.cache, DirectoryState.toState]
      simp[LE.le, State.le]
    | .cacheEvent _ =>
      have hshim_vc_down_is_dir := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
      simp[Event.isDirectoryEvent] at hshim_vc_down_is_dir
  | .cacheEvent _ =>
    have hshim_vd_down_is_dir := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    simp[Event.isDirectoryEvent] at hshim_vd_down_is_dir

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade
  {b : Behaviour n} {init : InitialSystemState n} {init_cdir_state : EntryState n}
  {e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n} {e_gdown : Event n} (hsc_write : e_gdown.isSCWrite) (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b init_cdir_state e_dir_shim_vc_down) ≤
  EntryState.cache n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_gdown) e_gdown)
  := by
  /- Strategy:
  1. show that with an Acquire, Acquire Dir event, Vd Dir downgrade, and Vc Dir downgrade, the state after e_dir_shim_vc_down is `I`.
    (a) Show that Acquire Dir access `e_dir_shim_acq` sets the Directory State to `Vd`.
    (b) Show that the Vd Dir Downgrade `e_dir_shim_vd_down` sets the Directory State to `Vc`.
    (c) Show that the Vc Dir Downgrade `e_dir_shim_vc_down` sets the Directory State to `I`.
  2. show that the stateAfter the SC Write Downgrade `e_gdown` is `I`.
  QED.
  -/

  -- cache state after a Fwd Get SW Downgrade is I.
  rw[Behaviour.stateAfter_fwd_sw_downgrade_eq_i n hgdown.isGlobal.reqAtCache hgdown.isDown hsc_write]

  simp[Behaviour.stateAfter]

  -- Now show that the state after an Acquire + Directory Vd Downgrade + Directory Vc Downgrade is I.
  rw[Behaviour.upTo_immediatePredecessor_eq n hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir]
  rw[Behaviour.upTo_immediatePredecessor_eq n hfwd_sw_down_translation.acqDirImmBeforeVdWBDir]

  induction eventsUpToEvent n b e_dir_shim_acq generalizing init_cdir_state with
  | nil =>
    simp
    rw [List.stateAfter]
    simp[Event.SucceedingState]
    match e_dir_shim_acq with
    | .directoryEvent de_acq =>
      simp [DirectoryEvent.SucceedingState]
      -- Show the Directory Acq `de_acq` corresponds to the proxy `e_shim_acq`
      have hacq_correspond_dir_acq := hfwd_sw_down_translation.acqDir.dirCorresponds.dirReq
      simp[reqToDirOfRequestEvent] at hacq_correspond_dir_acq
      have hacq_same_down_dir_acq := hfwd_sw_down_translation.acqDir.dirCorresponds.sameDown

      have hshim_acq_spec := hfwd_sw_down_translation.acq
      have hshim_acq_at_proxy := hfwd_sw_down_translation.acq.atCorrClusterProxy.atProxy
      simp[Event.atProxy] at hshim_acq_at_proxy
      match e_shim_acq with
      | .cacheEvent ce_acq =>
        -- Relate `e_shim_acq` not downgrade to `e_dir_shim_acq` not downgrade as well.
        have hshim_acq_not_downgrade := hshim_acq_spec.downgrade
        simp at hshim_acq_not_downgrade
        simp[hshim_acq_not_downgrade,] at hacq_same_down_dir_acq
        simp[Event.down,] at hacq_same_down_dir_acq
        -- Simp goal; `e_dir_shim_acq` not a downgrade
        simp[hacq_same_down_dir_acq]

        -- Relate `e_shim_acq` Acquire request to `e_dir_shim_acq` Acquire request as well.
        have hshim_acq_is_acq := hshim_acq_spec.reqTranslation
        simp[Event.req, ValidRequest.isAcquire] at hshim_acq_is_acq

        simp[Event.req, hshim_acq_is_acq] at hacq_correspond_dir_acq
        simp[Event.reqToDirOfRequestEvent,] at hacq_correspond_dir_acq
        simp[Event.req,] at hacq_correspond_dir_acq
        simp[hshim_acq_is_acq,] at hacq_correspond_dir_acq
        match hacq_made_on : EntryState.cache n
          (stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_acq)) (Event.cacheEvent ce_acq)) with
        | ⟨some .wr, false⟩ =>
          simp[hacq_made_on] at hacq_correspond_dir_acq
          simp [hacq_correspond_dir_acq]
          apply Behaviour.directory_vd_and_vc_downgrade_from_vd_state_le_i
          . case hfwd_sw_down_translation => exact hfwd_sw_down_translation
        | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .r, false⟩ | ⟨none, true⟩ | ⟨none, false⟩ =>
          simp[hacq_made_on] at hacq_correspond_dir_acq
          simp [hacq_correspond_dir_acq]
          match hdir_acq_made_on : init_cdir_state.directory with
          | .SW sw _ | .MR mr _ | .Vd vd | .Vc vc | .I i
            =>
            simp[]
            try (all_goals apply Behaviour.directory_vd_and_vc_downgrade_from_vd_state_le_i n hfwd_sw_down_translation )
            try (all_goals apply Behaviour.directory_vd_and_vc_downgrade_from_vc_state_le_i n hfwd_sw_down_translation )
            try (all_goals apply Behaviour.directory_vd_and_vc_downgrade_from_vd_state_le_i' n hfwd_sw_down_translation )
      | .directoryEvent _ => simp at hshim_acq_at_proxy
    | .cacheEvent _ =>
      have hdir_acq_is_dir := hfwd_sw_down_translation.acqDir.isDir
      simp[Event.isDirectoryEvent] at hdir_acq_is_dir
  | cons head l_tail ih =>
    simp only [List.cons_append]
    simp only [List.stateAfter]
    apply ih

lemma CompoundProtocol.noCoherentRead.global_sc_write_downgrade_le_cluster_dir_state
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_write_spec : Event.isSCWriteGlobalDowngrade n e_gdown)
  (hgdown_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW.wrapper n b init e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose_spec.right
  let hvc_inval_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose_spec.left

  /- Identify the event that finishes the last, right before `e_gdown` does. -/
  -- (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  have hevict_imm_finish_before_gdown := Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade n
    hgdown_in_b hgdown hvc_inval_in_b htranslation_spec
  let e_dir_shim_vc_down := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose
  let e_dir_shim_vc_down_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose_spec.left
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_shim_vc_down_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]

  /- Simp into the state after the coherent read is ≤ the state after the coherent read downgrade. -/
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' e_dir_shim_vc_down hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp

  apply Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade
  . case hsc_write => exact hgdown_write_spec.isSCWrite
  . case hgdown => exact hgdown
  . case hfwd_sw_down_translation => exact htranslation_spec

/- adding lemmas for Case `noCoherentRead`, `SC Write Downgrade` on `Vd` state. -/

lemma Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_vc_down e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  intro e_inter hinter_in_b hinter_btn_vcInval_and_gdown

  have hdir_vc_same_struct_inter := hinter_btn_vcInval_and_gdown.sameCidInterPred
  match hdir_vc : e_dir_shim_vc_down, hinter : e_inter with
  | .directoryEvent de_dir_vc_down , .directoryEvent de_inter =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_vc_down de_inter
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_vc_ob_inter =>
      -- can't have another event between dir_evict and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      -- have test : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := hfwd_sw_down_translation.
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        constructor
        . case clusterMatch =>
          constructor
          . case sameAddr =>
            simp[Event.sameAddr]
            rw[hinter, hinter_btn_vcInval_and_gdown.sameAddr]
            rw[← hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
          . case atCorrCluster =>
            have hdir_vcInval_corr_cluster := Behaviour.global_downgrade_cache_translation_encap_corresponding_request n hgdown
              hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
              (by rfl)
              hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
            simp[Event.reqAtCorrespondingGCacheOfCDir] at hdir_vcInval_corr_cluster
            simp[Event.correspondingClusterOfGlobalCache]

            simp[Event.protocol] at hdir_vcInval_corr_cluster
            match hdir_evict_pi : de_dir_vc_down.pInst with
            | .global => simp[hdir_evict_pi] at hdir_vcInval_corr_cluster
            | .cluster2 | .cluster1 =>
              simp[hdir_evict_pi] at hdir_vcInval_corr_cluster
              simp[Event.reqAtGlobalCacheCid] at hdir_vcInval_corr_cluster
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
                    simp[Event.struct] at hdir_vc_same_struct_inter
                    rw[hdir_vc_same_struct_inter]
                    exact hdir_evict_pi)
                | .proxy pi => simp[hcegdown_cid] at hdir_vcInval_corr_cluster
              | .directoryEvent _ => simp at hdir_vcInval_corr_cluster
        . case atDir => simp [Event.isDirectoryEvent, hinter]
        . case globalEncap =>
          simp[Event.Encapsulates]
          apply And.intro
          . case left =>
            simp [DirectoryEvent.OrderedBefore] at hdir_vc_ob_inter
            calc e_gdown.oStart < e_dir_shim_vc_down.oStart := by simp[hdir_vc, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.left]
                -- _ < e_dir_shim_vc_down.oStart := by simp[hdir_vc, hfwd_sw_down_translation.cohEvictDir.reqEncapDir.left]
                _ < e_dir_shim_vc_down.oEnd := e_dir_shim_vc_down.oWellFormed
                _ < e_inter.oStart := by simp[hdir_vc, hinter, Event.oEnd, Event.oStart, hdir_vc_ob_inter]
          . case right => simp[← Event.finishesBefore.eq_def, hinter, hinter_btn_vcInval_and_gdown.interSucc]
      have honly_encap_vd_vc := hfwd_sw_down_translation.onlyVdVcDir
      have hinter_is_dir_vd_or_vc := honly_encap_vd_vc e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      cases hinter_is_dir_vd_or_vc
      . case inl hinter_eq_vd =>
        -- contradiction, hinter is coh get SW dir event, that's immediately before coh put SW dir event.
        rw[hinter] at hinter_eq_vd
        absurd hinter_btn_vcInval_and_gdown.interPred
        rw[hinter_eq_vd]
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hinter_imm_pred_dir_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
        simp[ImmediateBottomPredecessor,] at hinter_imm_pred_dir_vc
        have hinter_pred_dir_vc := hinter_imm_pred_dir_vc.isImmPred.bPred.isPred
        simp[Event.Predecessor, Event.OrderedBefore,] at hinter_pred_dir_vc
        match e_dir_shim_vd_down with
        | .directoryEvent de_dir_vd =>
          simp[Event.oEnd, Event.oStart] at hinter_pred_dir_vc
          simp[Event.oEnd]
          calc de_dir_vd.oEnd < de_dir_vc_down.oStart := hinter_pred_dir_vc
            _ < de_dir_vc_down.oEnd := de_dir_vc_down.oWellFormed
        | .cacheEvent _ =>
          have hvd_dir_is_dir := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
          simp[Event.isDirectoryEvent] at hvd_dir_is_dir
      . case inr hinter_eq_vc =>
        -- contradiction, dir evict event can't finish before itself!
        absurd hinter_btn_vcInval_and_gdown.interPred
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_right
        rw[hinter] at hinter_eq_vc
        rw[hinter_eq_vc]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_btn_vcInval_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc de_inter.oEnd < de_dir_vc_down.oStart := hinter_ob_dir_evict
        _ < de_dir_vc_down.oEnd := de_dir_vc_down.oWellFormed
  | .cacheEvent ce_dir_vc , .directoryEvent de_inter
  | .directoryEvent de_dir_vc , .cacheEvent ce_inter
  | .cacheEvent ce_dir_vc , .cacheEvent ce_inter =>
    have hdir_vc_dir := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
    simp[Event.struct] at hdir_vc_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_vc_dir

lemma Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vd_down e_dir_shim_vc_down : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_vc_down e_gdown := by
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore => simp[Event.finishesBefore, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.right]
      . case sameAddr =>
        simp[ Event.sameAddr,]
        apply Eq.symm
        simp[← Event.sameAddr.eq_def, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
      . case predInB => exact hvc_down_in_b
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => rfl
      . case hdir_is_dir => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
  . case noIntermediate =>
    apply Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade_on_cluster_Vd
    . case hgdown => exact hgdown
    . case hfwd_sw_down_translation => exact hfwd_sw_down_translation

lemma Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore' {b e es init_state}
  : (List.stateAfter n (eventsUpToEvent n b e ++ es) init_state) = (es.stateAfter n (stateBefore n b init_state e))
  := by
  simp [stateBefore]
  induction eventsUpToEvent n b e generalizing init_state with
  | nil => simp[List.stateAfter]
  | cons head l_tail ih =>
    rw[List.cons_append]
    nth_rw 2 [List.stateAfter]
    nth_rw 1 [List.stateAfter]
    apply ih

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
  (h : ∀ e ∈ b, Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
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
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      have hall_es_same_entry : ∀ e' ∈ b.eventsUpToEvent n e_cdir, b.eventAtEntry n e' e_cdir.struct e_cdir.addr := Behaviour.eventsUpToEntry_at_e_entry' n
      rw[hes_upto] at hall_es_same_entry
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
    have htail_not_ob_e_cdir := h tail htail_pred_cdir.predInB htail_correspond_gdown hgdown_encap_tail
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
  (h : ∀ e ∈ b, Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
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
  (h : ∀ e ∈ b, Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
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

lemma Behaviour.immediateBottomPredecessor_of_immediateFinishesBeforeAtClusterDirectoryNotEncap_and_matchingCluster_encap
  -- (hcdir_first_event_at_dir : )
  /- Will need a hypothesis that `e_cdir` is encapsulated by `e_gdown`,
  and no other Event `e` is encapsulated by `e_gdown` at the coresponding cluster directory -/
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_in_b : e_cdir ∈ b)
  -- (h : ∀ e ∈ b, Event.reqAtCorrespondingGCacheOfCDir n e e_gdown → e_gdown.Encapsulates n e → ¬ e.OrderedBefore n e_cdir)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
  (hpred : ∃ e_pred ∈ b, immediateFinishesBeforeAtClusterDirectoryNotEncap n b e_pred e_gdown)
  : ImmediateBottomPredecessor n b hpred.choose e_cdir := by
  constructor
  . case isImmPred =>
    -- all directory events are ordered. in the `e_cdir`.OrderedBefore `e_pred` case, show a contradiction.
    -- have hpred_spec := himm_finish_nonempty.choose_spec.right
    constructor
    . case bPred =>
      constructor
      . case sameEntry =>
        apply Behaviour.cluster_directory_matching_global_cache_same_entry n hcdir_is_dir hcdir_matching_cluster hpred
      . case isPred =>
        simp[Event.Predecessor, Event.OrderedBefore]
        -- [] prove lemma to say that corresponding to a CDir as well means hpred.choose is a DirectoryEvent.
        have test := hpred.choose_spec.right
        sorry
      . case predInB => exact hpred.choose_spec.left
      . case succInB => exact hcdir_in_b
    . case noIntermediate =>
      simp[NoIntermediatePredecessor]
      /- this implies there is another "immediate finishes before at cluster not encap" (`immediateFinishesBeforeAtClusterDirectoryNotEncap`)
      like `hpred.choose`, but `hpred.choose` is the immediate.
      -/
      sorry
  . case isBottomPred => sorry
  . case isBottomSucc => exact Behaviour.directory_event_is_bottom n b e_cdir (by simp[hcdir_is_dir])

-- consider the immediate successor event encapsulated in e_gdown.
lemma Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event {b init e_gdown}
  -- (hcdir_first_event_at_dir : )
  (e_cdir : Event n)
  (hcdir_is_dir : e_cdir.isDirectoryEvent)
  (hcdir_in_b : e_cdir ∈ b)
  (hcdir_matching_cluster : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_cdir)
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
    have hpred_imm_pred_e_cdir : ImmediateBottomPredecessor n b e_pred e_cdir :=
      Behaviour.immediateBottomPredecessor_of_immediateFinishesBeforeAtClusterDirectoryNotEncap_and_matchingCluster_encap n
        hcdir_is_dir hcdir_in_b hcdir_matching_cluster himm_finish_nonempty

    rw [Behaviour.upTo_immediatePredecessor_eq n hpred_imm_pred_e_cdir]

    --
    -- simp[himm_finish_before_subsingleton]
    have t := Set.mem_setOf.mpr himm_finish_nonempty.choose_spec.right
    rw[Behaviour.immediate_finishes_before_cluster_not_encap_singleton_of_nonempty_and_subsingleton n himm_finish_before_subsingleton himm_finish_nonempty]

    rw[Set.toOption_singleton'' himm_finish_nonempty.choose]
    (
    show {himm_finish_nonempty.choose} = {himm_finish_nonempty.choose}
    rfl)
    -- subst e_pred

    simp[eventToEntryState, stateAfter]

    have := InitialSystemState.same_entry_eq
    rw[InitialSystemState.same_entry_eq n hpred_same_entry_cdir]
  . case neg himm_finish_empty =>
    rw [Set.not_nonempty_iff_eq_empty'] at himm_finish_empty
    rw[← immediateFinishesBeforeAtClusterDirectoryEventsNotEncap]
    rw[himm_finish_empty]
    simp[eventToEntryState, Set.toOption]

    rw[Behaviour.eventsUpToEvent_eq_nil_of_empty_finishes_before_events]
    simp [List.stateAfter]

    -- show initial states are the same
    apply Behaviour.InitialSystemState_eq_of_cluster_directory_corresponding_to_global_cache
    . case hdir_is_dir => exact hcdir_is_dir
    . case hcdir_matching_cluster => exact hcdir_matching_cluster

    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry

/- Something like this is probably the best way to break down the 3 lemmas -/
lemma Behaviour.directory_vd_downgrade_from_vd_state_eq_stateAfter_vc_append_rest
  {es : List (Event n)} {e_dir_shim_vd_down : Event n}
  (hvd_is_dir : e_dir_shim_vd_down.isDirectoryEvent)
  (hvd_is_down : e_dir_shim_vd_down.down)
  (hvd_is_nc_weak_write : e_dir_shim_vd_down.req.isNcWeakWrite)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  :
  List.stateAfter n ([e_dir_shim_vd_down] ++ es) (Sum.inr (DirectoryState.Vd ⟨Vd, by simp⟩)) = List.stateAfter n es (Sum.inr (DirectoryState.Vc ⟨Vc, by simp⟩))
  -- (List.stateAfter n ([e_dir_shim_vd_down] ++ [e_dir_shim_vc_down]) (Sum.inr (DirectoryState.Vd a✝)))
  := by
  rw[List.stateAfter.eq_def]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_vd_down with
  | .directoryEvent de_shim_vd_down =>
    simp [DirectoryEvent.SucceedingState]
    simp[Event.down] at hvd_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hvd_is_down]

    simp[Event.req, ValidRequest.isNcWeakWrite] at hvd_is_nc_weak_write
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hvd_is_nc_weak_write]
    simp[EntryState.directory]
  | .cacheEvent _ =>
    simp[Event.isDirectoryEvent] at hvd_is_dir

lemma Behaviour.directory_vc_downgrade_from_vc_state_eq_stateAfter_i_append_rest
  {es : List (Event n)} {e_dir_shim_vc_down : Event n}
  (hvc_is_dir : e_dir_shim_vc_down.isDirectoryEvent)
  (hvc_is_down : e_dir_shim_vc_down.down)
  (hvc_is_nc_weak_read : e_dir_shim_vc_down.req.isNcWeakRead)
  :
  List.stateAfter n ([e_dir_shim_vc_down] ++ es) (Sum.inr (DirectoryState.Vc ⟨Vc, by simp⟩)) = List.stateAfter n es (Sum.inr (DirectoryState.I ⟨I, by simp⟩))
  := by
  -- Now resolve Shim Vc downgrade
  simp[List.stateAfter]
  simp[Event.SucceedingState]
  match e_dir_shim_vc_down with
  | .directoryEvent de_shim_vc_down =>
    simp[DirectoryEvent.SucceedingState]
    have hshim_vc_down_is_down := hvc_is_down
    simp[Event.down] at hshim_vc_down_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hshim_vc_down_is_down]

    have hshim_vc_down_is_vc_req := hvc_is_nc_weak_read
    simp[Event.req, ValidRequest.isNcWeakRead] at hshim_vc_down_is_vc_req
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hshim_vc_down_is_vc_req]
    simp[EntryState.directory]
  | .cacheEvent _ =>
    simp[Event.isDirectoryEvent] at hvc_is_dir

lemma Behaviour.stateAfter_directory_event_is_directory_state' {b init_state e_dir_coh_read} {es : List (Event n)} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  (hall_dir : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e_dir_coh_read) (Event.addr n e_dir_coh_read))
  : (List.stateAfter n es init_state).isDirectoryState := by
  simp[EntryState.isDirectoryState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isDirectoryState.eq_def]
    exact hinit_dir
  | cons head tail ih =>
    apply ih
    . case cons.hinit_dir =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_dir head (by simp) |>.eAtStruct
      match head with
      | .directoryEvent de => simp[EntryState.isDirectoryState]
      | .cacheEvent _ =>
        match e_dir_coh_read with
        | .directoryEvent _ => simp [Event.struct] at hhead_of_dir
        | .cacheEvent _ => simp[Event.isDirectoryEvent] at hdir_is_dir
    . case cons.hall_dir =>
      intro e' he'_in_tail
      apply hall_dir
      . case a => simp[he'_in_tail]

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

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  {e_dir_shim_vd_down e_dir_shim_vc_down : Event n} {e_gdown : Event n}
  (hsc_write : e_gdown.isSCWrite) (hgdown_cache : e_gdown.isCacheEvent) (hgdown : e_gdown.isGlobalDowngrade)
  (hdir_on_vd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_shim_vc_down) e_dir_shim_vc_down) ≤
  EntryState.cache n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_gdown) e_gdown)
  := by
  /- Strategy:
  1. Link the state finishing before (not encapsulated) at the cluster directory = Vd
    to the state before `e_dir_shim_vd_down`.
  2. show that with an Acquire, Acquire Dir event, Vd Dir downgrade, and Vc Dir downgrade, the state after e_dir_shim_vc_down is `I`.
    (a) Show that the Vd Dir Downgrade `e_dir_shim_vd_down` sets the Directory State to `Vc`.
    (b) Show that the Vc Dir Downgrade `e_dir_shim_vc_down` sets the Directory State to `I`.
  3. show that the stateAfter the SC Write Downgrade `e_gdown` is `I`.
  QED.
  -/

  -- cache state after a Fwd Get SW Downgrade is I.
  rw[Behaviour.stateAfter_fwd_sw_downgrade_eq_i n hgdown.isGlobal.reqAtCache hgdown.isDown hsc_write]

  simp[Behaviour.stateAfter]

  -- Now show that the state after an Acquire + Directory Vd Downgrade + Directory Vc Downgrade is I.
  rw[Behaviour.upTo_immediatePredecessor_eq n hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir]

  simp only [ List.append_assoc, ]
  rw[ Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore']
  /- But taking the `List.stateAfter` of the `eventsUpToEvent n b e_dir_shim_vd_down` and `e_dir_shim_vd_down`
  is the same as taking the `List.stateAfter` of the state of the last finishing (not encap'd) event before `e_dir_shim_vd_down`
  -/

  have hvd_vc_same_entry : e_dir_shim_vd_down.sameEntry n e_dir_shim_vc_down := by
    have hvd_imm_pred_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
    simp[ImmediateBottomPredecessor,] at hvd_imm_pred_vc
    have hvd_same_struct_vc := hvd_imm_pred_vc.isImmPred.sameStructure
    exact hvd_imm_pred_vc.isImmPred.bPred.sameEntry
  rw[← InitialSystemState.same_entry_eq n hvd_vc_same_entry]
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n
    e_dir_shim_vd_down hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch]

  simp [Shim.Global.toCluster.clusterDirStateBefore, latestDirectoryState.Before.GlobalCache, stateOfSubsingletonEventSet] at hdir_on_vd
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_shim_vd_down


  match hstate_before_vd : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))) with
  | Sum.inr ds => match ds with
    | .SW _ _ | .MR _ _ | .Vc _ | .I _
      =>
      simp[hstate_before_vd, EntryState.state, DirectoryState.toState] at hdir_on_vd
    | .Vd ⟨⟨some .wr, false⟩, _⟩ =>
      rw[Behaviour.directory_vd_downgrade_from_vd_state_eq_stateAfter_vc_append_rest n
        hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
        (by simp[hfwd_sw_down_translation.gDownEncapVdWBDir.downgrade])
        hfwd_sw_down_translation.gDownEncapVdWBDir.reqTranslation
        ]

      rw[← List.append_nil [e_dir_shim_vc_down]]
      rw[Behaviour.directory_vc_downgrade_from_vc_state_eq_stateAfter_i_append_rest n
        hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
        (by simp[hfwd_sw_down_translation.gDownEncapVcInvalDir.downgrade])
        hfwd_sw_down_translation.gDownEncapVcInvalDir.reqTranslation
        ]

      simp[List.stateAfter]
      simp[EntryState.state, EntryState.cache, DirectoryState.toState]
      simp[LE.le, State.le]
  | Sum.inl s =>
    have : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))).isDirectoryState := Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_directory_state n init hgdown_cache hgdown
    simp [hstate_before_vd] at this
    simp [EntryState.isDirectoryState] at this

lemma CompoundProtocol.noCoherentRead.global_sc_write_downgrade_on_Vd_le_cluster_dir_state
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_write_spec : Event.isSCWriteGlobalDowngrade n e_gdown)
  (hdir_on_vd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (hgdown_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd.wrapper n b init e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right
  let hvc_inval_in_b := hgdown_translation.choose_spec.right.choose_spec.left

  /- Identify the event that finishes the last, right before `e_gdown` does. -/
  -- (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  have hevict_imm_finish_before_gdown := Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade_on_cluster_Vd n
    hgdown_in_b hgdown hvc_inval_in_b htranslation_spec
  let e_dir_shim_vc_down := hgdown_translation.choose_spec.right.choose
  let e_dir_shim_vc_down_in_b := hgdown_translation.choose_spec.right.choose_spec.left
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_shim_vc_down_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToEntryState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]

  /- Simp into the state after the coherent read is ≤ the state after the coherent read downgrade. -/
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' e_dir_shim_vc_down hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp

  apply Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade_on_cluster_Vd
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

/- adding lemmas for Case `noCoherentRead`, `SC Write Downgrade` on `Vc` state. -/

/-- Lemma 6/7: A global downgrade `e_gdown` leaves it's corresponding cluster directory
in state `s` ≤ `e_gdown.MRS` -/
lemma CompoundProtocol.globalDowngrade.satisfies_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  : CompoundSWMR n b init e_gdown := by
  apply CompoundSWMR.gCache
  . case gcache_satisfies_cmp_swmr =>
    simp [Behaviour.globalCacheEvent.satisfiesCompoundSWMR]
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
      let cluster_p_of_gdown := cmp.clusterProtocolCorrespondingToGlobalProtocol n e_gdown
      have hgdown_translation_to_cluster := cmp.shimAxioms.globalToCluster b init cluster_p_of_gdown e_gdown hgdown_in_b
      -- Get the corresponding cluster to the global cache;
      cases hgdown_translation_to_cluster
      . case bothCoherentWriteAndRead hcluster_of_gcache hcluster_has_sc_write_read hgdown_is_down =>
        cases hgdown_is_down
        . case scWriteDown hgdown_write_spec hgdown_translation =>
          apply CompoundProtocol.global_sc_write_downgrade_le_cluster_dir_state
          . case hgdown_in_b => exact hgdown_in_b
          . case hgdown => exact hgdown
          . case hgdown_write_spec => exact hgdown_write_spec
          . case hgdown_translation => exact hgdown_translation
        . case scReadDown hgdown_read_spec hgdown_on_sw hgdown_translation =>
          apply CompoundProtocol.global_sc_read_downgrade_le_cluster_dir_state
          . case hgdown_in_b => exact hgdown_in_b
          . case hgdown => exact hgdown
          . case hgdown_read_spec => exact hgdown_read_spec
          . case hgdown_on_sw => exact hgdown_on_sw
          . case hgdown_translation => exact hgdown_translation
      . case noCoherentRead hcorrespond hno_coherent_read_in_p hdown_translation =>
        cases hdown_translation
        . case scWriteDowngrade hgdown_write_spec hgdown_translation =>
          cases hgdown_translation
          . case onDirSW hdir_on_sw htranslation =>
            apply CompoundProtocol.noCoherentRead.global_sc_write_downgrade_le_cluster_dir_state
            . case hgdown_in_b => exact hgdown_in_b
            . case hgdown => exact hgdown
            . case hgdown_write_spec => exact hgdown_write_spec
            . case hgdown_translation => exact htranslation
          . case onDirVd hdir_on_vd htranslation =>
            apply CompoundProtocol.noCoherentRead.global_sc_write_downgrade_on_Vd_le_cluster_dir_state
            sorry
            sorry
            sorry
            sorry
            sorry
          . case onDirVc hdir_on_vc htranslation =>
            sorry
        . case scReadDowngrade hgdown_read_spec hgdown_translation =>
          cases hgdown_translation
          . case onDirSW hdir_on_sw htranslation =>
            sorry
          . case onDirVd hdir_on_vd htranslation =>
            sorry
