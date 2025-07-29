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

-- consider the immediate successor event encapsulated in e_gdown.
lemma Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event
  -- (hcdir_first_event_at_dir : )
  (e_cdir : Event n)
  : eventToState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
    (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))
    =
    EntryState.state n (stateBefore n b (InitialSystemState.stateAt n init e_cdir) e_cdir)
  := by
  sorry

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
  let h := hgdown_translation.choose_spec.right.choose_spec.right

  -- use `Behaviour.cluster_dir_event_immediately_finish_before_of_global_read_downgrade` here.
  have hevict_imm_finish_before_gdown := b.cluster_dir_event_immediately_finish_before_of_global_read_downgrade n
    hgdown_in_b hgdown htranslation_spec
  let e_dir_coh_get_mr_in_b := htranslation_spec.cohReadDir.dirInB
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_coh_get_mr_in_b hevict_imm_finish_before_gdown]
  sorry

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
      . case noCoherentRead =>
        sorry
      -- have hglobal_swmr := cmp.globalSWMR
