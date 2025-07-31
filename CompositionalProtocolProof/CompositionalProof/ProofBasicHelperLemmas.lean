import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
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
