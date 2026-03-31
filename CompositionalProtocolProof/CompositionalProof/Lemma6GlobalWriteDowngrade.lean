import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourHelpers
import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.ProofBasicHelperLemmas

variable (n : Nat)

/-
Assume the Initial State / Current State satisfies Compound SWMR.
  (Must define a version of Compound SWMR for InitialSystemState)
For any global SW downgrade cache event `e_gdown`:
1. the corresponding Cluster Directory state is ≤ the state after `e_gdown`.
2. the corresponding Cluster is in SWMR. (techinically have this by an Axiom)
-/

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
  : EntryState.state n (List.stateAfter n [e_dir_coh_read] state_before_e_dir) ≤
  EntryState.cache n (List.stateAfter n [e_gdown] state_before_gdown)
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
  . case hsc_read => exact hgdown_read_spec.isSCRead
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

lemma Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown {e_inter de_inter e_dir_shim_vc_down e_gdown de_dir_vc_down}
  (hdir_vc : e_dir_shim_vc_down = Event.directoryEvent de_dir_vc_down)
  (hgdown_same_addr_vc_down : Event.sameAddr n e_gdown e_dir_shim_vc_down)
  (hdir_vc_ob_inter : DirectoryEvent.OrderedBefore n de_dir_vc_down de_inter)
  (hinter : e_inter = Event.directoryEvent de_inter)
  (hgdown_start_before_vc_down : Event.oStart n e_gdown < Event.oStart n e_dir_shim_vc_down)
  (hinter_btn_vcInval_and_gdown : Event.intermediateFinishesBeforeOfSameEntry n e_inter e_dir_shim_vc_down e_gdown)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hvc_down_corr_gdown : Event.correspondingClusterOfGlobalCache n e_gdown (Event.directoryEvent de_dir_vc_down) (Event.protocol n))
  (hvc_down_is_dir : Event.isDirectoryEvent n (Event.directoryEvent de_dir_vc_down))
  : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
  have hdir_vc_same_struct_inter := hinter_btn_vcInval_and_gdown.sameCidInterPred
  constructor
  . case clusterMatch =>
    constructor
    . case sameAddr =>
      simp[Event.sameAddr]
      rw[hinter_btn_vcInval_and_gdown.sameAddr]
      rw[← hgdown_same_addr_vc_down]
    . case atCorrCluster =>
      have hdir_vcInval_corr_cluster := Behaviour.global_downgrade_cache_translation_encap_corresponding_request n hgdown
        hvc_down_corr_gdown
        (by rfl)
        hvc_down_is_dir
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
      calc e_gdown.oStart < e_dir_shim_vc_down.oStart := by simp[hgdown_start_before_vc_down]
          -- _ < e_dir_shim_vc_down.oStart := by simp[hdir_vc, hfwd_sw_down_translation.cohEvictDir.reqEncapDir.left]
          _ < e_dir_shim_vc_down.oEnd := e_dir_shim_vc_down.oWellFormed
          _ < e_inter.oStart := by simp[hdir_vc, hinter, Event.oEnd, Event.oStart, hdir_vc_ob_inter]
    . case right => simp[← Event.finishesBefore.eq_def, hinter_btn_vcInval_and_gdown.interSucc]

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
        apply Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown
        . case hdir_vc => exact hdir_vc
        . case hgdown_same_addr_vc_down => simp[hdir_vc,hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
        . case hdir_vc_ob_inter => exact hdir_vc_ob_inter
        . case hinter => exact hinter
        . case hgdown_start_before_vc_down => simp[hdir_vc, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.left]
        . case hinter_btn_vcInval_and_gdown => simp[hdir_vc, hinter, hinter_btn_vcInval_and_gdown]
        . case hgdown => exact hgdown
        . case hvc_down_corr_gdown => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        . case hvc_down_is_dir => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
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
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToEntryState, -- Set.toOption,
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
        apply Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown
        . case hdir_vc => exact hdir_vc
        . case hgdown_same_addr_vc_down => simp[hdir_vc,hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
        . case hdir_vc_ob_inter => exact hdir_vc_ob_inter
        . case hinter => exact hinter
        . case hgdown_start_before_vc_down => simp[hdir_vc, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.left]
        . case hinter_btn_vcInval_and_gdown => simp[hdir_vc, hinter, hinter_btn_vcInval_and_gdown]
        . case hgdown => exact hgdown
        . case hvc_down_corr_gdown => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        . case hvc_down_is_dir => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
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

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  {e_dir_shim_vd_down e_dir_shim_vc_down : Event n} {e_gdown : Event n}
  (hsc_write : e_gdown.isSCWrite) (hgdown_cache : e_gdown.isCacheEvent) (hgdown : e_gdown.isGlobalDowngrade)
  (hdir_on_vd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  (hgdown_in_b : e_gdown ∈ b)
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
  have hall_dir_es_not_before_vd_down : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown →
    Event.Encapsulates n e_gdown e → ¬Event.OrderedBefore n e e_dir_shim_vd_down := by
    intro event he_in_b he_same_addr_gdown he_req_corr_gcache hgdown_encap_e
    have he_dir_corr_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown event := by
      constructor
      . case clusterMatch =>
        constructor
        . case sameAddr => simp_all[Event.sameAddr]
        . case atCorrCluster =>
          apply Behaviour.event_reqAtCorrespondingGCacheOfCDir_is_correspondingClusterOfGlobalCache
          . case he_req_corr_gcache => exact he_req_corr_gcache
      . case atDir =>
        apply Behaviour.reqAtCorrespondingGCacheOfCDir_is_directory_event
        . case he_req_corr_gcache => exact he_req_corr_gcache
      . case globalEncap => exact hgdown_encap_e
    have he_is_vd_or_vd := hfwd_sw_down_translation.onlyVdVcDir event he_in_b he_dir_corr_gdown
    cases he_is_vd_or_vd
    . case inl he_eq_vd =>
      simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      rw[he_eq_vd]
      simp[e_dir_shim_vd_down.oWellFormed]
    . case inr he_eq_vc =>
      simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      rw[he_eq_vc]
      have hvd_imm_bott_pred_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
      simp[ImmediateBottomPredecessor] at hvd_imm_bott_pred_vc
      have hvd_pred_vc := hvd_imm_bott_pred_vc.isImmPred.isPred
      calc e_dir_shim_vd_down.oStart < e_dir_shim_vd_down.oEnd := e_dir_shim_vd_down.oWellFormed
        _ < e_dir_shim_vc_down.oStart := hvd_pred_vc
        _ < e_dir_shim_vc_down.oEnd := e_dir_shim_vc_down.oWellFormed
  have hcdir_same_addr_gdown : e_dir_shim_vd_down.sameAddr n e_gdown := by
    have := hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr
    simp_all[Event.sameAddr]
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n
    e_dir_shim_vd_down hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    hcdir_same_addr_gdown
    hvd_down_in_b hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch
    hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
    hall_dir_es_not_before_vd_down
    hgdown_in_b
    hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap
    -- hfwd_sw_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch
    ]

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
  . case hsc_write => exact hgdown_write_spec.isSCWrite
  . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
  . case hgdown => exact hgdown
  . case hdir_on_vd => exact hdir_on_vd
  . case hfwd_sw_down_translation => exact htranslation_spec
  . case hvd_down_in_b => exact hgdown_translation.choose_spec.left
  . case hgdown_in_b => exact hgdown_in_b

/- adding lemmas for Case `noCoherentRead`, `SC Read Downgrade` on `SW` state. -/

lemma Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade_on_cluster_Vc
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vc_down : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc n b init  e_gdown e_dir_shim_vc_down)
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
        apply Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown
        . case hdir_vc => exact hdir_vc
        . case hgdown_same_addr_vc_down => simp[hdir_vc,hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
        . case hdir_vc_ob_inter => exact hdir_vc_ob_inter
        . case hinter => exact hinter
        . case hgdown_start_before_vc_down => simp[hdir_vc, hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap.left]
        . case hinter_btn_vcInval_and_gdown => simp[hdir_vc, hinter, hinter_btn_vcInval_and_gdown]
        . case hgdown => exact hgdown
        . case hvc_down_corr_gdown => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        . case hvc_down_is_dir => exact hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
      have honly_encap_vd_vc := hfwd_sw_down_translation.onlyVcDir
      have hinter_is_dir_vc := honly_encap_vd_vc e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      -- cases hinter_is_dir_vd_or_vc
      -- . case inr hinter_eq_vc =>
      -- contradiction, dir evict event can't finish before itself!
      absurd hinter_btn_vcInval_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_right
      rw[hinter] at hinter_is_dir_vc
      rw[hinter_is_dir_vc]
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

lemma Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade_on_cluster_Vc
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vc_down : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc n b init  e_gdown e_dir_shim_vc_down)
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
    apply Behaviour.noCoherentRead.cluster_vc_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_write_downgrade_on_cluster_Vc
    . case hgdown => exact hgdown
    . case hfwd_sw_down_translation => exact hfwd_sw_down_translation

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade_on_cluster_Vc
  {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  {e_dir_shim_vc_down : Event n} {e_gdown : Event n}
  (hsc_write : e_gdown.isSCWrite) (hgdown_cache : e_gdown.isCacheEvent) (hgdown : e_gdown.isGlobalDowngrade)
  (hdir_on_vc : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vc)
  (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc n b init  e_gdown e_dir_shim_vc_down)
  (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  (hgdown_in_b : e_gdown ∈ b)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_shim_vc_down) e_dir_shim_vc_down) ≤
  EntryState.cache n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_gdown) e_gdown)
  := by

  -- cache state after a Fwd Get SW Downgrade is I.
  rw[Behaviour.stateAfter_fwd_sw_downgrade_eq_i n hgdown.isGlobal.reqAtCache hgdown.isDown hsc_write]

  simp[Behaviour.stateAfter]

  -- Now show that the state after an Acquire + Directory Vd Downgrade + Directory Vc Downgrade is I.
  -- rw[Behaviour.upTo_immediatePredecessor_eq n hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir]

  rw[ Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore']
  /- But taking the `List.stateAfter` of the `eventsUpToEvent n b e_dir_shim_vd_down` and `e_dir_shim_vd_down`
  is the same as taking the `List.stateAfter` of the state of the last finishing (not encap'd) event before `e_dir_shim_vd_down`
  -/

  /-
  have hvd_vc_same_entry : e_dir_shim_vd_down.sameEntry n e_dir_shim_vc_down := by
    have hvd_imm_pred_vc := hfwd_sw_down_translation.vdWBDirImmBeforeVcInvalDir
    simp[ImmediateBottomPredecessor,] at hvd_imm_pred_vc
    have hvd_same_struct_vc := hvd_imm_pred_vc.isImmPred.sameStructure
    exact hvd_imm_pred_vc.isImmPred.bPred.sameEntry
  rw[← InitialSystemState.same_entry_eq n hvd_vc_same_entry]
    -/
  have hall_dir_es_not_before_vc_down : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown →
    Event.Encapsulates n e_gdown e → ¬Event.OrderedBefore n e e_dir_shim_vc_down := by
    intro event he_in_b he_same_addr_gdown he_req_corr_gcache hgdown_encap_e
    have he_dir_corr_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown event := by
      constructor
      . case clusterMatch =>
        constructor
        . case sameAddr => simp_all[Event.sameAddr]
        . case atCorrCluster =>
          apply Behaviour.event_reqAtCorrespondingGCacheOfCDir_is_correspondingClusterOfGlobalCache
          . case he_req_corr_gcache => exact he_req_corr_gcache
      . case atDir =>
        apply Behaviour.reqAtCorrespondingGCacheOfCDir_is_directory_event
        . case he_req_corr_gcache => exact he_req_corr_gcache
      . case globalEncap => exact hgdown_encap_e
    have he_eq_vc := hfwd_sw_down_translation.onlyVcDir event he_in_b he_dir_corr_gdown
    simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq]
    apply Or.intro_left
    rw[he_eq_vc]
    simp[e_dir_shim_vc_down.oWellFormed]
  have hcdir_same_addr_gdown : e_dir_shim_vc_down.sameAddr n e_gdown := by
    have := hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr
    simp_all[Event.sameAddr]
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n
    e_dir_shim_vc_down hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir
    hcdir_same_addr_gdown
    hvc_down_in_b hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch
    hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
    hall_dir_es_not_before_vc_down
    hgdown_in_b
    hfwd_sw_down_translation.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap
    ]

  simp [Shim.Global.toCluster.clusterDirStateBefore, latestDirectoryState.Before.GlobalCache, stateOfSubsingletonEventSet] at hdir_on_vc
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_shim_vc_down


  match hstate_before_vd : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))) with
  | Sum.inr ds => match ds with
    | .SW _ _ | .MR _ _ | .Vd _ | .I _
      =>
      simp[hstate_before_vd, EntryState.state, DirectoryState.toState] at hdir_on_vc
    | .Vc ⟨⟨some .r, false⟩, _⟩ =>
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

lemma CompoundProtocol.noCoherentRead.global_sc_write_downgrade_on_Vc_le_cluster_dir_state
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_write_spec : Event.isSCWriteGlobalDowngrade n e_gdown)
  (hdir_on_vc : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vc)
  (hgdown_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc.wrapper n b init e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right
  let hvc_inval_in_b := hgdown_translation.choose_spec.left

  /- Identify the event that finishes the last, right before `e_gdown` does. -/
  -- (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  have hevict_imm_finish_before_gdown := Behaviour.noCoherentRead.cluster_dir_vc_downgrade_event_immediately_finish_before_of_global_write_downgrade_on_cluster_Vc n
    hgdown_in_b hgdown hvc_inval_in_b htranslation_spec
  let e_dir_shim_vc_down := hgdown_translation.choose
  let e_dir_shim_vc_down_in_b := hgdown_translation.choose_spec.left
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

  apply Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_sw_downgrade_on_cluster_Vc
  . case hsc_write => exact hgdown_write_spec.isSCWrite
  . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
  . case hgdown => exact hgdown
  . case hdir_on_vc => exact hdir_on_vc
  . case hfwd_sw_down_translation => exact htranslation_spec
  . case hvc_down_in_b => exact hgdown_translation.choose_spec.left
  . case hgdown_in_b => exact hgdown_in_b

/- adding lemmas for Case `noCoherentRead`, `SC Read Downgrade` on `Vc` state. -/

lemma Behaviour.noCoherentRead.cluster_vd_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_read_downgrade_on_cluster_SW
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vd_down : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_vd_down e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  intro e_inter hinter_in_b hinter_btn_vdWB_and_gdown

  have hdir_vc_same_struct_inter := hinter_btn_vdWB_and_gdown.sameCidInterPred
  match hdir_vd : e_dir_shim_vd_down, hinter : e_inter with
  | .directoryEvent de_dir_vd_down , .directoryEvent e_dir_shim_vd_down =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_vd_down e_dir_shim_vd_down
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_vc_ob_inter =>
      -- can't have another event between dir_evict and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      -- have test : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := hfwd_sw_down_translation.
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        apply Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown
        . case hdir_vc => exact hdir_vd
        . case hgdown_same_addr_vc_down => simp[hdir_vd, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
        . case hdir_vc_ob_inter => exact hdir_vc_ob_inter
        . case hinter => exact hinter
        . case hgdown_start_before_vc_down => simp[hdir_vd, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap.left]
        . case hinter_btn_vcInval_and_gdown => simp[hdir_vd, hinter, hinter_btn_vdWB_and_gdown]
        . case hgdown => exact hgdown
        . case hvc_down_corr_gdown => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        . case hvc_down_is_dir => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
      have honly_encap_acq_vd := hfwd_mr_down_translation.onlyAcqVdDir
      have hinter_is_dir_acq_vd := honly_encap_acq_vd e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      cases hinter_is_dir_acq_vd
      . case inl hinter_eq_acq =>
        -- contradiction, hinter is coh get SW dir event, that's immediately before coh put SW dir event.
        rw[hinter] at hinter_eq_acq
        absurd hinter_btn_vdWB_and_gdown.interPred
        rw[hinter_eq_acq]
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hinter_imm_pred_dir_vd := hfwd_mr_down_translation.acqDirImmBeforeVdWBDir
        simp[ImmediateBottomPredecessor,] at hinter_imm_pred_dir_vd
        have hinter_pred_dir_vd := hinter_imm_pred_dir_vd.isImmPred.bPred.isPred
        simp[Event.Predecessor, Event.OrderedBefore,] at hinter_pred_dir_vd
        match e_dir_shim_acq with
        | .directoryEvent de_dir_acq =>
          simp[Event.oEnd, Event.oStart] at hinter_pred_dir_vd
          simp[Event.oEnd]
          calc de_dir_acq.oEnd < de_dir_vd_down.oStart := hinter_pred_dir_vd
            _ < de_dir_vd_down.oEnd := de_dir_vd_down.oWellFormed
        | .cacheEvent _ =>
          have hvd_dir_is_dir := hfwd_mr_down_translation.acqDir.isDir
          simp[Event.isDirectoryEvent] at hvd_dir_is_dir
      . case inr hinter_eq_vd =>
        -- contradiction, dir evict event can't finish before itself!
        absurd hinter_btn_vdWB_and_gdown.interPred
        simp[Event.finishesBefore]
        simp[Nat.le_iff_lt_or_eq]
        apply Or.intro_right
        rw[hinter] at hinter_eq_vd
        rw[hinter_eq_vd]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_btn_vdWB_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc e_dir_shim_vd_down.oEnd < de_dir_vd_down.oStart := hinter_ob_dir_evict
        _ < de_dir_vd_down.oEnd := de_dir_vd_down.oWellFormed
  | .cacheEvent ce_dir_vc , .directoryEvent de_inter
  | .directoryEvent de_dir_vc , .cacheEvent ce_inter
  | .cacheEvent ce_dir_vc , .cacheEvent ce_inter =>
    have hdir_vc_dir := hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    simp[Event.struct] at hdir_vc_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_vc_dir

lemma Behaviour.noCoherentRead.cluster_dir_vd_downgrade_event_immediately_finish_before_of_global_write_downgrade
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_vd_down e_gdown := by
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore =>
        simp[Event.finishesBefore, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap.right]
      . case sameAddr =>
        simp[ Event.sameAddr,]
        apply Eq.symm
        simp[← Event.sameAddr.eq_def, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
      . case predInB => exact hvd_down_in_b
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => rfl
      . case hdir_is_dir => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
  . case noIntermediate =>
    apply Behaviour.noCoherentRead.cluster_vd_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_read_downgrade_on_cluster_SW
    . case hgdown => exact hgdown
    . case hfwd_mr_down_translation => exact hfwd_mr_down_translation

lemma ite_SW_le_MR_then_I_else_MR_eq_MR
  : (if SW ≤ { p := some ReadWritePermissions.r, c := true } then I else { p := some ReadWritePermissions.r, c := true })
    = { p := some ReadWritePermissions.r, c := true } := by
  simp[LE.le]
  simp[State.le]
  simp[LT.lt]
  simp [LE.le]
  simp [LT.lt]

lemma Behaviour.state_after_cluster_dir_on_Vc_and_global_sc_read_le_state_on_SW_of_cmp_swmr
  (hgdown :  e_gdown.isGlobalDowngrade)
  (hgdown_cache : e_gdown.isCacheEvent)
  (hsc_read : e_gdown.isSCRead)
  (hstate_before_gdown_is_cache_state : state_before_gdown.isCacheState)
  (hstate_before_gdown : state_before_gdown.cache = SW)
  : EntryState.state n (Sum.inr (DirectoryState.Vc ⟨Vc, by simp⟩)) ≤
  EntryState.cache n (List.stateAfter n [e_gdown] state_before_gdown) := by
  simp[List.stateAfter]
  have hgdown_cache := hgdown.isGlobal.reqAtCache
  match e_gdown with
  | .cacheEvent ce =>
    match state_before_gdown with
    | .inl cache_s_before_gdown =>
      simp [EntryState.cache] at hstate_before_gdown
      rw[hstate_before_gdown]
      -- nth_rw 2 [Event.SucceedingState.eq_def]
      rw [Event.SucceedingState.eq_def]
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
      simp[EntryState.cache]
      simp[ValidRequest.MRS]
      simp[ReadWrite.toPerms,ReadWrite.toRWPerms]
      rw [ite_SW_le_MR_then_I_else_MR_eq_MR]

      -- Now unravel the last bit on the left side of ≤
      simp [EntryState.state, DirectoryState.toState]
      simp[LE.le, State.le, LT.lt, State.lt, Option.le, ReadWritePermissions.le]
  | .directoryEvent _
    => simp[Event.isCacheEvent] at hgdown_cache

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade_on_cluster_SW
  {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  {e_shim_acq e_dir_shim_acq e_dir_shim_vd_down : Event n} {e_gdown : Event n} (hsc_read : e_gdown.isSCRead) (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_cache : e_gdown.isCacheEvent)
  (hgdown_on_sw : Behaviour.cacheStateMadeOn n b init e_gdown = SW)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down)
  -- {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  -- {e_dir_shim_vd_down e_dir_shim_vc_down : Event n} {e_gdown : Event n}
  -- (hsc_write : e_gdown.isSCWrite) (hgdown_cache : e_gdown.isCacheEvent) (hgdown : e_gdown.isGlobalDowngrade)
  (hdir_on_sw : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown SW)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  -- (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  (hgdown_in_b : e_gdown ∈ b)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_shim_vd_down) e_dir_shim_vd_down) ≤
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

  simp[Behaviour.stateAfter]

  -- Now show that the state after an Acquire + Directory Vd Downgrade + Directory Vc Downgrade is I.
  rw[Behaviour.upTo_immediatePredecessor_eq n hfwd_mr_down_translation.acqDirImmBeforeVdWBDir]

  simp only [ List.append_assoc, ]
  rw[ Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore']
  /- But taking the `List.stateAfter` of the `eventsUpToEvent n b e_dir_shim_vd_down` and `e_dir_shim_vd_down`
  is the same as taking the `List.stateAfter` of the state of the last finishing (not encap'd) event before `e_dir_shim_vd_down`
  -/

  have hacq_vd_same_entry : e_dir_shim_acq.sameEntry n e_dir_shim_vd_down := by
    have hvd_imm_pred_vc := hfwd_mr_down_translation.acqDirImmBeforeVdWBDir
    simp[ImmediateBottomPredecessor,] at hvd_imm_pred_vc
    have hvd_same_struct_vc := hvd_imm_pred_vc.isImmPred.sameStructure
    exact hvd_imm_pred_vc.isImmPred.bPred.sameEntry
  rw[← InitialSystemState.same_entry_eq n hacq_vd_same_entry]
  have hall_dir_es_not_before_acq : ∀ e ∈ b, e.sameAddr n e_gdown → Event.reqAtCorrespondingGCacheOfCDir n e e_gdown →
    Event.Encapsulates n e_gdown e → ¬Event.OrderedBefore n e e_dir_shim_acq := by
    intro event he_in_b he_same_addr_gdown he_req_corr_gcache hgdown_encap_e
    have he_dir_corr_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown event := by
      constructor
      . case clusterMatch =>
        constructor
        . case sameAddr => simp_all[Event.sameAddr]
        . case atCorrCluster =>
          apply Behaviour.event_reqAtCorrespondingGCacheOfCDir_is_correspondingClusterOfGlobalCache
          . case he_req_corr_gcache => exact he_req_corr_gcache
      . case atDir =>
        apply Behaviour.reqAtCorrespondingGCacheOfCDir_is_directory_event
        . case he_req_corr_gcache => exact he_req_corr_gcache
      . case globalEncap => exact hgdown_encap_e
    have he_is_acq_or_vd := hfwd_mr_down_translation.onlyAcqVdDir event he_in_b he_dir_corr_gdown
    cases he_is_acq_or_vd
    . case inl he_eq_acq =>
      simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      rw[he_eq_acq]
      simp[e_dir_shim_acq.oWellFormed]
    . case inr he_eq_vd =>
      simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      rw[he_eq_vd]
      have hvd_imm_bott_pred_vc := hfwd_mr_down_translation.acqDirImmBeforeVdWBDir
      simp[ImmediateBottomPredecessor] at hvd_imm_bott_pred_vc
      have hacq_pred_vd := hvd_imm_bott_pred_vc.isImmPred.isPred
      calc e_dir_shim_acq.oStart < e_dir_shim_acq.oEnd := e_dir_shim_acq.oWellFormed
        _ < e_dir_shim_vd_down.oStart := hacq_pred_vd
        _ < e_dir_shim_vd_down.oEnd := e_dir_shim_vd_down.oWellFormed
  have hcdir_same_addr_gdown : e_dir_shim_acq.sameAddr n e_gdown := by
    have := hfwd_mr_down_translation.acqDir.dirCorresponds.sameAddr
    have hacq_same_addr_egdown := hfwd_mr_down_translation.acq.atCorrClusterProxy.clusterMatch.sameAddr
    simp_all[Event.sameAddr]

  have hdir_acq_match_cluster_gdown : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_dir_shim_acq := by
    constructor
    . case sameAddr =>
      have hacq_same_addr_dir := hfwd_mr_down_translation.acqDir.dirCorresponds.sameAddr
      have hacq_same_addr_gdown :=hfwd_mr_down_translation.acq.atCorrClusterProxy.clusterMatch.sameAddr
      simp_all[Event.sameAddr]
    . case atCorrCluster =>
      simp[Event.correspondingClusterOfGlobalCache]
      have hacq_dir_protocol := hfwd_mr_down_translation.acqDir.dirCorresponds.sameProtocol
      simp[Event.sameProtocol] at hacq_dir_protocol
      have hacq := hfwd_mr_down_translation.acq.atCorrClusterProxy.clusterMatch.atCorrCluster
      simp[Event.correspondingClusterOfGlobalCache] at hacq

      match e_gdown with
      | .cacheEvent cgdown => simp_all
      | .directoryEvent _ => simp at hacq
  have hdir_acq_corresponding_cluster : Event.correspondingClusterOfGlobalCache n e_gdown e_dir_shim_acq (Event.protocol n) := by
    exact hdir_acq_match_cluster_gdown.atCorrCluster
  have hgdown_encap_dir_acq : Event.Encapsulates n e_gdown e_dir_shim_acq := by
    have hgdown_encap_acq := hfwd_mr_down_translation.acq.globalEncap
    have hacq_encap_dir := hfwd_mr_down_translation.acqDir.reqEncapDir
    simp[Event.Encapsulates]
    apply And.intro
    . case left =>
      simp[Event.Encapsulates] at hgdown_encap_acq hacq_encap_dir
      grind
    . case right =>
      simp[Event.Encapsulates] at hgdown_encap_acq hacq_encap_dir
      grind
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n
    e_dir_shim_acq hfwd_mr_down_translation.acqDir.isDir
    hcdir_same_addr_gdown
    hfwd_mr_down_translation.acqDir.dirInB
    hdir_acq_match_cluster_gdown
    hdir_acq_corresponding_cluster
    hall_dir_es_not_before_acq
    hgdown_in_b
    hgdown_encap_dir_acq
    ]

  simp [Shim.Global.toCluster.clusterDirStateBefore, latestDirectoryState.Before.GlobalCache, stateOfSubsingletonEventSet] at hdir_on_sw
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_shim_vd_down


  match hstate_before_vd : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))) with
  | Sum.inr ds => match ds with
    | .MR _ _ | .Vd _ | .Vc _ | .I _
      =>
      simp[hstate_before_vd, EntryState.state, DirectoryState.toState] at hdir_on_sw
    | .SW ⟨⟨some .wr, true⟩, _⟩ owner =>
    -- CHECKPOINT
      -- Derive that the dir req is NC write (rw=.w, coherent=false) from reqToDirOfRequestEvent.
      -- Acquire on Vd cache state → NC weak write at directory.
      have hacq_dir_req := hfwd_mr_down_translation.acqDir.dirCorresponds.dirReq
      simp[reqToDirOfRequestEvent] at hacq_dir_req
      have hacq_req := hfwd_mr_down_translation.acq.reqTranslation
      simp[ValidRequest.isAcquire] at hacq_req
      simp[hacq_req] at hacq_dir_req
      simp[Event.reqToDirOfRequestEvent] at hacq_dir_req
      simp[hacq_req] at hacq_dir_req
      have h_nc_write : (Event.req n e_dir_shim_acq).val.rw = .w ∧ (Event.req n e_dir_shim_acq).val.coherent = false := by
        match hacq_state_before : EntryState.cache n (stateBefore n b (InitialSystemState.stateAt n init e_shim_acq) e_shim_acq) with
        | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .r, false⟩ | ⟨none, true⟩ | ⟨none, false⟩ =>
          -- Non-Vd cache state: reqToDirOfRequestEvent preserves acquire (rw=.r).
          -- Acquire on SW dir state → Vc (not Vd). The lemma doesn't apply.
          -- These cases may be ruled out by protocol constraints (dir state SW
          -- implies cluster cache has exclusive perms → cache state should be Vd
          -- for the NC read downgrade scenario).
          simp[hacq_state_before] at hacq_dir_req
          simp[hacq_dir_req]; sorry
        | ⟨some .wr, false⟩ =>
          simp[hacq_state_before] at hacq_dir_req
          simp[hacq_dir_req]
      have hdir_acq_not_down :¬Event.down n e_dir_shim_acq = true := by
        have hdir_acq_down_eq_acq_down := hfwd_mr_down_translation.acqDir.dirOfReq
        simp[Event.dirEventOfReqEvent] at hdir_acq_down_eq_acq_down
        match e_dir_shim_acq, e_shim_acq with
        | .directoryEvent de, .cacheEvent ce =>
          simp at hdir_acq_down_eq_acq_down
          have hdir_acq_sameDown_acq := hdir_acq_down_eq_acq_down.sameDown
          have hacq_not_down := hfwd_mr_down_translation.acq.downgrade
          simp[Event.down]
          simp[Event.down] at hdir_acq_sameDown_acq hacq_not_down
          simp[hdir_acq_sameDown_acq, hacq_not_down]
        | .cacheEvent _, .cacheEvent _
        | .directoryEvent _, .directoryEvent _
        | .cacheEvent _, .directoryEvent _ =>
          simp at hdir_acq_down_eq_acq_down
      rw[Behaviour.directory_acq_from_sw_state_eq_stateAfter_vd_append_rest n
        hfwd_mr_down_translation.acqDir.isDir
        hdir_acq_not_down
        h_nc_write
        ]

      rw[← List.append_nil [e_dir_shim_vd_down]]
      rw[Behaviour.directory_vd_downgrade_from_vd_state_eq_stateAfter_vc_append_rest n
        hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
        (by simp [hfwd_mr_down_translation.gDownEncapVdWBDir.downgrade])
        hfwd_mr_down_translation.gDownEncapVdWBDir.reqTranslation
        ]

      -- Now unravel the cache state. We know it's on SW, and gets a MR downgrade, so it will result in MR
      simp[List.stateAfter]
      rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]


      simp[List.stateAfter]

      apply Behaviour.state_after_cluster_dir_on_Vc_and_global_sc_read_le_state_on_SW_of_cmp_swmr
      . case hgdown => exact hgdown
      . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
      . case hsc_read => exact hsc_read
      . case hstate_before_gdown_is_cache_state =>
        simp[stateBefore]
        apply Behaviour.stateAfter_cache_event_is_cache_state
        . case he_is_cache => exact hgdown_cache
        . case hinit_cache =>
          simp[InitialSystemState.stateAt]
          match e_gdown with
          | .cacheEvent _ => simp[EntryState.isCacheState]
          | .directoryEvent _ =>
            simp[Event.isCacheEvent] at hgdown_cache
        . case hall_at_entry => apply Behaviour.eventsUpToEntry_at_e_entry
      . case hstate_before_gdown =>
        simp[cacheStateMadeOn] at hgdown_on_sw
        simp[hgdown_on_sw]
  | Sum.inl s =>
    have : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))).isDirectoryState := Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_directory_state n init hgdown_cache hgdown
    simp [hstate_before_vd] at this
    simp [EntryState.isDirectoryState] at this

lemma Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  {e_dir_shim_vd_down : Event n} {e_gdown : Event n} (hsc_read : e_gdown.isSCRead) (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_cache : e_gdown.isCacheEvent)
  (hgdown_on_sw : Behaviour.cacheStateMadeOn n b init e_gdown = SW)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd n b init e_gdown e_dir_shim_vd_down)
  -- {b : Behaviour n} {init : InitialSystemState n} -- {init_cdir_state : EntryState n}
  -- {e_dir_shim_vd_down e_dir_shim_vc_down : Event n} {e_gdown : Event n}
  -- (hsc_write : e_gdown.isSCWrite) (hgdown_cache : e_gdown.isCacheEvent) (hgdown : e_gdown.isGlobalDowngrade)
  (hdir_on_vd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init  e_gdown e_dir_shim_vd_down e_dir_shim_vc_down)
  -- (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  (hgdown_in_b : e_gdown ∈ b)
  (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  /-
  (hprev_cluster_state_cmp_swmr :
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache →
    Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' n b init e_gcache)-/
  :
  EntryState.state n (Behaviour.stateAfter n b (InitialSystemState.stateAt n init e_dir_shim_vd_down) e_dir_shim_vd_down) ≤
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
  simp[Behaviour.stateAfter]

  rw[ Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore']


  have hdir_vd_same_addr_gdown : Event.sameAddr n e_dir_shim_vd_down e_gdown := by
    have := hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr
    simp_all[Event.sameAddr]
  have hall_encap_not_before_vd : ∀ e ∈ b,
    Event.sameAddr n e e_gdown →
      Event.reqAtCorrespondingGCacheOfCDir n e e_gdown →
      Event.Encapsulates n e_gdown e → ¬Event.OrderedBefore n e e_dir_shim_vd_down := by
    intro e he_in_b he_same_addr_gdown he_at_corr_gdown hgdown_encap_e
    -- [good lemma]
    have he_corr_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e := by
      constructor
      . case clusterMatch =>
        constructor
        . case sameAddr => simp_all[Event.sameAddr]
        . case atCorrCluster =>
          apply Behaviour.event_reqAtCorrespondingGCacheOfCDir_is_correspondingClusterOfGlobalCache
          . case he_req_corr_gcache => exact he_at_corr_gdown
      . case atDir =>
        apply Behaviour.reqAtCorrespondingGCacheOfCDir_is_directory_event
        . case he_req_corr_gcache => exact he_at_corr_gdown
      . case globalEncap => exact hgdown_encap_e
    have he_eq_vd := hfwd_mr_down_translation.onlyVdDir e he_in_b he_corr_gdown
    rw[he_eq_vd]
    intro hvd_ob_vd
    apply Event.contradiction_of_reflexive_ordered_before n hvd_ob_vd
  -- correspondingClusterOfGlobalCache
  rw[Behaviour.state_imm_before_cluster_dir_event_eq_stateBefore_cluster_dir_event n
    e_dir_shim_vd_down hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    hdir_vd_same_addr_gdown hvd_down_in_b
    hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch
    hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
    hall_encap_not_before_vd
    hgdown_in_b
    hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap
    ]

  simp [Shim.Global.toCluster.clusterDirStateBefore, latestDirectoryState.Before.GlobalCache, stateOfSubsingletonEventSet] at hdir_on_vd
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_shim_vd_down


  match hstate_before_vd : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))) with
  | Sum.inr ds => match ds with
    | .SW _ _| .MR _ _ | .Vc _ | .I _
      =>
      simp[hstate_before_vd, EntryState.state, DirectoryState.toState] at hdir_on_vd
    | .Vd ⟨⟨some .wr, false⟩, _⟩ =>
    -- CHECKPOINT
    /-
      have hdir_acq_is_acq_or_weak_write : (Event.req n e_dir_shim_acq).isAcquire ∨ (Event.req n e_dir_shim_acq).isNcWeakWrite := by
        have hacq_dir_req := hfwd_mr_down_translation.acqDir.dirCorresponds.dirReq
        simp[reqToDirOfRequestEvent] at hacq_dir_req

        have hacq_req := hfwd_mr_down_translation.acq.reqTranslation
        simp[ValidRequest.isAcquire] at hacq_req
        simp[hacq_req] at hacq_dir_req
        simp[Event.reqToDirOfRequestEvent] at hacq_dir_req
        simp[hacq_req] at hacq_dir_req

        match hacq_state_before : EntryState.cache n (stateBefore n b (InitialSystemState.stateAt n init e_shim_acq) e_shim_acq) with
        | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .r, false⟩ | ⟨none, true⟩ | ⟨none, false⟩ =>
          simp[hacq_state_before] at hacq_dir_req
          apply Or.intro_left
          simp[ValidRequest.isAcquire,]
          rw[hacq_dir_req]
        | ⟨some .wr, false⟩ =>
          simp[hacq_state_before] at hacq_dir_req
          apply Or.intro_right
          simp[ValidRequest.isNcWeakWrite,]
          rw[hacq_dir_req]
      have hdir_acq_not_down :¬Event.down n e_dir_shim_acq = true := by
        have hdir_acq_down_eq_acq_down := hfwd_mr_down_translation.acqDir.dirOfReq
        simp[Event.dirEventOfReqEvent] at hdir_acq_down_eq_acq_down

        match e_dir_shim_acq, e_shim_acq with
        | .directoryEvent de, .cacheEvent ce =>
          simp at hdir_acq_down_eq_acq_down
          have hdir_acq_sameDown_acq := hdir_acq_down_eq_acq_down.sameDown
          have hacq_not_down := hfwd_mr_down_translation.acq.downgrade
          simp[Event.down]
          simp[Event.down] at hdir_acq_sameDown_acq hacq_not_down
          simp[hdir_acq_sameDown_acq, hacq_not_down]
        | .cacheEvent _, .cacheEvent _
        | .directoryEvent _, .directoryEvent _
        | .cacheEvent _, .directoryEvent _ =>
          simp at hdir_acq_down_eq_acq_down
      rw[Behaviour.directory_acq_from_sw_state_eq_stateAfter_vd_append_rest n
        hfwd_mr_down_translation.acqDir.isDir
        hdir_acq_not_down
        hdir_acq_is_acq_or_weak_write
        ]-/

      rw[← List.append_nil [e_dir_shim_vd_down]]
      rw[Behaviour.directory_vd_downgrade_from_vd_state_eq_stateAfter_vc_append_rest n
        hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
        (by simp [hfwd_mr_down_translation.gDownEncapVdWBDir.downgrade])
        hfwd_mr_down_translation.gDownEncapVdWBDir.reqTranslation
        ]

      -- Now unravel the cache state. We know it's on SW, and gets a MR downgrade, so it will result in MR
      simp[List.stateAfter]
      rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore]


      simp[List.stateAfter]

      apply Behaviour.state_after_cluster_dir_on_Vc_and_global_sc_read_le_state_on_SW_of_cmp_swmr
      . case hgdown => exact hgdown
      . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
      . case hsc_read => exact hsc_read
      . case hstate_before_gdown_is_cache_state =>
        simp[stateBefore]
        apply Behaviour.stateAfter_cache_event_is_cache_state
        . case he_is_cache => exact hgdown_cache
        . case hinit_cache =>
          simp[InitialSystemState.stateAt]
          match e_gdown with
          | .cacheEvent _ => simp[EntryState.isCacheState]
          | .directoryEvent _ =>
            simp[Event.isCacheEvent] at hgdown_cache
        . case hall_at_entry => apply Behaviour.eventsUpToEntry_at_e_entry
      . case hstate_before_gdown =>
        simp[cacheStateMadeOn] at hgdown_on_sw
        simp[hgdown_on_sw]
  | Sum.inl s =>
    have : (eventToEntryState n b init (immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n b e_gdown).toOption
      (Struct.directory (Event.clusterDirProtocolCorrespondingToGlobalCache n e_gdown))).isDirectoryState := Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_directory_state n init hgdown_cache hgdown
    simp [hstate_before_vd] at this
    simp [EntryState.isDirectoryState] at this

lemma CompoundProtocol.noCoherentRead.global_sc_read_downgrade_on_SW_le_cluster_dir_state
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_cache : e_gdown.isCacheEvent)
  (hgdown_read_spec : Event.isSCReadGlobalDowngrade n e_gdown)
  (hgdown_on_sw : Behaviour.cacheStateMadeOn n b init e_gdown = SW)
  (hdir_on_sw : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown SW)
  (hgdown_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW.wrapper n b init e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right
  -- let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose_spec.right
  let hvd_inval_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.left

  /- Identify the event that finishes the last, right before `e_gdown` does. -/
  -- (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  have hevict_imm_finish_before_gdown := Behaviour.noCoherentRead.cluster_dir_vd_downgrade_event_immediately_finish_before_of_global_write_downgrade n
    hgdown_in_b hgdown hvd_inval_in_b htranslation_spec
  let e_dir_shim_vd_down := hgdown_translation.choose_spec.right.choose_spec.right.choose
  let e_dir_shim_vd_down_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.left
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_shim_vd_down_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToEntryState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]

  /- Simp into the state after the coherent read is ≤ the state after the coherent read downgrade. -/
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' e_dir_shim_vd_down hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp

  -- simp [Behaviour.stateAfter]

  apply Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade_on_cluster_SW
  . case hsc_read =>
    exact hgdown_read_spec.isSCRead
  . case hgdown => exact hgdown
  . case hgdown_cache => exact hgdown_cache
  . case hgdown_on_sw => exact hgdown_on_sw
  . case hfwd_mr_down_translation => exact htranslation_spec
  . case hdir_on_sw => exact hdir_on_sw
  . case hgdown_in_b => exact hgdown_in_b

/- adding lemmas for Case `noCoherentRead`, `SC Read Downgrade` on `Vd` state. -/

lemma Behaviour.noCoherentRead.cluster_vd_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_read_downgrade_on_cluster_Vd
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vd_down : Event n}
  (hgdown : e_gdown.isGlobalDowngrade)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd n b init e_gdown e_dir_shim_vd_down)
  : noIntermediateFinishesBeforeOfSameEntry n b e_dir_shim_vd_down e_gdown := by
  simp[noIntermediateFinishesBeforeOfSameEntry]
  intro e_inter hinter_in_b hinter_btn_vdWB_and_gdown

  have hdir_vc_same_struct_inter := hinter_btn_vdWB_and_gdown.sameCidInterPred
  match hdir_vd : e_dir_shim_vd_down, hinter : e_inter with
  | .directoryEvent de_dir_vd_down , .directoryEvent e_dir_shim_vd_down =>
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_dir_vd_down e_dir_shim_vd_down
    have hordered := hdir_ordered.ordered
    simp[DirectoryEvent.Ordered] at hordered
    cases hordered
    . case inl hdir_vc_ob_inter =>
      -- can't have another event between dir_evict and e_gdown ending.
      --Event.Shim.Global.ToCluster.correspondingDirectoryEvent
      -- have test : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := hfwd_sw_down_translation.
      have hinter_dir_of_gdown : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_inter := by
        apply Behaviour.intermediateFinishesBeforeOfSameEntry_correspondingDirectoryEvent_gdown
        . case hdir_vc => exact hdir_vd
        . case hgdown_same_addr_vc_down => simp[hdir_vd, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
        . case hdir_vc_ob_inter => exact hdir_vc_ob_inter
        . case hinter => exact hinter
        . case hgdown_start_before_vc_down => simp[hdir_vd, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap.left]
        . case hinter_btn_vcInval_and_gdown => simp[hdir_vd, hinter, hinter_btn_vdWB_and_gdown]
        . case hgdown => exact hgdown
        . case hvc_down_corr_gdown => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        . case hvc_down_is_dir => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
      have honly_encap_acq_vd := hfwd_mr_down_translation.onlyVdDir
      have hinter_is_dir_vd := honly_encap_acq_vd e_inter (by simp[hinter, hinter_in_b]) hinter_dir_of_gdown
      absurd hinter_btn_vdWB_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_right
      rw[hinter] at hinter_is_dir_vd
      rw[hinter_is_dir_vd]
    . case inr hinter_ob_dir_evict =>
      absurd hinter_btn_vdWB_and_gdown.interPred
      simp[Event.finishesBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp[Event.oEnd]
      calc e_dir_shim_vd_down.oEnd < de_dir_vd_down.oStart := hinter_ob_dir_evict
        _ < de_dir_vd_down.oEnd := de_dir_vd_down.oWellFormed
  | .cacheEvent ce_dir_vc , .directoryEvent de_inter
  | .directoryEvent de_dir_vc , .cacheEvent ce_inter
  | .cacheEvent ce_dir_vc , .cacheEvent ce_inter =>
    have hdir_vc_dir := hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
    simp[Event.struct] at hdir_vc_same_struct_inter
    try simp[Event.isDirectoryEvent] at hdir_vc_dir

lemma Behaviour.noCoherentRead.cluster_dir_vd_downgrade_event_immediately_finish_before_of_global_write_downgrade'
  {b : Behaviour n} {init : InitialSystemState n} {e_gdown e_dir_shim_vd_down : Event n}
  (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvd_down_in_b : e_dir_shim_vd_down ∈ b)
  (hfwd_mr_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd n b init e_gdown e_dir_shim_vd_down)
  : immediateFinishesBeforeAtClusterDirectory n b e_dir_shim_vd_down e_gdown := by
  constructor
  . case finishBefore =>
    constructor
    . case finBefore =>
      constructor
      . case endBefore =>
        simp[Event.finishesBefore, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap.right]
      . case sameAddr =>
        simp[ Event.sameAddr,]
        apply Eq.symm
        simp[← Event.sameAddr.eq_def, hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr]
      . case predInB => exact hvd_down_in_b
      . case succInB => exact hgdown_in_b
    . case gCacheOfCDir =>
      apply Behaviour.global_downgrade_cache_translation_encap_corresponding_request
      . case hgdown => exact hgdown
      . case hrequest_protocol => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
      . case hdir_req_same_protocol_req => rfl
      . case hdir_is_dir => exact hfwd_mr_down_translation.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir
  . case noIntermediate =>
    apply Behaviour.noCoherentRead.cluster_vd_downgrade_has_noIntermediateFinishesBeforeSameEntry_of_global_sc_read_downgrade_on_cluster_Vd
    . case hgdown => exact hgdown
    . case hfwd_mr_down_translation => exact hfwd_mr_down_translation

lemma CompoundProtocol.noCoherentRead.global_sc_read_downgrade_on_Vd_le_cluster_dir_state
  {b : Behaviour n} {init : InitialSystemState n}
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  (hgdown_cache : e_gdown.isCacheEvent)
  (hgdown_read_spec : Event.isSCReadGlobalDowngrade n e_gdown)
  (hgdown_on_sw : Behaviour.cacheStateMadeOn n b init e_gdown = SW)
  (hdir_on_vd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (hgdown_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd.wrapper n b init e_gdown)
  : Behaviour.dirEventStateLeGlobalCacheState' n b init e_gdown := by
  simp[Behaviour.dirEventStateLeGlobalCacheState']

  simp[Behaviour.latestDirectoryStateOfGlobalCache]
  simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

  let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right
  -- let htranslation_spec := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.right.choose_spec.right
  let hvd_inval_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.left

  /- Identify the event that finishes the last, right before `e_gdown` does. -/
  -- (hgdown_in_b : e_gdown ∈ b) (hgdown : e_gdown.isGlobalDowngrade) (hvc_down_in_b : e_dir_shim_vc_down ∈ b)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  have hevict_imm_finish_before_gdown := Behaviour.noCoherentRead.cluster_dir_vd_downgrade_event_immediately_finish_before_of_global_write_downgrade' n
    hgdown_in_b hgdown hvd_inval_in_b htranslation_spec
  let e_dir_shim_vd_down := hgdown_translation.choose_spec.right.choose_spec.right.choose
  let e_dir_shim_vd_down_in_b := hgdown_translation.choose_spec.right.choose_spec.right.choose_spec.left
  rw[Behaviour.event_immediate_finish_before_gdown_singleton n e_dir_shim_vd_down_in_b hevict_imm_finish_before_gdown]
  simp only [Behaviour.stateOfSubsingletonEventSet, Behaviour.eventToEntryState, -- Set.toOption,
    -- nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceDIte, ge_iff_le
    ]

  /- Simp into the state after the coherent read is ≤ the state after the coherent read downgrade. -/
  have hcdir_fin_before_gdown_singleton := Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton n b e_gdown hevict_imm_finish_before_gdown
  have hsingleton := Set.toOption_singleton' e_dir_shim_vd_down hcdir_fin_before_gdown_singleton
  rw[hcdir_fin_before_gdown_singleton] at hsingleton
  rw[hsingleton]
  simp


  apply Behaviour.noCoherentRead.corresponding_cluster_dir_state_le_stateAfter_fwd_mr_downgrade_on_cluster_Vd
  . case hsc_read => exact hgdown_read_spec.isSCRead
  . case hgdown => exact hgdown
  . case hgdown_cache => exact hgdown_cache
  . case hgdown_on_sw => exact hgdown_on_sw
  . case hfwd_mr_down_translation => exact htranslation_spec
  . case hdir_on_vd => exact hdir_on_vd
  . case hgdown_in_b => exact hgdown_in_b
  . case hvd_down_in_b => exact hvd_inval_in_b

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
            . case hgdown_in_b => exact hgdown_in_b
            . case hgdown => exact hgdown
            . case hgdown_write_spec => exact hgdown_write_spec
            . case hdir_on_vd => exact hdir_on_vd
            . case hgdown_translation => exact htranslation
          . case onDirVc hdir_on_vc htranslation =>
            apply CompoundProtocol.noCoherentRead.global_sc_write_downgrade_on_Vc_le_cluster_dir_state
            . case hgdown_in_b => exact hgdown_in_b
            . case hgdown => exact hgdown
            . case hgdown_write_spec => exact hgdown_write_spec
            . case hdir_on_vc => exact hdir_on_vc
            . case hgdown_translation => exact htranslation
        . case scReadDowngrade hgdown_read_spec hgdown_on_sw hgdown_translation =>
          cases hgdown_translation
          . case onDirSW hdir_on_sw htranslation =>
            apply CompoundProtocol.noCoherentRead.global_sc_read_downgrade_on_SW_le_cluster_dir_state
            . case hgdown_in_b => exact hgdown_in_b
            . case hgdown => exact hgdown
            . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
            . case hgdown_read_spec => exact hgdown_read_spec
            . case hgdown_on_sw => exact hgdown_on_sw
            . case hdir_on_sw => exact hdir_on_sw
            . case hgdown_translation => exact htranslation
          . case onDirVd hdir_on_vd htranslation =>
            apply CompoundProtocol.noCoherentRead.global_sc_read_downgrade_on_Vd_le_cluster_dir_state
            . case hgdown_in_b => exact hgdown_in_b
            . case hgdown => exact hgdown
            . case hgdown_cache => exact hgdown.isGlobal.reqAtCache
            . case hgdown_read_spec => exact hgdown_read_spec
            . case hgdown_on_sw => exact hgdown_on_sw
            . case hdir_on_vd => exact hdir_on_vd
            . case hgdown_translation => exact htranslation
