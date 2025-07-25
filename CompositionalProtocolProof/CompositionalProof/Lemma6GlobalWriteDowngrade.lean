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
            simp [hde, hde_c, Event.reqAtGlobalCache, hcid] at hcdir_at_gcache he_at_gcache
          | .cache pci =>
            match pci with
            | .globalP fin2 =>
              simp_all [hde, hde_c, Event.reqAtGlobalCache, hcid]
            | .cluster1 fin | .cluster2 fin =>
              simp [hde, hde_c, Event.reqAtGlobalCache, hcid] at hcdir_at_gcache he_at_gcache
      | .cacheEvent ce_e, .directoryEvent de_c, .cacheEvent ce_g
      | .cacheEvent ce_e, .cacheEvent ce_c, .cacheEvent ce_g
      | .directoryEvent de_e, .cacheEvent ce_c, .cacheEvent ce_g
      | .cacheEvent ce_e, .directoryEvent de_c, .directoryEvent de_g
      | .cacheEvent ce_e, .cacheEvent ce_c, .directoryEvent de_g
      | .directoryEvent de_e, .cacheEvent ce_c, .directoryEvent de_g
      | .directoryEvent de_e, .directoryEvent de_c, .directoryEvent de_g
        =>
        all_goals simp [he, hecdir, Event.reqAtGlobalCache, hegdown] at hcdir_at_gcache he_at_gcache
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
          all_goals simp [hde_e, hde_c, Event.reqAtGlobalCache] at hcdir_at_gcache he_at_gcache

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

lemma Behaviour.cluster_dir_event_immediately_finish_before_of_global_downgrade
  {b : Behaviour n} (e_cdir e_gdown : Event n)
  : immediateFinishesBeforeAtClusterDirectory n b e_cdir e_gdown := by
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
  sorry

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
      simp[Behaviour.dirEventStateLeGlobalCacheState']
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
          simp [Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper] at hgdown_translation
          have hwrite_down_translation := hgdown_translation.choose_spec.right.scGDownTranslation
          simp[Behaviour.encapCorrespondingGetSWAndEvictWrapper] at hwrite_down_translation
          have htranslation_spec := hwrite_down_translation.choose_spec.right.choose_spec.right.choose_spec.choose_spec.right
          let coh_evict := hwrite_down_translation.choose_spec.right.choose_spec.right.choose_spec.choose
          let hcoh_evict_in_b := hwrite_down_translation.choose_spec.right.choose_spec.right.choose_spec.choose_spec.left
          have htrans_coherent_evict_sw := htranslation_spec.cohEvict
          /- Now, this Coherent SW Evict's corresponding Directory Event is the last Directory Event that finishes before `e_gdown`.
          There are no others, -/
          simp[Behaviour.latestDirectoryStateOfGlobalCache]
          simp[Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents]

          have hevict_imm_finish_before_gdown := b.cluster_dir_event_immediately_finish_before_of_global_downgrade n coh_evict e_gdown
          rw[Behaviour.event_immediate_finish_before_gdown_singleton n hcoh_evict_in_b hevict_imm_finish_before_gdown]
          simp[Behaviour.stateOfSubsingletonEventSet, Set.toOption, Behaviour.eventToState]
          /- show the state after the evict `e_shim_coh_evict` (in the ⋯) is always ≤ the state after `e_gdown`.
          `e_shim_coh_evict` brings the Cluster Directory state down to `I` (get SW then evict SW to I).
          `e_gdown` is a downgrade at the Global Cache (fwd get M / SW), and will bring the Global cache to `I`. -/
          /- are the `Behaviour.stateAfter` definitions easy to work with? Maybe I need helper lemmas to make
          definitions like `stateAfter` easier to work with -/
          sorry
        . case scReadDown hgdown_read_spec hgdown_translation =>
          sorry
      . case noCoherentRead =>
        sorry
      -- have hglobal_swmr := cmp.globalSWMR
