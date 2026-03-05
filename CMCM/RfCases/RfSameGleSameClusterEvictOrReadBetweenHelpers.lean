/-
  Helper lemmas specifically for the `rf.sameGle.evictOrReadBetweenWAndRCleSameCluster` case
  (same GLE, same cluster, with evicts/reads between write's and read's CLEs).

  These lemmas handle the diffCache subcase for the evictOrReadBetween CLE relationship.
  The sameCache subcase uses the general `no_dir_write_between_same_cache` from RfProofHelpers.

  General helpers (same_gle_implies_same_protocol, diffCache_coherent_globalDowngrade,
  globalToCluster_extract_proxy_and_dir, diffCache_coherent_encapProxyAndDir,
  no_dir_write_between_same_cache) are in RfProofHelpers.lean for reuse across cases.
-/
import CMCM.RfProofHelpers

variable {n : ℕ}

/-- Helper: When e_w's CLE has evicts/reads between it and e_r's CLE,
    e_r's CLE is ordered after e_w's CLE (rCleAfterWCle).
    Extracted directly from the evictOrReadBetween.wObR field. -/
lemma evictOrReadBtn_diffCache_rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
  hevict_or_read_between.wObR

/-- Helper: No cache-level evict-SW between e_w and the cache-level downgrade e_r_down.

    With evictOrReadBetween, all intermediate events between w_cle and r_cle are reads/evicts
    (not write-downgrades). An evict-SW at the same cache between e_w and e_r_down would
    need to have a CLE between e_w_cle and e_r_cle — but such an evict is permitted by
    the evictOrReadBetween hypothesis (it could be a dir-read/evict). The key argument is
    that any such evict must not be a cache-level evict-SW that changes the ownership state,
    which the interDirEvictOrRead condition constrains. -/
lemma evictOrReadBtn_diffCache_noEvictBetween_noEvict
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noEvict b e_w hencapPDC.existsRDownAtW.choose := by
  sorry

/-- Helper: Every intervening write between e_w and e_r_down falls into one of the three
    excludeOtherWrites cases. With evictOrReadBetween, intermediate directory events are
    reads/evicts, so any write's CLE (a dir-write) between the CLE boundaries would
    contradict the interDirEvictOrRead condition. -/
lemma evictOrReadBtn_diffCache_noEvictBetween_noWrite
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noWrite b init e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := by
  -- noWrite quantifies over all cluster cache writes (not down).
  -- For each e_inter, case-split on same cache / diff cache same cluster / diff cluster.
  -- In same cache and diff-cache-same-cluster cases, pick e_w_cle as the existential
  -- witness for interCleNotBetween. The antecedent requires e_w_cle.OrderedBetween
  -- e_w_cle e_r_cdir_down, whose first component e_w_cle < e_w_cle is reflexive → contradiction.
  have hr_down_struct := hencapPDC.existsRDownAtW.choose_spec.right.left
  have he_w_cle_in_b := hw_c_and_g_lin.hreq's_dir_access.choose_spec.left
  intro e_inter _hinter_in_b _hinter_cluster _hinter_write hinter_not_down
  by_cases h_same_cache : e_inter.struct = e_w.struct
  · -- Same cache → otherWSameCache
    have hsame_w : e_inter.sameStructure n e_w := by unfold Event.sameStructure; exact h_same_cache
    have hsame_r : e_inter.sameStructure n hencapPDC.existsRDownAtW.choose := by
      unfold Event.sameStructure; exact h_same_cache.trans hr_down_struct.symm
    exact .otherWSameCache {
      notDown := hinter_not_down
      sameProtocol := ⟨sameStructure_implies_sameProtocol hsame_w,
                       sameStructure_implies_sameProtocol hsame_r⟩
      sameCache := ⟨hsame_w, hsame_r⟩
      interCleNotBetween := ⟨hw_c_and_g_lin.hreq's_dir_access.choose, he_w_cle_in_b,
        fun _ => fun ⟨_, hcle_ob⟩ => Event.contradiction_of_reflexive_ordered_before n hcle_ob.pred⟩
    }
  · by_cases h_same_proto : e_inter.protocol = e_w.protocol
    · -- Different cache, same cluster → otherWDiffCacheSameCluster
      have hr_down_proto : hencapPDC.existsRDownAtW.choose.protocol = e_w.protocol :=
        sameStructure_implies_sameProtocol (by unfold Event.sameStructure; exact hr_down_struct)
      exact .otherWDiffCacheSameCluster {
        sameProtocol := ⟨by unfold Event.sameProtocol; exact h_same_proto,
                         by unfold Event.sameProtocol; exact h_same_proto.trans hr_down_proto.symm⟩
        diffCache := ⟨by unfold Event.diffStructure; exact h_same_cache,
                      by unfold Event.diffStructure; intro heq; exact h_same_cache (heq.trans hr_down_struct)⟩
        interCleNotBetween := ⟨hw_c_and_g_lin.hreq's_dir_access.choose, he_w_cle_in_b,
          fun _ => fun hob => Event.contradiction_of_reflexive_ordered_before n hob.pred⟩
      }
    · -- Different cluster → otherWDiffCluster
      exact .otherWDiffCluster {
        interCleNotBetween := by
          -- Need: ¬ ∃ e_inter_down, dirWriteDowngradeFromDiffCluster ∧ OrderedBetween
          -- An e_inter_down from diff cluster would be a dir write-downgrade at e_w's protocol,
          -- between e_w_cle and e_r_cdir_down. By interDirEvictOrRead from evictOrReadBetween,
          -- all dir events between e_w_cle and e_r_cle are dir-reads. Since e_r_cdir_down is
          -- encapsulated by e_r_cle, e_inter_down between e_w_cle and e_r_cdir_down should also
          -- be constrained. However, the precise ordering relationship between e_r_cdir_down and
          -- e_r_cle needs further analysis.
          sorry
      }

/-- Construct the noEvictBetween.cond for the evictOrReadBetween case.
    Fields:
    - wObRDown: from hencapPDC.existsRDownAtW
    - noEvictBtn: from evictOrReadBtn_diffCache_noEvictBetween_noEvict
    - noWriteBtn: from evictOrReadBtn_diffCache_noEvictBetween_noWrite -/
lemma evictOrReadBtn_diffCache_noEvictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : WriteRead.noEvictBetween.cond b init
      e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := {
    wObRDown := hencapPDC.existsRDownAtW.choose_spec.right.right.right
    noEvictBtn := evictOrReadBtn_diffCache_noEvictBetween_noEvict hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
    noWriteBtn := evictOrReadBtn_diffCache_noEvictBetween_noWrite hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
  }

/-- No directory-level write between e_w_cle and e_r_cdir_down.
    With evictOrReadBetween, intermediate events are reads/evicts, so no directory write
    from a same-cluster or diff-cluster write can be between the boundaries. -/
lemma evictOrReadBtn_diffCache_evictBetween_noWriteBtn
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Event.Between.noDirWrite cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := by
  sorry

/-- e_w_cle is ordered before e_r_cdir_down.
    With evictOrReadBetween, we have e_w_cle ordered before e_r_cle (from wObR).
    The downgrade chain from e_r's GLE produces e_r_cdir_down at e_w's cluster directory.
    The ordering e_w_cle < e_r_cdir_down follows from the protocol structure. -/
lemma evictOrReadBtn_diffCache_evictBetween_wObRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
      hencapPD.existsRClusterDirDown.choose := by
  -- e_w_cle < e_r_cle (from evictOrReadBetween.wObR)
  have hpred := hevict_or_read_between.wObR
  -- e_r_cle ≻ e_r_cdir_down (from encapProxyAndDir)
  have hencap := hencapPD.existsRClusterDirDown.choose_spec.right.right.right
  -- By Trans (OrderedBefore ∘ Encapsulates → OrderedBefore)
  exact Trans.trans hpred hencap

/-- Construct the evictBetween.cond for the evictOrReadBetween case.
    Fields:
    - noWriteBtn: from evictOrReadBtn_diffCache_evictBetween_noWriteBtn
    - evictBtn: trivially satisfiable (pick e_w_cle, antecedent OrderedBetween → False)
    - wObRDown: from evictOrReadBtn_diffCache_evictBetween_wObRDown -/
lemma evictOrReadBtn_diffCache_evictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_cdown : ¬ ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down)
  : WriteRead.evictBetween.cond cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := {
    noWriteBtn := evictOrReadBtn_diffCache_evictBetween_noWriteBtn hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent
      hencapPD hknow_dir_access
    evictBtn := ⟨hw_c_and_g_lin.hreq's_dir_access.choose,
      hw_c_and_g_lin.hreq's_dir_access.choose_spec.left,
      fun h => (Event.contradiction_of_reflexive_ordered_before n h.pred).elim⟩
    wObRDown := evictOrReadBtn_diffCache_evictBetween_wObRDown
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hencapPD
  }

/-- Coherent write at a different cache with evictOrReadBetween CLE relationship.
    Builds the wHasPermsAfter.case by constructing the downgrade chain from the read's GLE
    down to e_w's cache, then deciding between noEvictBetween and evictBetween. -/
lemma evictOrReadBtn_diffCache_coherent_wHasPermsAfter_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
      hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Step 1: Construct the global + cluster level downgrade chain (reuse general helper)
  have hencapPD := diffCache_coherent_encapProxyAndDir
    hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
  -- Step 2: noEvictBetween or evictBetween
  by_cases hcdown : ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  · -- noEvictBetween: downgrade reaches e_w's cache directly
    let hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin :=
      { encapProxyAndDir := hencapPD, existsRDownAtW := hcdown }
    exact .noEvictBetween {
      gdownEncapProxyAndDirAndCDown := hencapPDC
      noEvictBetween := evictOrReadBtn_diffCache_noEvictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
    }
  · -- evictBetween: cache was evicted, downgrade only reaches cluster directory level
    exact .evictBetween {
      encapProxyAndDir := hencapPD
      evictBetween := evictOrReadBtn_diffCache_evictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent
        hencapPD hknow_dir_access hcdown
    }

/-- diffCache case decision for evictOrReadBetween: coherent vs non-coherent write.
    - Coherent write → wHasPermsAfter
    - Non-coherent write → case split on dirAccessOfRequest:
      - encapDir → wNoPermsAfter
      - orderBeforeDir or orderAfterDir → wCleAfter -/
lemma evictOrReadBtn_diff_cache_choose_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Extract rCleAfterWCle from evictOrReadBetween.wObR
  have hr_cle_after := evictOrReadBtn_diffCache_rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter with notImmPred (evictOrReadBetween case)
    exact .wHasPermsAfter hw_coherent
      (.notImmPred (evictOrReadBtn_diffCache_coherent_wHasPermsAfter_case hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hknow_dir_access
        hw_in_b hw_cluster))
  · -- Non-coherent write: use rCleAfterWCle for the new constructors
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      exact .wCleAfter hr_cle_after
    | orderAfterDir _ _ _ _ =>
      exact .wCleAfter hr_cle_after
