import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetweenHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and all intermediate directory events between e_w's CLE
    and the directory-level read downgrade are reads or evicts.

    Uses the `diffCluster` constructor of `sameOrDifferentCluster.cases` with
    `wHasPermsAfter.notImmPred.evictBetween` for the coherent case. -/
lemma CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_down : ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hw_in_b : e_w ∈ b) (hw_cluster_cache : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- GLE_w is ordered before GLE_r (from immediate predecessor)
  apply Behaviour.readsFrom.cases.wObRGle
    (hw_imm_pred_r_gle.isImmPred.bPred.isPred)
  -- Different cluster → different cache
  have hdiff_cache : e_w.struct ≠ e_r.struct :=
    fun h => hdiff_cluster (sameStructure_implies_sameProtocol h)
  refine .diffCluster (r_is_read := hr_is_read) hdiff_cluster hdiff_cache ?_ ?_
  · -- encapGDown: same proof as wCleImmPredDown case
    constructor
    intro hstate_sw
    have ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, h_wrapper⟩ :=
      diffCache_coherent_globalDowngrade hr_c_and_g_lin
    have h_dpow := h_wrapper.downgradePrevOwner
    have h_at_prev := h_dpow.atPrevOwner
    have h_fwd := h_dpow.fwdFromRequester
    have h_is_cache := h_dpow.downAtCache
    unfold Behaviour.directoryStateMadeOn at hstate_sw
    rw [hstate_sw] at h_at_prev
    cases e_r_gdown with
    | directoryEvent de =>
      exact absurd h_is_cache (by simp [Event.isCacheEvent])
    | cacheEvent ce =>
      refine ⟨.cacheEvent ce, he_r_gdown_in_b, ?_, ?_⟩
      · simp only [Event.downgradeAtPrevOwner] at h_at_prev
        simp only [Event.cid]
        exact h_at_prev
      · exact downgradeCorrespondingToRequest_isDown h_fwd
  · -- diffCache.case
    by_cases hw_coherent : e_w.isCoherent
    · -- Coherent case: write has permissions after, use evictBetween
      have hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW :=
        coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster_cache.eAtCache
      refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.evictBetween ⟨hw_cle_imm_pred_down.rDown.encapDir, ?_, ?_, hw_cle_imm_pred_down.wObRDown⟩))
      · -- noWriteBtn: Event.Between.noDirWrite
        -- From hw_cle_imm_pred_down.wCleImmPredRDown: all intermediate dir events between
        -- e_w_cle and e_r_cdir_down are reads or evicts (not writes).
        -- Any hypothetical dir write between them contradicts this.
        sorry
      · -- evictBtn: Event.Between.dirEvict b e_w_cle e_r_cdir_down
        -- There exists a dir evict event between e_w_cle and e_r_cdir_down.
        -- From hw_cle_imm_pred_down.wCleImmPredRDown, intermediate events are reads or evicts.
        -- At least one must be an evict (since we're in the evictOrReadBetween case,
        -- not the wCleImmPredDown case where e_w_cle is the immediate predecessor).
        sorry
    · -- Non-coherent case: split on directory access structure
      have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
      have hr_cle_after : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin := by
        sorry -- Derive from e_w_cle < e_r_cdir_down < e_r_cle ordering chain
      have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
      cases hw_dir_access with
      | encapDir hreq_missing_perms _ =>
        exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
      | orderBeforeDir _ _ _ _ _ _ _ _ =>
        exact .wCleAfter hr_cle_after
      | orderAfterDir _ _ _ _ =>
        exact .wCleAfter hr_cle_after
