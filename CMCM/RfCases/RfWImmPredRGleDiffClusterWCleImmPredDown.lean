import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleWImmPredRCleHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and e_w's CLE is the immediate predecessor of the
    directory-level read downgrade at e_w's protocol.

    Uses the `diffCluster` constructor of `sameOrDifferentCluster.cases` with
    `wHasPermsAfter.notImmPred.noEvictBetween` for the coherent case. -/
lemma CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
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
  · -- encapGDown
    constructor
    intro hstate_sw
    have ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, h_wrapper⟩ :=
      diffCache_coherent_globalDowngrade hr_c_and_g_lin
    have h_dpow := h_wrapper.downgradePrevOwner
    have h_at_prev := h_dpow.atPrevOwner
    have h_fwd := h_dpow.fwdFromRequester
    have h_is_cache := h_dpow.downAtCache
    -- hstate_sw says directoryStateMadeOn = .SW with owner e_w.gCacheOfCEvent
    -- atPrevOwner uses the same (b.stateBefore ...).directory = directoryStateMadeOn
    unfold Behaviour.directoryStateMadeOn at hstate_sw
    rw [hstate_sw] at h_at_prev
    -- h_at_prev : e_r_gdown.downgradeAtPrevOwner n (.SW ⟨SW, _⟩ e_w.gCacheOfCEvent)
    -- Case-split: e_r_gdown must be a cache event (from downAtCache)
    cases e_r_gdown with
    | directoryEvent de =>
      exact absurd h_is_cache (by simp [Event.isCacheEvent])
    | cacheEvent ce =>
      refine ⟨.cacheEvent ce, he_r_gdown_in_b, ?_, ?_⟩
      · -- ce.cid = e_w.gCacheOfCEvent (from downgradeAtPrevOwner on .SW state)
        simp only [Event.downgradeAtPrevOwner] at h_at_prev
        simp only [Event.cid]
        exact h_at_prev
      · -- ce.down (from downgradeCorrespondingToRequest → downgradeOfReq.isDown)
        exact downgradeCorrespondingToRequest_isDown h_fwd
  · -- diffCache.case
    -- Note 1: by_cases on whether e_w leaves SW state (permissions after).
    -- This separates wHasPermsAfter (leaves SW) from wNoPermsAfter/wCleAfter (doesn't).
    by_cases hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW
    · -- e_w leaves SW state → use wHasPermsAfter
      -- Note 2: by_cases on whether e_w's CLE is immPred of e_r's cluster downgrade.
      -- We know immPred is TRUE from hw_cle_imm_pred_r_down.wCleImmPredRDown.
      -- This selects .noEvictBetween (nothing between immPred pair, so noWrite/noEvict are easy).
      refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.noEvictBetween ⟨hw_cle_imm_pred_r_down.rDown, ?_, ?_, hw_cle_imm_pred_r_down.rDown.existsRDownAtW.choose_spec.right.right.right⟩))
      · -- noWriteBtn: Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cdir_down
        -- For each cluster-cache write e_inter, show excludeOtherWrites using immPred:
        --   ImmediateBottomPredecessor says no bottom dir event at the same entry as
        --   e_r_cdir_down can be OrderedBetween e_w_cle and e_r_cdir_down.
        --   All three excludeOtherWrites cases involve a dir event at e_w's cluster directory
        --   (same entry as e_r_cdir_down), so immPred excludes them.
        -- noWriteBtn: Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cdir_down
        -- Strategy: Use otherWDiffCluster for ALL e_inter.
        -- For same-protocol e_inter: dirWriteDowngradeFromDiffCluster.diffProtocol fails → ∃ vacuously false.
        -- For diff-protocol e_inter: use hw_cle_imm_pred_r_down.wCleImmPredRDown.isImmPred.noIntermediate
        --   to show any bottom dir event with sameEntry to e_r_cdir_down cannot be between e_w_cle and e_r_cdir_down.
        --   Need: directory_event_is_bottom + sameEntry (sameStruct from sameProtocol + sameAddr).
        -- Requires: sameAddr lemma connecting dirWriteDowngradeFromDiffCluster to e_r_cdir_down.
        sorry
      · -- noEvictBtn: Event.Between.noEvict b e_w e_r_down
        -- Strategy: Event.Between requires coherentRead (e_r_down.isCoherent) and
        --   sameCache (e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r_down).
        -- If e_r_down is not coherent, Between is vacuously False → noEvict trivially holds.
        -- Otherwise: use hw_cle_imm_pred_r_down.wCleImmPredRDown.isImmPred.noIntermediate + the fact
        --   that an evict's CLE is a bottom dir event at the same entry → cannot be between.
        -- See RfSameGleSameCle.lean for the 9-case dirAccessOfRequest analysis pattern.
        sorry
    · -- e_w does NOT leave SW state → use wNoPermsAfter or wCleAfter
      -- These don't require noWriteBtn/noEvictBtn, just rCleAfterWCle.
      have hr_cle_after : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin := by
        sorry -- TODO: derive from GLE ordering chain via gle_ordered_implies_cle_ordered
      have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
      cases hw_dir_access with
      | encapDir hreq_missing_perms _ =>
        have hw_not_coherent : ¬ e_w.isCoherent := fun h_coh =>
          hw_leaves_SW (coherent_write_leaves_at_least_SW hw_is_write h_coh hw_not_down hw_cluster_cache.eAtCache)
        have hw_nc := isNonCoherent_of_not_isCoherent_write hw_is_write hw_not_coherent
        exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
      | orderBeforeDir _ _ _ _ _ _ _ _ =>
        exact .wCleAfter hr_cle_after
      | orderAfterDir _ _ _ _ =>
        exact .wCleAfter hr_cle_after
