import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleWImmPredRCleHelpers

/-- Proof that reads-from is correct when a write's CLE is the immediate predecessor of a read's CLE.

    Unlike the sameCle case where both events access the same CLE, this case handles:
    - Same GLE (global linearization event) for both events
    - e_w_cle is the immediate predecessor of e_r_cle (directory cluster events)
    - Different cache structures possible

    Sub-goals:
    1. hw_r_cle_ob: Extract immediate predecessor ordering
    2. hwr_same_cluster: Prove same protocol via GLE equality
    3. hwr_cle_ob_case: Prove write-before-read with CLE ordering
       - sameCache: Both at same cache, no intervening writes
       - diffCache: Different caches, analyze coherence and CLE ordering
         * Coherent write: Check for evicts, use noEvictBetween
         * Non-coherent write: Distinguish release vs. other writes
-/

lemma CMCM.rf.sameGle.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_cluster_cache : e_w.isClusterCache) (hr_cluster_cache : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_now_down : ¬ e_w.down) (hr_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hw_in_b : e_w ∈ b)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- Expand Behaviour.readsFrom.cases case so we can prove this specific case.
  apply Behaviour.readsFrom.cases.wEqRGle hsame_gle (hw_cluster := hw_cluster_cache) (hr_cluster := hr_cluster_cache) (hw_not_down := hw_now_down) (hr_not_down := hr_not_down)
  · -- hwr_same_cluster: protocol equality
    exact same_gle_implies_same_protocol hw_c_and_g_lin hr_c_and_g_lin hsame_gle
  · -- hw_eq_r_gle_cases: wObRCle
    apply Behaviour.readsFrom.wEqRGle.cases.wObRCle
    constructor
    . case hwr_gle_or_cle_case.hw_r_cle_ob =>
      -- Extract the ordering from cleImmediatePredecessor
      unfold CompoundProtocol.cleImmediatePredecessor at hw_imm_pred_r_cle
      have : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose :=
        hw_imm_pred_r_cle.isImmPred.bPred.isPred
      exact this
    . case hwr_cle_ob_case =>
      by_cases e_w.struct = e_r.struct
      . case pos hsame_cache =>
        apply WriteRead.wObRCle.case.sameCache hsame_cache
        exact wimmpredrCle_no_dir_write_between_same_cache hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hsame_cache hknow_dir_access hno_intervening_writes
      . case neg hdiff_cache =>
        apply WriteRead.wObRCle.case.diffCache hdiff_cache
        exact wimmpredrCle_diff_cache_choose_case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hknow_dir_access hw_in_b hw_cluster_cache hw_now_down
