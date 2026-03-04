import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetweenHelpers

/-- Proof that reads-from is correct when the GLEs are the same and the CLE relationship
    is evictOrReadBetween (all intermediate directory events between w_cle and r_cle are
    reads or evicts, not writes).

    Unlike the wImmPredRCle case where e_w_cle is immediately before e_r_cle, this case
    allows intermediate directory events (reads/evicts) between the CLEs. The proof follows
    the same structure:
    1. Apply wEqRGle with GLE equality
    2. Apply wObRCle with CLE ordering from evictOrReadBetween.wObR
    3. Same protocol from same_gle_implies_same_protocol
    4. Case split on sameCache / diffCache -/
lemma CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_cluster_cache : e_w.isClusterCache) (hr_cluster_cache : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (hr_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hw_in_b : e_w ∈ b)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- Apply wEqRGle (same GLE) then wObRCle (CLE ordered-before)
  apply Behaviour.readsFrom.cases.wEqRGle hsame_gle
    (hw_cluster := hw_cluster_cache) (hr_cluster := hr_cluster_cache)
    (hw_not_down := hw_not_down) (hr_not_down := hr_not_down)
  apply Behaviour.readsFrom.wEqRGle.cases.wObRCle

  constructor
  . case hwr_gle_or_cle_case.hw_r_cle_ob =>
    -- CLE ordering directly from evictOrReadBetween hypothesis
    exact hevict_or_read_between_w_r_cle.wObR
  . case hwr_same_cluster =>
    -- Same protocol from same GLE (reuse general helper)
    exact same_gle_implies_same_protocol hw_c_and_g_lin hr_c_and_g_lin hsame_gle
  . case hwr_cle_ob_case =>
    by_cases hsame_cache : e_w.struct = e_r.struct
    . case pos =>
      -- Same cache: no intervening directory writes (reuse general helper)
      apply WriteRead.wObRCle.case.sameCache hsame_cache
      exact no_dir_write_between_same_cache hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hsame_cache hknow_dir_access hno_intervening_writes
    . case neg =>
      -- Different cache: delegates to case-specific helpers
      apply WriteRead.wObRCle.case.diffCache hsame_cache
      exact evictOrReadBtn_diff_cache_choose_case hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between_w_r_cle hsame_cache hknow_dir_access
        hw_in_b hw_cluster_cache
