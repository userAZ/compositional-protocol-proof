import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleWImmPredRCleHelpers

/-- Proof that reads-from is correct when e_w's GLE is ordered before e_r's GLE,
    both events are in the same cluster, and e_w's CLE is the immediate predecessor of e_r's CLE.

    This parallels the sameGle.wImmPredRCle case, but uses `wObRGle` instead of `wEqRGle`
    since the GLEs are ordered (not equal). The inner structure (CLE ordering, same/diff cache)
    is identical and reuses the same helper lemmas. -/
lemma CMCM.rf.wObRGle.sameCluster.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_ob_r_gle : CompoundProtocol.gleOrderedBefore hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hw_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hw_in_b : e_w ∈ b) (hw_cluster_cache : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- Use wObRGle since GLEs are ordered (immediate predecessor → ordered before)
  apply Behaviour.readsFrom.cases.wObRGle
    hw_ob_r_gle
  -- Extract CLE ordering from rCleOrDownAtWAfterWCle
  -- In the sameCluster case, this must be .sameCluster
  have hw_cle_ob : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose :=
    match hw_imm_pred_r_cle with
    | .sameCluster _ hw_ob_r_cle => hw_ob_r_cle
    | .diffCluster hdiff_prot _ => absurd hsame_cluster hdiff_prot
  refine .sameCluster hsame_cluster ⟨hw_cle_ob, ?_⟩
  -- Same/diff cache case split
  by_cases hsame_cache : e_w.struct = e_r.struct
  · apply WriteRead.wObRCle.case.sameCache hsame_cache
    exact wimmpredrCle_no_dir_write_between_same_cache hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hsame_cache hknow_dir_access
      hno_intervening_writes
  · apply WriteRead.wObRCle.case.diffCache hsame_cache
    exact wimmpredrCle_diff_cache_choose_case hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hsame_cache hknow_dir_access
      hw_in_b hw_cluster_cache hw_not_down
