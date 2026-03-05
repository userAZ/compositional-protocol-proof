import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

import CMCM.RfCases.RfSameGleSameCle
import CMCM.RfCases.RfSameGleWImmPredRCle
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWImmPredRGleSameClusterWImmPredRCle
import CMCM.RfCases.RfWImmPredRGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWImmPredRGleDiffClusterWCleImmPredDown
import CMCM.RfCases.RfWImmPredRGleDiffClusterEvictOrReadBetween

variable {n : ℕ}

theorem CMCM.rf_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  {hw_in_b : e_w ∈ b}
  {hsame_addr : e_w.sameAddr n e_r}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  /- Synchronization conditions -/
  (hgle_cle_rf_constraints : CompoundProtocol.gleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- probably want to start with cases of `e_w` and `e_r`'s GLEs.
  -- Only expand cases of `e_w` and `e_r`'s requests (coherent, non-coherent, release, acquire...) further into the subcases.

  let e_w_gle := hw_c_and_g_lin.hreq's_global_lin.choose
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose


  let test := hw_c_and_g_lin.hreq's_global_lin.choose_spec.right.isDirEvent

  cases hgle_cle_rf_constraints
  . case sameGle hsame_gle hcle_cases =>
    cases hcle_cases
    . case wEqRCle hsame_cle =>
      apply CMCM.rf.sameGle.sameCle hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) (hw_not_down := hw_not_down) (hr_not_down := hr_not_down) (hr_not_ob_w := hr_not_ob_w) hknow_dir_access hno_intervening_writes hsucc_w_of_w_after_r
    . case otherCases hsame_as_gle_ob_cases =>
      cases hsame_as_gle_ob_cases
      . case wImmPredRCle hw_imm_pred_r_cle =>
        apply CMCM.rf.sameGle.wImmPredRCle
          hw_cluster hr_cluster
          hw_is_write hr_is_read
          hw_not_down hr_not_down
          hw_c_and_g_lin hr_c_and_g_lin
          hsame_gle hw_imm_pred_r_cle
          hknow_dir_access hno_intervening_writes
          hw_in_b
      . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
        apply CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
          hw_cluster hr_cluster
          hw_is_write hr_is_read
          hw_not_down hr_not_down
          hw_c_and_g_lin hr_c_and_g_lin
          hsame_gle hevict_or_read_between_w_r_cle
          hknow_dir_access hno_intervening_writes
          hw_in_b
  . case wImmPredRGle hw_imm_pred_r_gle hcle_cases =>
      cases hcle_cases
      . case sameCluster hsame_cluster hsame_cluster_cases =>
        -- NOTE: potential to reuse some of the same cluster case lemmas
        -- from the same GLE & CLE case
        cases hsame_cluster_cases
        . case wImmPredRCle hw_imm_pred_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.wImmPredRCle hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hw_imm_pred_r_cle => exact hw_imm_pred_r_cle
        . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hevict_or_read_between_w_r_cle => exact hevict_or_read_between_w_r_cle
      . case diffCluster hdiff_cluster hdiff_cluster_cases =>
        cases hdiff_cluster_cases
        . case wCleImmPredDown hw_cle_imm_pred_r_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_r_down => exact hw_cle_imm_pred_r_down
        . case evictOrReadBetweenWAndRDown hw_cle_imm_pred_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_down => exact hw_cle_imm_pred_down
