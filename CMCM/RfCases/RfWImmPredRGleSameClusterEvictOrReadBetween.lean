import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

lemma CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry
