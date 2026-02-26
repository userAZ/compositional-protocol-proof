import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

lemma CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry
