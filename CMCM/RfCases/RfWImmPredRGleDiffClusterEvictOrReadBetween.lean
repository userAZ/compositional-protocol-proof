import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and all intermediate directory events between e_w's CLE
    and the cache-level read downgrade are reads or evicts.

    This case is vacuously true: `evictOrReadBetween.wAndRDown.wCleImmPredRDown` quantifies
    over ALL events in `b`, including CLE_w itself. Applying it to CLE_w yields
    `IntermediateDirEvictOrRead CLE_w CLE_w rDown.choose`, which requires
    `CLE_w.OrderedBetween n CLE_w rDown.choose`, whose `.pred` field gives
    `CLE_w.oEnd < CLE_w.oStart`. This contradicts `CLE_w.oWellFormed : CLE_w.oStart < CLE_w.oEnd`. -/
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
  -- The hypothesis is uninhabitable: wCleImmPredRDown applied to CLE_w (which is in b)
  -- yields IntermediateDirEvictOrRead CLE_w CLE_w rDown.choose, which requires
  -- CLE_w.OrderedBetween n CLE_w rDown.choose. The .pred field gives
  -- CLE_w.oEnd < CLE_w.oStart, contradicting CLE_w.oWellFormed (CLE_w.oStart < CLE_w.oEnd).
  exfalso
  have h_cle_in_b := hw_c_and_g_lin.hreq's_dir_access.choose_spec.left
  have h_inter := hw_cle_imm_pred_down.wCleImmPredRDown _ h_cle_in_b
  have h_ob_self := h_inter.betweenWR.pred
  have h_wf := hw_c_and_g_lin.hreq's_dir_access.choose.oWellFormed
  simp [Event.OrderedBefore] at h_ob_self
  omega
