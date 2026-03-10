import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and e_w's CLE is the immediate predecessor of the
    cache-level read downgrade at e_w's cluster.

    This case is vacuously true: `ReadDowngradeAtWrite.wCleImmPredDown` requires
    `ImmediateBottomPredecessor` between a directory event (CLE_w) and a cache event
    (`existsRDownAtW.choose`), but `sameEntry` requires matching `Struct` constructors
    (`.directory` vs `.cache`), which is impossible. -/
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
  -- The hypothesis is uninhabitable: wCleImmPredRDown requires ImmediateBottomPredecessor
  -- between CLE_w (directory event, struct = .directory _) and existsRDownAtW.choose
  -- (cache event, struct = .cache _). sameEntry requires sameStructure, which is impossible.
  exfalso
  have h_same_struct := hw_cle_imm_pred_r_down.wCleImmPredRDown.isImmPred.bPred.sameEntry.sameStruct
  simp [Event.sameStructure] at h_same_struct
  have h_rdown_eq := hw_cle_imm_pred_r_down.rDown.existsRDownAtW.choose_spec.right.left
  rw [h_rdown_eq] at h_same_struct
  -- h_same_struct : CLE_w.struct = e_w.struct
  -- CLE_w is a directory event, e_w is a cache event — different Struct constructors
  have h_dir := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
  have h_cache := hw_cluster_cache.eAtCache
  cases hw_c_and_g_lin.hreq's_dir_access.choose with
  | directoryEvent de =>
    cases e_w with
    | cacheEvent ce => simp [Event.struct] at h_same_struct
    | directoryEvent _ => simp [Event.isCacheEvent] at h_cache
  | cacheEvent _ => simp [Event.isDirectoryEvent] at h_dir
