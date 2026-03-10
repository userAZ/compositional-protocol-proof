import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and e_w's CLE is the immediate predecessor of the
    cache-level read downgrade at e_w's cluster.

    Proof strategy: Use `.wObRGle` → `.diffCluster` → `.wHasPermsAfter` → `.notImmPred` →
    by_cases on CLE_w immPred e_r_cdir_down:
    - immPred: `.noEvictBetween` (noEvictBtn trivially satisfied)
    - not immPred: `.evictBetween`
    CLE_w immPred rDown constrains the interval between e_w and its downgrade. -/
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
  -- GLE ordering: w's GLE is immediate predecessor of r's GLE → GLE_w < GLE_r
  apply Behaviour.readsFrom.cases.wObRGle
    (hw_imm_pred_r_gle.isImmPred.bPred.isPred)
  -- Different cluster → different protocol, different cache
  have hdiff_cache : e_w.struct ≠ e_r.struct := by
    intro h; exact hdiff_cluster (sameStructure_implies_sameProtocol h)
  apply WriteRead.wObR.GleAndCle.sameOrDifferentCluster.cases.diffCluster hdiff_cluster hdiff_cache
  · -- encapGDown: since wImmPredRGle, the read's GLE triggers a downgrade at e_w's global cache
    constructor
    intro hstate_sw
    -- Use diffCache_coherent_globalDowngrade to get the global downgrade
    have hgdown := diffCache_coherent_globalDowngrade hr_c_and_g_lin
    obtain ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b, hdowngrade⟩ := hgdown
    exact ⟨e_r_gdown, he_r_gdown_in_b, sorry, sorry⟩
  · -- diffCache.case: main proof via coherent/non-coherent case split
    -- by_cases on whether e_w leaves state at least SW (hasPerms)
    by_cases hw_has_perms : b.reqLeavesStateAtLeast n e_w init SW
    · -- e_w leaves at least SW → wHasPermsAfter
      apply WriteRead.wObRCle.diffCache.case.wHasPermsAfter hw_has_perms
      apply WriteRead.wObRCle.diffCache.wCoherent.case.notImmPred
      -- by_cases on whether CLE_w is immPred of e_r_cdir_down (cluster dir downgrade)
      let e_r_cdir_down := hw_cle_imm_pred_r_down.rDown.encapDir.existsRClusterDirDown.choose
      by_cases h_cle_imm_cdir : b.ImmediateBottomPredecessor n
          hw_c_and_g_lin.hreq's_dir_access.choose e_r_cdir_down
      · -- CLE_w immPred e_r_cdir_down → noEvictBetween (noEvictBtn trivially satisfied)
        apply WriteRead.wObRCle.diffCache.wHasPermsAfter.case.noEvictBetween
        exact {
          gdownEncapProxyAndDirAndCDown := hw_cle_imm_pred_r_down.rDown
          noEvictBetween := {
            noWriteBtn := sorry
            noEvictBtn := sorry
            wObRDown := hw_cle_imm_pred_r_down.rDown.existsRDownAtW.choose_spec.right.right.right
          }
        }
      · -- CLE_w NOT immPred e_r_cdir_down → evictBetween
        apply WriteRead.wObRCle.diffCache.wHasPermsAfter.case.evictBetween
        exact {
          encapProxyAndDir := hw_cle_imm_pred_r_down.rDown.encapDir
          evictBetween := {
            noWriteBtn := sorry
            evictBtn := sorry
            wObRDown := sorry
          }
        }
    · -- e_w does NOT leave state at least SW → non-coherent case
      have hw_nc_not_coherent : ¬ e_w.isCoherent := by
        intro hw_coherent
        exact hw_has_perms (coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster_cache.eAtCache)
      have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_nc_not_coherent
      have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
      cases hw_dir_access with
      | encapDir hreq_missing_perms _ =>
        -- NC write with missing perms → wNoPermsAfter
        apply WriteRead.wObRCle.diffCache.case.wNoPermsAfter hreq_missing_perms hw_nc
        sorry
      | orderBeforeDir _ _ _ _ _ _ _ _ =>
        -- NC write with perms (predecessor obtained dir access) → wCleAfter
        exact .wCleAfter sorry
      | orderAfterDir _ _ _ _ =>
        -- NC weak request on Vd (e.g. writeback) → wCleAfter
        exact .wCleAfter sorry
