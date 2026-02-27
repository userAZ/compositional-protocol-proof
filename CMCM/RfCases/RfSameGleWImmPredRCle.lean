import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

lemma CMCM.rf.sameGle.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_cluster_cache : e_w.isClusterCache) (hr_cluster_cache : e_r.isClusterCache)
  -- (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_now_down : ¬ e_w.down) (hr_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- Expand Behaviour.readsFrom.cases case so we can prove this specific case.
  apply Behaviour.readsFrom.cases.wEqRGle hsame_gle (hw_cluster := hw_cluster_cache) (hr_cluster := hr_cluster_cache) (hw_not_down := hw_now_down) (hr_not_down := hr_not_down)
  apply Behaviour.readsFrom.wEqRGle.cases.wObRCle

  constructor
  . case hwr_gle_or_cle_case.hw_r_cle_ob =>
    simp[CompoundProtocol.cleImmediatePredecessor, Behaviour.ImmediateBottomPredecessor] at hw_imm_pred_r_cle
    have hw_r_cle_pred := hw_imm_pred_r_cle.isImmPred.bPred.isPred
    simp[Event.Predecessor] at hw_r_cle_pred
    exact hw_r_cle_pred
    -- AZ NOTE: the rest of the cases in this proof are not really important, so I will try them later if I have time. The main case is the same Gle case, which is the first one.
  . case hwr_same_cluster =>
    -- Similar to the same cluster case in the same Gle same Cle case, but now `e_w_cle` is the immediate predecessor of `e_r_cle`
    -- Use the same GLE fact to show `e_w` and `e_r` are in the same protocol cluster.
    -- TODO: Need to implement a 'same_gle_implies_same_protocol'
    /- Do so in a similar way to same_cle_implies_same_protocol.
    Just work from the global protocol first, then work backwards.
    Take the global request. Use an axiom that says a global request comes from a corresponding directory cluster request.
    Use axiom 6.5 to link the directory request back to the `e_w` and `e_r` cluster requests' protocol cluster.

    Thus the GLEs of `e_w` and `e_r` will get mapped to the same protocol cluster through
    1. the fact they have the same GLE,
    2. the global request that caused the GLE comes from a corresponding directory cluster request,
    3. the directory cluster request is linked to the `e_w` and `e_r` cluster requests' protocol cluster. (through axiom 6.5)
    -/
    sorry
  . case hwr_cle_ob_case =>
    by_cases hsame_cache : e_w.struct = e_r.struct
    . case pos =>
      apply WriteRead.wObRCle.case.sameCache hsame_cache
      -- TODO: also show no intervening dir write between the two
      -- Use hw_imm_pred_r_cle to show `e_w_cle` is the immediate predecessor of `e_r_cle`
      sorry
    . case neg =>
      -- TODO: prove the branches in this case.
      -- "different cache" cases.
      -- AZ NOTE: doesn't really matter. try this later, not really important.
      sorry
