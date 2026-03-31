import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

import CMCM.RfCases.RfSameGleSameCle
import CMCM.RfCases.RfSameGleWImmPredRCle
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWObRGleSameClusterWImmPredRCle
import CMCM.RfCases.RfWObRGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWObRGleDiffClusterWCleImmPredDown
import CMCM.RfCases.RfWObRGleDiffClusterEvictOrReadBetween

variable {n : ℕ}

/-! # CO Theorem: Coherence Order from Protocol Axioms

Analogous to `CMCM.rf_holds` (RfTheorem.lean), but for two writes instead of
a write and a read. The directory serializes writes at the same address, giving
`co.ordering` (sameCache / sameClusDiffCache / diffClus).

The proof structure is a carbon copy of the RF theorem:
- Case-split on GLE ordering (sameGle vs wObRGle)
- Within each, case-split on CLE ordering
- Delegate to the same RF case helper infrastructure (which works for any
  pair of cluster cache events, not just write+read)
-/

theorem CMCM.co_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w1 e_w2 : Event n}
  {hw1_cluster : e_w1.isClusterCache} {hw2_cluster : e_w2.isClusterCache}
  (hw1_is_write : e_w1.isWrite) (hw2_is_write : e_w2.isWrite)
  {hw1_not_down : ¬ e_w1.down} {hw2_not_down : ¬ e_w2.down}
  {hw1_in_b : e_w1 ∈ b}
  {hsame_addr : e_w1.sameAddr n e_w2}
  (hw1_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w1)
  (hw2_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w2)
  /- Synchronization conditions (same structure as RF) -/
  (hgle_cle_constraints : CompoundProtocol.gleOrdering.Cases hw1_lin hw2_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw1_is_write hw2_is_write hw1_lin hw2_lin hknow_dir_access)
  (hw2_not_ob_w1 : ¬ e_w2.OrderedBefore n e_w1)
  (hsucc_w_of_w1_after_w2 : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w1 ∧ e_w_succ.sameStructure n e_w1 ∧
    e_w1.OrderedBefore n e_w_succ → e_w2.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw1_is_write hw2_is_write hw1_lin hw2_lin hknow_dir_access
  := by
  -- Carbon copy of rf_holds: case-split on GLE ordering, delegate to same helpers.
  -- The RF case helpers work for any pair of cluster cache events (write+write works).
  cases hgle_cle_constraints
  . case sameGle hsame_gle hcle_cases =>
    cases hcle_cases
    . case wEqRCle hsame_cle =>
      apply CMCM.rf.sameGle.sameCle hw1_lin hw2_lin hsame_gle hsame_cle (hw_cluster := hw1_cluster) (hr_cluster := hw2_cluster) (hw_not_down := hw1_not_down) (hr_not_down := hw2_not_down) (hr_not_ob_w := hw2_not_ob_w1) hknow_dir_access hno_intervening_writes hsucc_w_of_w1_after_w2
    . case otherCases hsame_as_gle_ob_cases =>
      cases hsame_as_gle_ob_cases
      . case wImmPredRCle hw_imm_pred_r_cle =>
        apply CMCM.rf.sameGle.wImmPredRCle
          hw1_cluster hw2_cluster
          hw1_is_write hw2_is_write
          hw1_not_down hw2_not_down
          hw1_lin hw2_lin
          hsame_gle hw_imm_pred_r_cle
          hknow_dir_access hno_intervening_writes
          hw1_in_b
      . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between =>
        apply CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
          hw1_cluster hw2_cluster
          hw1_is_write hw2_is_write
          hw1_not_down hw2_not_down
          hw1_lin hw2_lin
          hsame_gle hevict_or_read_between
          hknow_dir_access hno_intervening_writes
          hw1_in_b
  . case wObRGle hw_ob_r_gle hcle_cases =>
      cases hcle_cases
      . case sameCluster hsame_cluster hsame_cluster_cases =>
        cases hsame_cluster_cases
        . case wImmPredRCle hw_imm_pred_r_cle =>
          exact CMCM.rf.wObRGle.sameCluster.wImmPredRCle
            hw1_lin hw2_lin
            hw_ob_r_gle hsame_cluster hw_imm_pred_r_cle
            hno_intervening_writes hw1_in_b hw1_cluster hw1_not_down
        . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between =>
          exact CMCM.rf.wObRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster
            hw1_lin hw2_lin
            hw_ob_r_gle hsame_cluster hevict_or_read_between
            hno_intervening_writes hw1_in_b hw1_cluster hw1_not_down
      . case diffCluster hdiff_cluster hdiff_cluster_cases =>
        cases hdiff_cluster_cases
        . case wCleImmPredDown hw_cle_imm_pred_down =>
          exact CMCM.rf.wObRGle.diffCluster.wCleImmPredDown
            hw1_lin hw2_lin
            hw_ob_r_gle hdiff_cluster hw_cle_imm_pred_down
            hknow_dir_access hno_intervening_writes hw1_in_b hw1_cluster hw1_not_down
        . case evictOrReadBetweenWAndRDown hevict_or_read_btn_down =>
          exact CMCM.rf.wObRGle.diffCluster.evictOrReadBetweenWAndRDown
            hw1_lin hw2_lin
            hw_ob_r_gle hdiff_cluster hevict_or_read_btn_down
            hknow_dir_access hno_intervening_writes hw1_in_b hw1_cluster hw1_not_down
