/-
  Helper lemmas specifically for the `rf.sameGle.evictOrReadBetweenWAndRCleSameCluster` case
  (same GLE, same cluster, with evicts/reads between write's and read's CLEs).

  These lemmas handle the diffCache subcase for the evictOrReadBetween CLE relationship.
  The sameCache subcase uses the general `no_dir_write_between_same_cache` from RfProofHelpers.

  General helpers (same_gle_implies_same_protocol, diffCache_coherent_globalDowngrade,
  globalToCluster_extract_proxy_and_dir, diffCache_coherent_encapProxyAndDir,
  no_dir_write_between_same_cache) are in RfProofHelpers.lean for reuse across cases.
-/
import CMCM.RfProofHelpers

variable {n : ℕ}

/-- Helper: When e_w's CLE has evicts/reads between it and e_r's CLE,
    e_r's CLE is ordered after e_w's CLE (rCleAfterWCle).
    Extracted directly from the evictOrReadBetween.wObR field. -/
lemma evictOrReadBtn_diffCache_rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
  hevict_or_read_between.wObR

/-- diffCache case decision for evictOrReadBetween: coherent vs non-coherent write.
    - Coherent write → wHasPermsAfter
    - Non-coherent write → case split on dirAccessOfRequest:
      - encapDir → wNoPermsAfter
      - orderBeforeDir or orderAfterDir → wCleAfter -/
lemma evictOrReadBtn_diff_cache_choose_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Extract rCleAfterWCle from evictOrReadBetween.wObR
  have hr_cle_after := evictOrReadBtn_diffCache_rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write: first check if e_w's CLE is the immediate predecessor of e_r's CLE
    have hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW :=
      coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster.eAtCache
    by_cases h_imm : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin
    · -- immPred: e_w_cle is immediate predecessor of e_r_cle (same structure as wImmPredRCle)
      have hencapPD := diffCache_coherent_encapProxyAndDir hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
      by_cases hcdown : ∃ e_r_down ∈ b,
        e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
      · -- Cache-level downgrade exists → use immPred directly (skips noEvict/noWrite)
        have hencapPDC : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin :=
          { encapDir := hencapPD, existsRDownAtW := hcdown }
        exact .wHasPermsAfter hw_leaves_SW (.immPred h_imm hencapPDC)
      · -- No cache-level downgrade → fall back to wCleAfter
        exact .wCleAfter hr_cle_after
    · -- notImmPred: fall back to wCleAfter (no need for noEvict/noWrite/wObRDown)
      exact .wCleAfter hr_cle_after
  · -- Non-coherent write: use rCleAfterWCle for the new constructors
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      exact .wCleAfter hr_cle_after
    | orderAfterDir _ _ _ _ =>
      exact .wCleAfter hr_cle_after
