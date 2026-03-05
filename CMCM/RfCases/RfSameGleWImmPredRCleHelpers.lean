/-
  Helper lemmas specifically for the `rf.sameGle.wImmPredRCle` case
  (write's CLE is the immediate predecessor of read's CLE).

  These lemmas are used by `RfSameGleWImmPredRCle.lean` and handle:
  - Same cache: no intervening directory writes (`wimmpredrCle_no_dir_write_between_same_cache`)
  - Different cache: case selection (`wimmpredrCle_diff_cache_choose_case`)
    with the full diffCache proof chain:
    - noEvictBetween / evictBetween subcases
    - Coherent vs non-coherent write case split

  General helpers (same_gle_implies_same_protocol, diffCache_coherent_globalDowngrade,
  globalToCluster_extract_proxy_and_dir, diffCache_coherent_encapProxyAndDir,
  no_dir_write_between_same_cache) are in RfProofHelpers.lean for reuse across cases.
-/
import CMCM.RfProofHelpers

variable {n : ℕ}

/-- Wrapper for wImmPredRCle: delegates to the general `no_dir_write_between_same_cache`
    helper. The `hw_imm_pred_r_cle` parameter is accepted for signature compatibility
    but is not used. -/
lemma wimmpredrCle_no_dir_write_between_same_cache
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (_hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cache : e_w.struct = e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : Event.Between.noDirWrite cmp b init hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access :=
  no_dir_write_between_same_cache hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hsame_cache hknow_dir_access hno_intervening_writes

/-- Helper: When e_w's CLE is the immediate predecessor of e_r's CLE,
    e_r's CLE is ordered after e_w's CLE (rCleAfterWCle).
    Extracted directly from the immediate predecessor relationship. -/
lemma diffCache_rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
  hw_imm_pred_r_cle.isImmPred.bPred.isPred

/-- Helper for wImmPredRCle diffCache: Decides which WriteRead.wObRCle.diffCache.case to apply
    based on coherence of the write and its directory access structure.

    Case analysis:
    - Coherent write → wHasPermsAfter with immPred (CLE immediate predecessor)
    - Non-coherent write, case-split on dirAccessOfRequest:
      - encapDir (missing perms) → wNoPermsAfter
      - orderBeforeDir (has perms) or orderAfterDir (Vd writeback) → wCleAfter -/
lemma wimmpredrCle_diff_cache_choose_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Extract rCleAfterWCle from CLE immediate predecessor
  have hr_cle_after := diffCache_rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle
  -- Main decision point: is e_w coherent?
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter with immPred (CLE immediate predecessor)
    exact .wHasPermsAfter hw_coherent (.immPred hw_imm_pred_r_cle)
  · -- Non-coherent write: use rCleAfterWCle for the new constructors
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    -- dirAccessOfRequest determines whether write has missing perms
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      -- NC write with missing perms → wNoPermsAfter
      exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      -- NC write with perms (predecessor obtained dir access) → wCleAfter
      exact .wCleAfter hr_cle_after
    | orderAfterDir _ _ _ _ =>
      -- NC weak request on Vd (e.g. writeback) → wCleAfter
      exact .wCleAfter hr_cle_after
