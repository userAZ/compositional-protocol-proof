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
  (_hw_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cache : e_w.struct = e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : Event.Between.noDirWrite cmp b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access :=
  no_dir_write_between_same_cache hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hsame_cache hknow_dir_access hno_intervening_writes

/-- Helper: When e_w's CLE is the immediate predecessor of e_r's CLE,
    e_r's CLE is ordered after e_w's CLE (rCleAfterWCle).
    Extracted directly from the immediate predecessor relationship. -/
lemma diffCache_rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
  hw_imm_pred_r_cle

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
  (hw_imm_pred_r_cle : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Extract rCleAfterWCle from CLE immediate predecessor
  have hr_cle_after := diffCache_rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle
  -- Main decision point: is e_w coherent?
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter with immPred (CLE immediate predecessor).
    -- Context: e_w is a coherent write at a cluster cache. The reader e_r is at a different
    -- cache. cdirEncapsDown_exists gives the dir downgrade event at e_w's cluster WITH its
    -- cache downgrade, bundled so the encapsulation is preserved (no Exists.choose mismatch).
    have hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW :=
      coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster.eAtCache
    have hlin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest cmp b init e :=
      fun e => hknow_dir_access cmp b init e
    -- Get dir event + cache downgrade from cdirEncapsDown_exists (both from same source)
    obtain ⟨e_cdir, he_cdir_in_b, he_cdir_isDir, he_cdir_proto, hcdir_lt_cle,
      ⟨e_cache_down, he_cdown_in_b, hcdir_encap_down, hcdown_is_down, hcdown_is_cache⟩,
      ⟨e_evict, he_evict_in_b, he_evict_isDir, hevict_lt_cle,
       hcdir_ob_evict, he_evict_proto, he_evict_translatedDir⟩⟩ :=
      cdirEncapsDown_exists hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster hw_not_down hlin
    -- Construct encapProxyAndDirAndCDown using the bundled witnesses.
    -- Both existsRClusterDirDown and existsRDownAtW use events from cdirEncapsDown_exists.
    -- cdirEncapsDown: the encapsulation between e_cdir and e_cache_down comes from the same call.
    sorry
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
