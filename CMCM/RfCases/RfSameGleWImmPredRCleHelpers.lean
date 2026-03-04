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

/-- Helper: When e_w's CLE is the immediate predecessor of e_r's CLE and they are at different
    caches, the read's global linearization event triggers a downgrade at the previous owner,
    producing the wCleAfter condition wrapper. -/
lemma diffCache_wCleAfter_cond_wrapper
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  : WriteRead.wCleAfter.cond.wrapper cmp b init hw_c_and_g_lin hr_c_and_g_lin := by
  sorry

/-- Helper: No cache-level evict-SW between e_w and the cache-level downgrade e_r_down.

    After a coherent write, the cache holds exclusive (SW) state. The downgrade e_r_down
    is sent by e_r's GLE to e_w's cache to remove that state. An evict-SW at the same
    cache between e_w and e_r_down would mean the cache lost exclusive state before the
    downgrade arrived, but since the evict triggers directory activity (a CLE), and
    e_w_cle immediately precedes e_r_cle with no bottom events between them, such an
    evict's directory event would need to be between e_w_cle and e_r_cle — contradicting
    the CLE immediate predecessor property. -/
lemma diffCache_noEvictBetween_noEvict
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noEvict b e_w hencapPDC.existsRDownAtW.choose := by
  -- noEvict = ∀ e_inter ∈ b, e_inter.Between e_w e_r_down → ¬ e_inter.isEvictSW
  -- The Between structure requires coherentRead : e_r_down.isCoherent.
  -- Any evict at the same cache between e_w and e_r_down would need its CLE
  -- between e_w_cle and e_r_cle, violating the immediate predecessor property.
  sorry

/-- Helper: Every intervening write between e_w and e_r_down falls into one of the three
    excludeOtherWrites cases (same cache / diff cache same cluster / diff cluster).

    For each case, the key argument is: any such write's CLE (or directory-level
    downgrade event) would need to be between the CLE boundaries (e_w_cle and
    e_r_cdir_down). Since e_w_cle immediately precedes e_r_cle and e_r_cdir_down is
    part of e_r's downgrade chain, no write's CLE can fall between them without
    violating the immediate predecessor property. -/
lemma diffCache_noEvictBetween_noWrite
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noWrite b init e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := by
  -- noWrite = ∀ e_inter ∈ b, isClusterCache → isWrite → ¬down →
  --   excludeOtherWrites b init e_inter e_w e_r_down e_w_cle e_r_cdir_down
  -- For each e_inter, case-split on its location relative to e_w:
  --   1. Same cache → otherWSameCache
  --   2. Different cache, same cluster → otherWDiffCacheSameCluster
  --   3. Different cluster → otherWDiffCluster
  -- In each case, the interCleNotBetween field follows from the CLE immediate
  -- predecessor property: no bottom event at the same entry can be between e_w_cle
  -- and e_r_cle, and e_r_cdir_down is related to e_r_cle through the downgrade chain.
  sorry

/-- Helper: When a cache-level downgrade exists at e_w's cache (ordered after e_w), and
    e_w's CLE is the immediate predecessor of e_r's CLE, construct the noEvictBetween.cond.

    The three fields:
    - noWriteBtn: No intervening write between e_w and e_r_down at the cache level.
      Delegated to `diffCache_noEvictBetween_noWrite`.
    - noEvictBtn: No evict between e_w and e_r_down at the same cache.
      Delegated to `diffCache_noEvictBetween_noEvict`.
    - wObRDown: e_w is ordered before e_r_down.
      Extracted directly from the existential witness (hencapPDC.existsRDownAtW). -/
lemma diffCache_noEvictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : WriteRead.noEvictBetween.cond b init
      e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := {
    wObRDown := hencapPDC.existsRDownAtW.choose_spec.right.right.right
    noEvictBtn := diffCache_noEvictBetween_noEvict hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
    noWriteBtn := diffCache_noEvictBetween_noWrite hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
  }

/-- Helper: No directory-level write between e_w_cle and e_r_cdir_down.
    Since e_w_cle is the immediate predecessor of e_r_cle (CLE immediate predecessor),
    any intervening directory write from a same-cluster cache write would require that
    write's CLE to be between e_w_cle and e_r_cle, contradicting immediacy. Similarly,
    a different-cluster write's directory downgrade chain would need an event between
    e_w_cle and e_r_cle.

    The e_r_cdir_down boundary (cluster directory downgrade from e_r's chain) is part of
    the downgrade chain originating from e_r's GLE, structurally constraining what can
    appear between e_w_cle and e_r_cdir_down. -/
lemma diffCache_evictBetween_noWriteBtn
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Event.Between.noDirWrite cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := by
  -- noDirWrite is ¬ sameOrDiffCluster, so we assume sameOrDiffCluster and derive contradiction.
  -- The argument mirrors wimmpredrCle_no_dir_write_between_same_cache but with
  -- e_r_cdir_down as the second boundary instead of e_r_cle.
  sorry

/-- Helper: e_w_cle is ordered before e_r_cdir_down.
    The CLE immediate predecessor relationship places e_w_cle before e_r_cle.
    The downgrade chain from e_r's GLE produces e_r_cdir_down at e_w's cluster directory.
    The ordering e_w_cle < e_r_cdir_down follows from the protocol structure:
    e_w_cle → ... → e_r_cle → (global chain) → e_r_cdir_down, or
    e_w_cle < e_r_cdir_down directly via the downgrade chain's position relative
    to the CLE immediate predecessor boundary. -/
lemma diffCache_evictBetween_wObRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
      hencapPD.existsRClusterDirDown.choose := by
  sorry

/-- Helper: When no cache-level downgrade exists at e_w's cache (¬hcdown), and
    e_w's CLE is the immediate predecessor of e_r's CLE, construct the evictBetween.cond.

    The three fields:
    - noWriteBtn: No intervening directory write between e_w's CLE and e_r's cluster dir down.
      Delegated to `diffCache_evictBetween_noWriteBtn`.
    - evictBtn: Trivially satisfiable — `dirEvict` is `∃ e ∈ b, OrderedBetween → isDirEvict`.
      Picking e = e_w_cle, the antecedent `e_w_cle.OrderedBetween n e_w_cle e_r_cdir_down`
      is false (requires e_w_cle strictly after itself), so the implication holds vacuously.
    - wObRDown: Delegated to `diffCache_evictBetween_wObRDown`. -/
lemma diffCache_evictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_cdown : ¬ ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down)
  : WriteRead.evictBetween.cond cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := {
    noWriteBtn := diffCache_evictBetween_noWriteBtn hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent
      hencapPD hknow_dir_access
    evictBtn := ⟨hw_c_and_g_lin.hreq's_dir_access.choose,
      hw_c_and_g_lin.hreq's_dir_access.choose_spec.left,
      fun h => (Event.contradiction_of_reflexive_ordered_before n h.pred).elim⟩
    wObRDown := diffCache_evictBetween_wObRDown
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hencapPD
  }

/-- Coherent write at a different cache with CLE immediate predecessor relationship.
    Builds the wHasPermsAfter.case by constructing the downgrade chain from the read's GLE
    down to e_w's cache, then deciding between noEvictBetween and evictBetween.

    The downgrade chain goes:
    - e_r's GLE → global downgrade e_r_gdown (from diffCache_coherent_encapProxyAndDir)
    - e_r_gdown → cluster proxy e_r_proxy at e_w's protocol (via GlobalToCluster shim)
    - e_r_proxy → cluster directory downgrade e_r_cdir_down at e_w's protocol
    - e_r_cdir_down → cache downgrade e_r_down at e_w's cache struct (noEvict case only)

    The noEvict vs evict decision:
    - noEvictBetween: downgrade chain extends to e_w's cache, no evicts between e_w and e_r_down
    - evictBetween: cache was evicted, chain only reaches cluster directory level -/
lemma diffCache_coherent_wHasPermsAfter_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
      hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Step 1: Construct the global + cluster level downgrade chain (common to both cases)
  have hencapPD := diffCache_coherent_encapProxyAndDir
    hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
  -- Step 2: Does the cluster directory downgrade propagate to a cache-level downgrade at e_w?
  -- If e_w's cache still holds the line (no evict) → chain extends to cache → noEvictBetween
  -- If e_w's cache was evicted → chain only reaches cluster directory → evictBetween
  by_cases hcdown : ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  · -- noEvictBetween: downgrade reaches e_w's cache directly
    let hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin :=
      { encapProxyAndDir := hencapPD, existsRDownAtW := hcdown }
    exact .noEvictBetween {
      gdownEncapProxyAndDirAndCDown := hencapPDC
      noEvictBetween := diffCache_noEvictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
    }
  · -- evictBetween: cache was evicted, downgrade only reaches cluster directory level
    exact .evictBetween {
      encapProxyAndDir := hencapPD
      evictBetween := diffCache_evictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent
        hencapPD hknow_dir_access hcdown
    }

/-- Helper for wImmPredRCle diffCache: Decides which WriteRead.wObRCle.diffCache.case to apply
    based on coherence of the write and its directory access structure.

    Case analysis:
    - Coherent write → wHasPermsAfter (write retains/obtains permissions)
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
  -- Main decision point: is e_w coherent?
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter
    exact WriteRead.wObRCle.diffCache.case.wHasPermsAfter hw_coherent
      (diffCache_coherent_wHasPermsAfter_case hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hknow_dir_access
        hw_in_b hw_cluster)
  · -- Non-coherent write: construct the shared wCleAfter.cond.wrapper once,
    -- then case-split on dirAccessOfRequest to select the constructor.
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    have hwrapper := diffCache_wCleAfter_cond_wrapper
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache
    -- dirAccessOfRequest determines whether write has missing perms
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      -- NC write with missing perms → wNoPermsAfter
      exact WriteRead.wObRCle.diffCache.case.wNoPermsAfter hreq_missing_perms hw_nc hwrapper
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      -- NC write with perms (predecessor obtained dir access) → wCleAfter
      exact WriteRead.wObRCle.diffCache.case.wCleAfter hwrapper
    | orderAfterDir _ _ _ _ =>
      -- NC weak request on Vd (e.g. writeback) → wCleAfter
      exact WriteRead.wObRCle.diffCache.case.wCleAfter hwrapper
