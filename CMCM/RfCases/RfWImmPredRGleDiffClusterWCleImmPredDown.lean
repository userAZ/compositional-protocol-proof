import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleWImmPredRCleHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and e_w's CLE is the immediate predecessor of the
    directory-level read downgrade at e_w's protocol.

    Uses the `diffCluster` constructor of `sameOrDifferentCluster.cases` with
    `wHasPermsAfter.notImmPred.evictBetween` for the coherent case. -/
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
  -- GLE_w is ordered before GLE_r (from immediate predecessor)
  apply Behaviour.readsFrom.cases.wObRGle
    (hw_imm_pred_r_gle.isImmPred.bPred.isPred)
  -- Different cluster → different cache
  have hdiff_cache : e_w.struct ≠ e_r.struct :=
    fun h => hdiff_cluster (sameStructure_implies_sameProtocol h)
  refine .diffCluster (r_is_read := hr_is_read) hdiff_cluster hdiff_cache ?_ ?_
  · -- encapGDown
    constructor
    intro hstate_sw
    have ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, h_wrapper⟩ :=
      diffCache_coherent_globalDowngrade hr_c_and_g_lin
    have h_dpow := h_wrapper.downgradePrevOwner
    have h_at_prev := h_dpow.atPrevOwner
    have h_fwd := h_dpow.fwdFromRequester
    have h_is_cache := h_dpow.downAtCache
    -- hstate_sw says directoryStateMadeOn = .SW with owner e_w.gCacheOfCEvent
    -- atPrevOwner uses the same (b.stateBefore ...).directory = directoryStateMadeOn
    unfold Behaviour.directoryStateMadeOn at hstate_sw
    rw [hstate_sw] at h_at_prev
    -- h_at_prev : e_r_gdown.downgradeAtPrevOwner n (.SW ⟨SW, _⟩ e_w.gCacheOfCEvent)
    -- Case-split: e_r_gdown must be a cache event (from downAtCache)
    cases e_r_gdown with
    | directoryEvent de =>
      exact absurd h_is_cache (by simp [Event.isCacheEvent])
    | cacheEvent ce =>
      refine ⟨.cacheEvent ce, he_r_gdown_in_b, ?_, ?_⟩
      · -- ce.cid = e_w.gCacheOfCEvent (from downgradeAtPrevOwner on .SW state)
        simp only [Event.downgradeAtPrevOwner] at h_at_prev
        simp only [Event.cid]
        exact h_at_prev
      · -- ce.down (from downgradeCorrespondingToRequest → downgradeOfReq.isDown)
        exact downgradeCorrespondingToRequest_isDown h_fwd
  · -- diffCache.case
    -- Note 1: by_cases on whether e_w leaves SW state (permissions after).
    -- This separates wHasPermsAfter (leaves SW) from wNoPermsAfter/wCleAfter (doesn't).
    by_cases hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW
    · -- e_w leaves SW state → use wHasPermsAfter with evictBetween
      -- The evictBetween path works because wCleImmPredRDownReadOrEvict gives that all
      -- intermediate dir events are reads or evicts, avoiding cache-level noWrite/noEvict goals.
      refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.evictBetween
        ⟨hw_cle_imm_pred_r_down.rDown.encapDir, ?_, ?_, hw_cle_imm_pred_r_down.wObRDown⟩))
      · -- noDirWrite: Event.Between.noDirWrite
        -- From wCleImmPredRDownReadOrEvict: all intermediate dir events between e_w_cle and
        -- e_r_cdir_down are isDirReadOrEvict. An intervening dir write contradicts this.
        intro hinter
        cases hinter with
        | sameCluster e_w_inter h =>
          have he_in_b := (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose_spec.left
          have h_cle_prot : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.protocol
              = hw_c_and_g_lin.hreq's_dir_access.choose.protocol :=
            (write_cle_protocol_eq_write_protocol (hknow_dir_access cmp b init e_w_inter)).trans h.sameProtocol
          have h_inter_is_dir := (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose_spec.right.isDirEvent
          have h_w_is_dir := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
          have h_same_struct : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.sameStructure n
              hw_c_and_g_lin.hreq's_dir_access.choose := by
            unfold Event.sameStructure
            match h_e1 : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose,
                  h_e2 : hw_c_and_g_lin.hreq's_dir_access.choose with
            | .cacheEvent _, _ => simp [Event.isDirectoryEvent, h_e1] at h_inter_is_dir
            | _, .cacheEvent _ => simp [Event.isDirectoryEvent, h_e2] at h_w_is_dir
            | .directoryEvent de₁, .directoryEvent de₂ =>
              simp [Event.protocol, h_e1, h_e2] at h_cle_prot
              simp [Event.struct, h_cle_prot]
          have h_is_read := hw_cle_imm_pred_r_down.wCleImmPredRDownReadOrEvict _ he_in_b
            ⟨h_cle_prot, h_same_struct, h.cleBetween⟩
          unfold Event.isDirReadOrEvict at h_is_read
          have h_write := h.cleDirWrite
          match h_ev : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose with
          | .cacheEvent _ =>
            simp [Event.isDirWrite, h_ev] at h_write
          | .directoryEvent de =>
            simp [Event.isDirWrite, Request.isWrite, h_ev] at h_write
            simp [Event.isDirRead, Request.isRead, h_ev] at h_is_read
            rw [h_write] at h_is_read
            exact absurd h_is_read (by decide)
        | diffCluster e_w_inter h =>
          obtain ⟨e_cdir_down, he_in_b, h_is_dir, h_prot_eq, h_is_write, _, _, h_between⟩ :=
            h.existsClusterDirDown
          have h_w_is_dir := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
          have h_same_struct : e_cdir_down.sameStructure n hw_c_and_g_lin.hreq's_dir_access.choose := by
            unfold Event.sameStructure
            match h_e1 : e_cdir_down, h_e2 : hw_c_and_g_lin.hreq's_dir_access.choose with
            | .cacheEvent _, _ => simp [Event.isDirectoryEvent, h_e1] at h_is_dir
            | _, .cacheEvent _ => simp [Event.isDirectoryEvent, h_e2] at h_w_is_dir
            | .directoryEvent de₁, .directoryEvent de₂ =>
              simp [Event.protocol, h_e1, h_e2] at h_prot_eq
              simp [Event.struct, h_prot_eq]
          have h_is_read := hw_cle_imm_pred_r_down.wCleImmPredRDownReadOrEvict e_cdir_down he_in_b
            ⟨h_prot_eq, h_same_struct, h_between⟩
          unfold Event.isDirReadOrEvict at h_is_read
          match h_ev : e_cdir_down with
          | .cacheEvent _ => simp [Event.isDirectoryEvent, h_ev] at h_is_dir
          | .directoryEvent de =>
            simp [Event.isDirRead, Request.isRead, h_ev] at h_is_read
            simp [Event.isDirWrite, Request.isWrite, h_ev] at h_is_write
            rw [h_is_write] at h_is_read
            exact absurd h_is_read (by decide)
      · -- evictBtn: Event.Between.dirEvict b e_w_cle e_r_cdir_down
        -- All same-structure events between e_w_cle and e_r_cdir_down are dir evict or dir read.
        intro e he_in_b h_same_struct h_ordered_between
        cases e with
        | cacheEvent ce =>
          exfalso
          have h_w_cle_dir := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
          match h_cle_ev : hw_c_and_g_lin.hreq's_dir_access.choose with
          | .directoryEvent _ =>
            simp [Event.sameStructure, Event.struct, h_cle_ev] at h_same_struct
          | .cacheEvent _ =>
            simp [Event.isDirectoryEvent, h_cle_ev] at h_w_cle_dir
        | directoryEvent de =>
          by_cases h_down : (de.down : Prop)
          · exact Or.inl h_down
          · right
            show de.req.val.isRead
            unfold Request.isRead
            cases h_rw : de.req.val.rw with
            | r => rfl
            | w =>
              exfalso
              have h_same_prot : (Event.directoryEvent de).sameProtocol n
                  hw_c_and_g_lin.hreq's_dir_access.choose :=
                sameStructure_implies_sameProtocol h_same_struct
              have h_is_read := hw_cle_imm_pred_r_down.wCleImmPredRDownReadOrEvict (.directoryEvent de) he_in_b
                ⟨h_same_prot, h_same_struct, h_ordered_between⟩
              simp [Event.isDirReadOrEvict, Event.isDirRead, Request.isRead, h_rw] at h_is_read
    · -- e_w does NOT leave SW state → use wNoPermsAfter or wCleAfter
      -- These don't require noWriteBtn/noEvictBtn, just rCleAfterWCle.
      have hr_cle_after : WriteRead.wObRCle.diffCache.rCleOrDownAtWAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
        .diffCluster hdiff_cluster hw_cle_imm_pred_r_down.rDown.encapDir
      have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
      cases hw_dir_access with
      | encapDir hreq_missing_perms _ =>
        have hw_not_coherent : ¬ e_w.isCoherent := fun h_coh =>
          hw_leaves_SW (coherent_write_leaves_at_least_SW hw_is_write h_coh hw_not_down hw_cluster_cache.eAtCache)
        have hw_nc := isNonCoherent_of_not_isCoherent_write hw_is_write hw_not_coherent
        exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
      | orderBeforeDir _ _ _ _ _ _ _ _ =>
        exact .wCleAfter hr_cle_after
      | orderAfterDir _ _ _ _ =>
        exact .wCleAfter hr_cle_after
