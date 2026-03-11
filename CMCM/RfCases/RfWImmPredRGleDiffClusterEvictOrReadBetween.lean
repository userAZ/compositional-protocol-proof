import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetweenHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and all intermediate directory events between e_w's CLE
    and the directory-level read downgrade are reads or evicts.

    Uses the `diffCluster` constructor of `sameOrDifferentCluster.cases` with
    `wHasPermsAfter.notImmPred.evictBetween` for the coherent case. -/
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
  -- GLE_w is ordered before GLE_r (from immediate predecessor)
  apply Behaviour.readsFrom.cases.wObRGle
    (hw_imm_pred_r_gle.isImmPred.bPred.isPred)
  -- Different cluster → different cache
  have hdiff_cache : e_w.struct ≠ e_r.struct :=
    fun h => hdiff_cluster (sameStructure_implies_sameProtocol h)
  refine .diffCluster (r_is_read := hr_is_read) hdiff_cluster hdiff_cache ?_ ?_
  · -- encapGDown: same proof as wCleImmPredDown case
    constructor
    intro hstate_sw
    have ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, h_wrapper⟩ :=
      diffCache_coherent_globalDowngrade hr_c_and_g_lin
    have h_dpow := h_wrapper.downgradePrevOwner
    have h_at_prev := h_dpow.atPrevOwner
    have h_fwd := h_dpow.fwdFromRequester
    have h_is_cache := h_dpow.downAtCache
    unfold Behaviour.directoryStateMadeOn at hstate_sw
    rw [hstate_sw] at h_at_prev
    cases e_r_gdown with
    | directoryEvent de =>
      exact absurd h_is_cache (by simp [Event.isCacheEvent])
    | cacheEvent ce =>
      refine ⟨.cacheEvent ce, he_r_gdown_in_b, ?_, ?_⟩
      · simp only [Event.downgradeAtPrevOwner] at h_at_prev
        simp only [Event.cid]
        exact h_at_prev
      · exact downgradeCorrespondingToRequest_isDown h_fwd
  · -- diffCache.case
    -- Note 1: by_cases on whether e_w leaves SW state (permissions after).
    by_cases hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW
    · -- e_w leaves SW state → use wHasPermsAfter
      -- Note 2: by_cases on whether e_w's CLE is immPred of e_r's cluster downgrade.
      -- In the evictOrReadBetween case, we don't know this a priori, so we do an actual by_cases.
      by_cases h_cle_imm : b.ImmediateBottomPredecessor n
        hw_c_and_g_lin.hreq's_dir_access.choose
        hw_cle_imm_pred_down.rDown.encapDir.existsRClusterDirDown.choose
      · -- e_w_cle IS immPred of e_r_cdir_down → use noEvictBetween (nothing between them)
        refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.noEvictBetween
          ⟨hw_cle_imm_pred_down.rDown, ?_, ?_,
           hw_cle_imm_pred_down.rDown.existsRDownAtW.choose_spec.right.right.right⟩))
        · -- noWriteBtn: Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cdir_down
          -- Strategy: Use otherWDiffCluster for ALL e_inter.
          -- For same-protocol e_inter: dirWriteDowngradeFromDiffCluster.diffProtocol fails → ∃ vacuously false.
          -- For diff-protocol e_inter: use h_cle_imm.isImmPred.noIntermediate to show
          --   any bottom dir event at e_w's cluster with sameEntry to e_r_cdir_down
          --   cannot be OrderedBetween e_w_cle and e_r_cdir_down.
          --   Need: directory_event_is_bottom + sameEntry (sameStruct from sameProtocol + sameAddr).
          -- Requires: sameAddr lemma connecting dirWriteDowngradeFromDiffCluster to e_r_cdir_down.
          sorry
        · -- noEvictBtn: Event.Between.noEvict b e_w e_r_down
          -- Strategy: Event.Between requires coherentRead (e_r_down.isCoherent) and
          --   sameCache (e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r_down).
          -- If e_r_down is not coherent, Between is vacuously False → noEvict trivially holds.
          -- Otherwise: use h_cle_imm.isImmPred.noIntermediate + the fact that
          --   an evict's CLE is a bottom dir event at the same entry → cannot be between.
          -- See RfSameGleSameCle.lean for the 9-case dirAccessOfRequest analysis pattern.
          sorry
      · -- e_w_cle is NOT immPred → use evictBetween (intermediate events exist)
        refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.evictBetween
          ⟨hw_cle_imm_pred_down.rDown.encapDir, ?_, ?_, hw_cle_imm_pred_down.wObRDown⟩))
        · -- noDirWrite: Event.Between.noDirWrite
          -- From wCleImmPredRDown: all intermediate dir events between e_w_cle and e_r_cdir_down
          -- are isDirRead. An intervening dir write would be isDirWrite, contradicting isDirRead.
          intro hinter
          cases hinter with
          | sameCluster e_w_inter h =>
            -- h.cleDirWrite says the CLE of e_w_inter is isDirWrite
            -- wCleImmPredRDown will say it must be isDirRead → contradiction
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
            have h_is_read := hw_cle_imm_pred_down.wCleImmPredRDown _ he_in_b
              ⟨h_cle_prot, h_same_struct, h.cleBetween⟩
            -- isDirReadOrEvict = isDirRead, contradicts isDirWrite
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
            -- existsClusterDirDown gives a dir event that is isDirWrite between the boundaries
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
            have h_is_read := hw_cle_imm_pred_down.wCleImmPredRDown e_cdir_down he_in_b
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
          -- Strategy: show e can't be a non-down dir write; then either de.down (isDirEvict)
          -- or de.req.val.rw = .r (isDirRead).
          intro e he_in_b h_same_struct h_ordered_between
          cases e with
          | cacheEvent ce =>
            -- Cache events can't have sameStructure with a directory event
            exfalso
            have h_w_cle_dir := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
            match h_cle_ev : hw_c_and_g_lin.hreq's_dir_access.choose with
            | .directoryEvent _ =>
              simp [Event.sameStructure, Event.struct, h_cle_ev] at h_same_struct
            | .cacheEvent _ =>
              simp [Event.isDirectoryEvent, h_cle_ev] at h_w_cle_dir
          | directoryEvent de =>
            -- isDirEvict = de.down, isDirRead = de.req.val.rw = .r
            -- Case split: is de down (isDirEvict)?
            by_cases h_down : (de.down : Prop)
            · exact Or.inl h_down
            · -- ¬ de.down → show isDirRead (de.req.val.rw = .r)
              right
              show de.req.val.isRead
              unfold Request.isRead
              -- de.req.val.rw is either .r or .w
              cases h_rw : de.req.val.rw with
              | r => rfl
              | w =>
                -- de is a non-down dir write between e_w_cle and e_r_cdir_down
                -- wCleImmPredRDown says intermediate dir events (with right protocol/structure) are isDirRead
                -- isDirRead requires rw = .r, contradicting rw = .w
                exfalso
                -- Derive sameProtocol from sameStructure (both are directory events)
                have h_same_prot : (Event.directoryEvent de).sameProtocol n
                    hw_c_and_g_lin.hreq's_dir_access.choose :=
                  sameStructure_implies_sameProtocol h_same_struct
                -- Construct IntermediateDirEvictOrRead from OrderedBetween
                have h_is_read := hw_cle_imm_pred_down.wCleImmPredRDown (.directoryEvent de) he_in_b
                  ⟨h_same_prot, h_same_struct, h_ordered_between⟩
                simp [Event.isDirReadOrEvict, Event.isDirRead, Request.isRead, h_rw] at h_is_read
    · -- e_w does NOT leave SW state → use wNoPermsAfter or wCleAfter
      have hr_cle_after : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin := by
        sorry -- TODO: derive from GLE ordering chain via gle_ordered_implies_cle_ordered
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
