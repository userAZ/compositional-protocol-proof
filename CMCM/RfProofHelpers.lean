import CMCM.RfProofDefs

variable {n : ℕ}

/-- Helper: If two events both encapsulate the same CLE and are ordered,
    we get a timing contradiction. This pattern appears in Case 1.1 and similar dual-encap cases. -/
lemma dual_encap_ordered_contradiction
  (hw_encap : (e_w : Event n).Encapsulates n e_cle)
  (hr_encap : e_r.Encapsulates n e_cle)
  (hw_ob_r : e_w.OrderedBefore n e_r)
  : False := by
  simp only [Event.Encapsulates] at hw_encap hr_encap
  simp only [Event.OrderedBefore] at hw_ob_r
  have hcle_wf := e_cle.oWellFormed
  -- Combining: cle.oEnd < e_w.oEnd < e_r.oStart < cle.oStart
  -- This contradicts cle.oStart < cle.oEnd
  have : e_cle.oEnd < e_cle.oStart := by
    calc e_cle.oEnd < e_w.oEnd := hw_encap.2
      _ < e_r.oStart := hw_ob_r
      _ < e_cle.oStart := hr_encap.1
  exact Nat.lt_asymm this hcle_wf

/-- Helper lemma for Case 2a: Different cache, same protocol/cluster -/
lemma noInterveningWrites_diffCache_sameProtocol_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w e_r e_inter : Event n}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite_cluster : e_inter.isClusterCache)
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  (hsame_cache : ¬e_inter.sameStructure n e_w)
  (hsame_protocol : e_inter.sameProtocol n e_w)
  : Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose) := by

  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
  let e_inter_cle := hinter_lin.hreq's_dir_access.choose

  apply Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites.otherWDiffCacheSameCluster
  constructor
  · -- Prove: sameProtocol
    have hw_r_same_struct : e_w.sameStructure n e_r := by
      unfold Event.sameStructure
      exact _hsame_struct
    have hw_eq_r_protocol : e_w.protocol = e_r.protocol := sameStructure_implies_sameProtocol hw_r_same_struct
    have hsame_r_protocol : e_inter.sameProtocol n e_r := by
      unfold Event.sameProtocol at *
      calc e_inter.protocol
        _ = e_w.protocol := hsame_protocol
        _ = e_r.protocol := hw_eq_r_protocol
    exact ⟨hsame_protocol, hsame_r_protocol⟩
  · -- Prove: diffCache
    have hdiff_r : e_inter.diffStructure n e_r := by
      unfold Event.diffStructure Event.sameStructure at *
      simp[_hsame_struct] at *
      exact hsame_cache
    exact ⟨hsame_cache, hdiff_r⟩
  · -- Prove: interCleNotBetween
    -- Strategy: Use hcontra.notBetweenCles to contradict any attempt to show
    -- that some directory downgrade IS between e_w_cle and e_r_cle
    -- We provide e_inter as the witness, and show that if it encapsulates a downgrade,
    -- that downgrade cannot be between the CLEs due to notBetweenCles

    -- hdowngrade : Event.dirWriteDowngradeAtSameCluster e_inter e_inter e_w
    -- This means hdowngrade.interEncapDown : e_inter.Encapsulates n (some directory)

    -- Case on dirAccessOfRequest to relate e_inter to e_inter_cle
    have hdir_access := hinter_lin.hreq's_dir_access.choose_spec.right
    cases hdir_access with
    | encapDir hreq_missing_perms hencap_dir =>
      have hw_r_same_struct : e_w.sameStructure n e_r := by
        unfold Event.sameStructure; exact _hsame_struct
      have hw_eq_r_protocol : e_w.protocol = e_r.protocol :=
        sameStructure_implies_sameProtocol hw_r_same_struct
      have hw_cle_protocol : e_w_cle.protocol = e_w.protocol :=
        write_cle_protocol_eq_write_protocol hw_c_and_g_lin
      have hr_cle_protocol : e_r_cle.protocol = e_r.protocol :=
        read_cle_protocol_eq_read_protocol hr_c_and_g_lin
      have hsame_protocol_cles : e_inter_cle.protocol = e_w_cle.protocol ∧ e_inter_cle.protocol = e_r_cle.protocol := by
        constructor
        · calc e_inter_cle.protocol
            _ = e_inter.protocol := hencap_dir.sameProtocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_w_cle.protocol := hw_cle_protocol.symm
        · calc e_inter_cle.protocol
            _ = e_inter.protocol := hencap_dir.sameProtocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_r.protocol := hw_eq_r_protocol
            _ = e_r_cle.protocol := hr_cle_protocol.symm
      -- Show that e_inter_cle is a directory write
      have hinter_cle_is_dir_write : Event.isDirWrite n e_inter_cle := by
        -- e_inter is a write (hwrite : e_inter.isWrite)
        -- By dirAccessOfRequest in encapDir case, the directory event corresponds to the cache request
        -- The directory request matches the cache request type (write)
        have hdir_matches_req := hencap_dir.dirCorresponds
        have hdir_req_matches := hencap_dir.dirCorresponds.dirReq
        -- e_inter_cle is a directory event
        have hinter_cle_is_dir := hencap_dir.isDir
        -- Extract the directory event to access its request field
        match hinter_cle_ev : e_inter_cle with
        | .directoryEvent de_inter_cle =>
          unfold Event.isDirWrite
          simp
          -- The directory event's request is determined by reqToDirOfRequestEvent
          -- For writes, in most cases this preserves the write operation
          -- We need to show de_inter_cle.req.val.rw = .w
          -- Given: e_inter.isWrite means e_inter.req.val.rw = .w (for cache events)
          -- [AZ]: Show e_inter's CLE is a directory write event.
          unfold Event.isWrite at hwrite
          match hinter_ev : e_inter with
          | .directoryEvent _ =>
            -- e_inter is not a directory event (it's a cluster cache)
            have : e_inter.isCacheEvent := by
              simpa [hinter_ev] using hwrite_cluster.eAtCache
            simp [Event.isCacheEvent, hinter_ev] at this
          | .cacheEvent ce_inter =>
            -- Now hwrite : ce_inter.req.val.isWrite, i.e., ce_inter.req.val.rw = .w
            have hwrite' : ce_inter.req.val.isWrite := by
              simpa [Event.isWrite, hinter_ev] using hwrite
            -- From dirEventOfReqEvent, de_inter_cle.eReq = ce_inter

            -- unfold Behaviour.requestDirectoryEvent at hdir_matches_req
            -- unfold Event.dirEventOfReqEvent at hdir_matches_req
            -- simp [hinter_cle_ev, hinter_ev] at hdir_matches_req

            -- From requestDirectoryEvent, de_inter_cle.req = ...
            -- The directory request is derived from the cache request
            -- For a write, unless it's a NC write on I state (which becomes a read),
            -- the write is preserved
            -- In this context with NoInterveningWrites, we're dealing with intervening writes
            -- between two operations, so the directory event should also be a write
            sorry
        | .cacheEvent _ =>
          -- Contradiction: e_inter_cle cannot be both a cache event and a directory event
          have hinter_cle_is_dir' : e_inter_cle.isDirectoryEvent := hinter_cle_is_dir
          simp [Event.isDirectoryEvent, hinter_cle_ev] at hinter_cle_is_dir'
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      exists e_inter_cle
      constructor
      · exact hinter_lin.hreq's_dir_access.choose_spec.left
      intro hdowngrade
      exact hnot_between
    | orderBeforeDir hreq_has_perms hexists_pred_getting_perms hpred_accesses_dir hinter_leaves_state_at_least hpred_same_protocol =>
      have hw_r_same_struct : e_w.sameStructure n e_r := by
        unfold Event.sameStructure; exact _hsame_struct
      have hw_eq_r_protocol : e_w.protocol = e_r.protocol :=
        sameStructure_implies_sameProtocol hw_r_same_struct
      have hw_cle_protocol : e_w_cle.protocol = e_w.protocol :=
        write_cle_protocol_eq_write_protocol hw_c_and_g_lin
      have hr_cle_protocol : e_r_cle.protocol = e_r.protocol :=
        read_cle_protocol_eq_read_protocol hr_c_and_g_lin
      have hpred_protocol : e_inter.protocol = hexists_pred_getting_perms.choose.protocol := by
        unfold Event.sameProtocol at hpred_same_protocol; exact hpred_same_protocol.symm
      have hsame_pred_cle_protocol : hexists_pred_getting_perms.choose.protocol = e_inter_cle.protocol :=
        hpred_accesses_dir.sameProtocol
      have hsame_protocol_cles : e_inter_cle.protocol = e_w_cle.protocol ∧ e_inter_cle.protocol = e_r_cle.protocol := by
        constructor
        · calc e_inter_cle.protocol
            _ = hexists_pred_getting_perms.choose.protocol := hsame_pred_cle_protocol.symm
            _ = e_inter.protocol := hpred_protocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_w_cle.protocol := hw_cle_protocol.symm
        · calc e_inter_cle.protocol
            _ = hexists_pred_getting_perms.choose.protocol := hsame_pred_cle_protocol.symm
            _ = e_inter.protocol := hpred_protocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_r.protocol := hw_eq_r_protocol
            _ = e_r_cle.protocol := hr_cle_protocol.symm
      -- Show that e_inter_cle is a directory write (same proof structure as encapDir case)
      have hinter_cle_is_dir_write : Event.isDirWrite n e_inter_cle := sorry
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      exists e_inter_cle
      constructor
      · exact hinter_lin.hreq's_dir_access.choose_spec.left
      intro hdowngrade
      exact hnot_between

    | orderAfterDir hweak_read_on_vd hsucc_encap_dir hsucc_same_protocol =>
      have hw_r_same_struct : e_w.sameStructure n e_r := by
        unfold Event.sameStructure; exact _hsame_struct
      have hw_eq_r_protocol : e_w.protocol = e_r.protocol :=
        sameStructure_implies_sameProtocol hw_r_same_struct
      have hw_cle_protocol : e_w_cle.protocol = e_w.protocol :=
        write_cle_protocol_eq_write_protocol hw_c_and_g_lin
      have hr_cle_protocol : e_r_cle.protocol = e_r.protocol :=
        read_cle_protocol_eq_read_protocol hr_c_and_g_lin
      have hsame_succ_cle_protocol : hsucc_encap_dir.choose.protocol = e_inter_cle.protocol :=
        hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.sameProtocol
      have hsucc_protocol : e_inter.protocol = hsucc_encap_dir.choose.protocol := by
        unfold Event.sameProtocol at hsucc_same_protocol; exact hsucc_same_protocol.symm
      have hsame_protocol_cles : e_inter_cle.protocol = e_w_cle.protocol ∧ e_inter_cle.protocol = e_r_cle.protocol := by
        constructor
        · calc e_inter_cle.protocol
            _ = hsucc_encap_dir.choose.protocol := hsame_succ_cle_protocol.symm
            _ = e_inter.protocol := hsucc_protocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_w_cle.protocol := hw_cle_protocol.symm
        · calc e_inter_cle.protocol
            _ = hsucc_encap_dir.choose.protocol := hsame_succ_cle_protocol.symm
            _ = e_inter.protocol := hsucc_protocol.symm
            _ = e_w.protocol := hsame_protocol
            _ = e_r.protocol := hw_eq_r_protocol
            _ = e_r_cle.protocol := hr_cle_protocol.symm
      -- Show that e_inter_cle is a directory write (same proof structure as encapDir case)
      have hinter_cle_is_dir_write : Event.isDirWrite n e_inter_cle := sorry
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      exists e_inter_cle
      constructor
      · exact hinter_lin.hreq's_dir_access.choose_spec.left
      intro hdowngrade
      exact hnot_between
/-- Helper lemma for Case 2b: Different protocol/cluster -/
lemma noInterveningWrites_diffCache_diffProtocol_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w e_r e_inter : Event n}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
--   {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  (hsame_cache : ¬e_inter.sameStructure n e_w)
  (hsame_protocol : ¬e_inter.sameProtocol n e_w)
  : Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose) := by

  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
  let e_inter_cle := hinter_lin.hreq's_dir_access.choose

  -- Compute protocol differences upfront for use in both branches
  have hdiff_w_protocol : e_inter.diffProtocol n e_w := by
    unfold Event.diffProtocol Event.sameProtocol at *
    exact hsame_protocol
  have hw_r_same_struct : e_w.sameStructure n e_r := by
    unfold Event.sameStructure
    exact _hsame_struct
  have hw_eq_r_protocol : e_w.protocol = e_r.protocol := sameStructure_implies_sameProtocol hw_r_same_struct
  have hdiff_r_protocol : e_inter.diffProtocol n e_r := by
    unfold Event.diffProtocol at *
    calc e_inter.protocol
      _ ≠ e_w.protocol := hdiff_w_protocol
      _ = e_r.protocol := hw_eq_r_protocol

  -- Apply the constructor with the negation proof
  apply Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites.otherWDiffCluster
  constructor
  intro ⟨e_inter_down, he_mem, hdown, hob⟩
  apply hcontra.diffClusterNotBetweenCles
  use e_inter_down, he_mem
  exact ⟨DiffClusterCLE.NotBetweenCLEs.constraints_of_downgrade hdown hdiff_w_protocol hdiff_r_protocol, hob⟩

/-- Helper lemma for Case 2: Different cache case with protocol analysis -/
lemma noInterveningWrites_diffCache_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w e_r e_inter : Event n}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite_cluster : e_inter.isClusterCache)
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  (hsame_cache : ¬e_inter.sameStructure n e_w)
  : Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose) := by

  -- Case split on whether e_inter is in the same protocol/cluster as e_w and e_r
  by_cases hsame_protocol : e_inter.sameProtocol n e_w
  · -- Case 2a: Same protocol/cluster, different cache
    exact noInterveningWrites_diffCache_sameProtocol_case
      _hw_is_write _r_is_read _hsame_struct hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin _hcle_eq _hknow_dir_access
      (he_inter := he_inter) hwrite_cluster hwrite hcontra hinter_lin hsame_cache hsame_protocol
  · -- Case 2b: Different protocol/cluster
    exact noInterveningWrites_diffCache_diffProtocol_case
      _hw_is_write _r_is_read _hsame_struct hw_c_and_g_lin hr_c_and_g_lin _hcle_eq _hknow_dir_access
      (he_inter := he_inter) hwrite hcontra hinter_lin hsame_cache hsame_protocol

/-- If no writes are between GLEs and GLEs are equal, then no writes are between the original events -/
lemma noInterveningWrites_implies_no_writes_between
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (_hno_intervening : NoInterveningWrites _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin _hknow_dir_access)
  (_hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (_hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Event.Between.noWrite b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose := by
  intro e he hwrite_cluster hwrite

  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose

  have hcontra := _hno_intervening e he hwrite_cluster hwrite
  have hinter_lin := _hknow_dir_access cmp b init e

  by_cases hsame_protocol : e.sameProtocol n e_w
  .
    -- Case split: same cache, different cache same cluster, or different cluster
    by_cases hsame_cache : e.sameStructure n e_w
    · -- Case 1: Same cache as e_w (and e_r)
      apply Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites.otherWSameCache
      constructor
      · -- Prove: sameProtocol
        -- If e and e_w have the same structure (cache), they must have the same protocol
        have hsame_r : e.sameStructure n e_r := by
          unfold Event.sameStructure at *
          rw[← _hsame_struct]
          exact hsame_cache
        have hsame_w_protocol : e.sameProtocol n e_w := sameStructure_implies_sameProtocol hsame_cache
        have hsame_r_protocol : e.sameProtocol n e_r := sameStructure_implies_sameProtocol hsame_r
        exact ⟨hsame_w_protocol, hsame_r_protocol⟩
      · -- Prove: sameCache
        have hsame_r : e.sameStructure n e_r := by
          unfold Event.sameStructure at *
          rw[← _hsame_struct]
          exact hsame_cache
        exact ⟨hsame_cache, hsame_r⟩
      · -- Prove: interCleNotBetween
        exists hinter_lin.hreq's_dir_access.choose
        constructor
        · exact hinter_lin.hreq's_dir_access.choose_spec.left
        intro ⟨hdir_access, hbetween⟩ ⟨_, hcle_between⟩
        -- Use successive writes constraint: timing contradiction
        have hw_ob_e : e_w.OrderedBefore n e := hbetween.pred
        have he_ob_r : e.OrderedBefore n e_r := hbetween.succ
        have hr_end_before_e_end : e_r.oEnd < e.oEnd := _hsucc_w_of_w_after_r e he ⟨hwrite, hsame_protocol, hsame_cache, hw_ob_e⟩
        simp [Event.OrderedBefore] at he_ob_r
        have hr_well_formed := e_r.oWellFormed
        have hcontra_timing : e_r.oEnd < e_r.oStart := by
          calc e_r.oEnd
            _ < e.oEnd := hr_end_before_e_end
            _ < e_r.oStart := he_ob_r
        exact absurd (Nat.lt_trans hr_well_formed hcontra_timing) (Nat.lt_irrefl _)
    · -- Case 2: Different cache than e_w (and e_r)
      -- Delegate to helper lemma that handles protocol cases and dirAccessOfRequest analysis
      exact noInterveningWrites_diffCache_case _hw_is_write _r_is_read _hsame_struct
        hw_not_down r_not_down
        hw_c_and_g_lin hr_c_and_g_lin _hcle_eq _hknow_dir_access (he_inter := he)
        hwrite_cluster hwrite hcontra hinter_lin hsame_cache
  . -- TODO [AZ]; Fill in this case where e_inter is in a different protocol than e_w.
    sorry

/-- When CLEs are equal, the events must be in the same protocol/cluster -/
lemma same_cle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  : e_w.protocol = e_r.protocol := by
  -- Directory events are protocol-specific
  -- Both events access the same directory event, which belongs to a specific protocol
  -- From cacheEncapsulatesCorrespondingDirEvent, we have sameProtocol : e_req.protocol = e_dir.protocol
  -- Therefore both e_w and e_r must be in the same protocol as the shared directory event
  have hw_cle_protocol :
      hw_c_and_g_lin.hreq's_dir_access.choose.protocol = e_w.protocol :=
    write_cle_protocol_eq_write_protocol hw_c_and_g_lin
  have hr_cle_protocol :
      hr_c_and_g_lin.hreq's_dir_access.choose.protocol = e_r.protocol :=
    read_cle_protocol_eq_read_protocol hr_c_and_g_lin
  have hcle_protocol_eq :
      hw_c_and_g_lin.hreq's_dir_access.choose.protocol =
        hr_c_and_g_lin.hreq's_dir_access.choose.protocol := by
    simp [hcle_eq]
  calc
    e_w.protocol = hw_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hw_cle_protocol.symm
    _ = hr_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hcle_protocol_eq
    _ = e_r.protocol :=
      hr_cle_protocol

-- Helper: if a directory event corresponds to two request events, they are equal.
lemma dir_event_of_req_event_unique
  {e_dir e_req1 e_req2 : Event n}
  (hreq1 : e_dir.dirEventOfReqEvent n e_req1)
  (hreq2 : e_dir.dirEventOfReqEvent n e_req2)
  : e_req1 = e_req2 := by
  cases e_dir <;> cases e_req1 <;> cases e_req2 <;>
    simp[Event.dirEventOfReqEvent] at hreq1 hreq2
  · -- directoryEvent / cacheEvent / cacheEvent
    have hce1 := hreq1.correspondingCE
    have hce2 := hreq2.correspondingCE
    have hce : _ := hce1.symm.trans hce2
    simp[hce]

-- Helper: extract ordering from ImmediateBottomPredSatisfyingProp
lemma pred_ordering_from_imm_bottom_pred_satisfying_prop
  {b : Behaviour n} {e_pred e_req : Event n} {p : Event n → Prop}
  (hpred_struct : b.IsImmediateBottomPredSatisfyingProp n e_pred e_req p)
  : e_pred.OrderedBefore n e_req := by
  -- Extract from the structure: isImmPred contains the predecessor information
  have hpred_imm_pred_satisfying := hpred_struct.isImmPred
  -- isImmPred of type EntryImmediatePredecessorSatisfyingProp contains bPred
  have hpred_predecessor := hpred_imm_pred_satisfying.bPred
  -- bPred has isPred which gives us the Event.Predecessor relation
  exact hpred_predecessor.isPred

/-- When CLEs are equal, the events must be at the same cache -/
lemma same_cle_implies_same_struct
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
--   {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  : e_w.struct = e_r.struct := by
  classical
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
  have hw_cle_in_b := hw_c_and_g_lin.hreq's_dir_access.choose_spec.left
  have hr_cle_in_b := hr_c_and_g_lin.hreq's_dir_access.choose_spec.left
  have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
  have hr_dir_access := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right
  have hcle : e_w_cle = e_r_cle := hcle_eq
  -- Helper: sameEntry implies same struct.
  have hsame_struct_of_entry :
      ∀ {e₁ e₂ : Event n}, e₁.sameEntry n e₂ → e₁.struct = e₂.struct := by
    intro e₁ e₂ hentry
    exact Event.same_entry_impl_same_struct (n := n) e₁ e₂ hentry
  -- Align the CLEs and split by how each request accesses the directory.
  have hr_dir_access' : b.dirAccessOfRequest n init e_r e_w_cle := by
    simpa [hcle] using hr_dir_access
  cases hw_dir_access with
  | encapDir _ hw_encap =>
    cases hr_dir_access' with
    | encapDir _ hr_encap =>
      have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_encap.dirOfReq
      simp[hreq_eq]
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_pred_access.dirOfReq
      -- e_r is same entry as its predecessor that corresponds to the directory event.
      have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hr_struct := hsame_struct_of_entry hr_entry
      -- rewrite predecessor to e_w using hreq_eq
      have hr_struct' : e_r.struct = e_w.struct := by
        have hr_struct' : e_r.struct = hr_pred.choose.struct := hr_struct.symm
        have hr_struct'' : e_r.struct = e_w.struct := by
          simpa[hreq_eq] using hr_struct'
        exact hr_struct''
      exact hr_struct'.symm
    | orderAfterDir _ hr_succ =>
      have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
      -- e_r is same entry as its successor that corresponds to the directory event.
      have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hr_struct := hsame_struct_of_entry hr_entry
      have hr_struct' : e_r.struct = e_w.struct := by
        have hr_struct' : e_r.struct = hr_succ.choose.struct := hr_struct
        have hr_struct'' : e_r.struct = e_w.struct := by
          simpa[hreq_eq] using hr_struct'
        exact hr_struct''
      exact hr_struct'.symm
  | orderBeforeDir _ hw_pred hw_pred_access _ =>
    cases hr_dir_access' with
    | encapDir _ hr_encap =>
      have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_encap.dirOfReq
      have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hw_struct' : e_w.struct = e_r.struct := by
        have hw_struct' : e_w.struct = hw_pred.choose.struct := hw_struct.symm
        have hw_struct'' : e_w.struct = e_r.struct := by
          simpa[hreq_eq] using hw_struct'
        exact hw_struct''
      exact hw_struct'
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_pred_access.dirOfReq
      have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hr_struct := hsame_struct_of_entry hr_entry
      -- Both e_w and e_r share the same directory-corresponding predecessor.
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_pred.choose.struct := hw_struct.symm
        have hr' : e_r.struct = hr_pred.choose.struct := hr_struct.symm
        have hr'' : e_r.struct = hw_pred.choose.struct := by
          simpa[hreq_eq] using hr'
        exact hw'.trans hr''.symm
      exact this
    | orderAfterDir _ hr_succ =>
      have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
      have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hr_struct := hsame_struct_of_entry hr_entry
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_pred.choose.struct := hw_struct.symm
        have hr' : e_r.struct = hr_succ.choose.struct := hr_struct
        have hr'' : e_r.struct = hw_pred.choose.struct := by
          simpa[hreq_eq] using hr'
        exact hw'.trans hr''.symm
      exact this
  | orderAfterDir _ hw_succ =>
    cases hr_dir_access' with
    | encapDir _ hr_encap =>
      have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_encap.dirOfReq
      have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_succ.choose.struct := hw_struct
        have hw'' : e_w.struct = e_r.struct := by
          simpa[hreq_eq] using hw'
        exact hw''
      exact this
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_pred_access.dirOfReq
      have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hr_struct := hsame_struct_of_entry hr_entry
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_succ.choose.struct := hw_struct
        have hr' : e_r.struct = hr_pred.choose.struct := hr_struct.symm
        have hr'' : e_r.struct = hw_succ.choose.struct := by
          simpa[hreq_eq] using hr'
        exact hw'.trans hr''.symm
      exact this
    | orderAfterDir _ hr_succ =>
      have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
      have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hr_struct := hsame_struct_of_entry hr_entry
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_succ.choose.struct := hw_struct
        have hr' : e_r.struct = hr_succ.choose.struct := hr_struct
        have hr'' : e_r.struct = hw_succ.choose.struct := by
          simpa[hreq_eq] using hr'
        exact hw'.trans hr''.symm
      exact this

/-- When GLEs and CLEs are equal, write must be ordered before read -/
lemma eq_gle_cle_implies_write_before_read
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (hr_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  : e_w.OrderedBefore n e_r := by
  -- Cache events are ordered or encapsulated; with no downgrades, only ordering remains.
  have _ := hw_is_write
  have _ := r_is_read
  have _ := hgle_eq
  have _ := hcle_eq
  cases hw_ev : e_w with
  | directoryEvent de_w =>
    have : e_w.isCacheEvent := hw_cluster.eAtCache
    simp[Event.isCacheEvent, hw_ev] at this
  | cacheEvent ce_w =>
    cases hr_ev : e_r with
    | directoryEvent de_r =>
      have : e_r.isCacheEvent := hr_cluster.eAtCache
      simp[Event.isCacheEvent, hr_ev] at this
    | cacheEvent ce_r =>
      have hordered := b.orderedAtEntry.cache_ordered ce_w ce_r
      have hencap_or_ordered := hordered.ordered
      have hw_not_down' : ¬ ce_w.down := by
        simpa[Event.down, hw_ev] using hw_not_down
      have hr_not_down' : ¬ ce_r.down := by
        simpa[Event.down, hr_ev] using hr_not_down
      cases hencap_or_ordered with
      | inl hencap_or_before =>
        cases hencap_or_before with
        | inl hencap_by =>
          have hdown : ce_w.down := b.orderedAtEntry.cache_encap_rule ce_r ce_w hencap_by
          exact (hw_not_down' hdown).elim
        | inr h_ob =>
          simpa[Event.OrderedBefore, Event.oEnd, Event.oStart, hw_ev, hr_ev] using h_ob
      | inr hencap_or_before =>
        cases hencap_or_before with
        | inl hencap_by =>
          have hdown : ce_r.down := b.orderedAtEntry.cache_encap_rule ce_w ce_r hencap_by
          exact (hr_not_down' hdown).elim
        | inr h_ob =>
          have h_ob_ev : e_r.OrderedBefore n e_w := by
            simpa[Event.OrderedBefore, Event.oEnd, Event.oStart, hr_ev, hw_ev] using h_ob
          exact (hr_not_ob_w h_ob_ev).elim

-- Helper lemma: true is not ≤ false for Bool
lemma bool_true_not_le_false : ¬(true ≤ false) := by decide

-- Helper lemma: a state with c=true cannot be < a state with c=false
lemma state_true_not_lt_false {p₁ p₂ : Permissions} : ¬(State.mk p₁ true < State.mk p₂ false) := by
  intro h
  show False
  have : true ≤ false := h.right.left
  exact bool_true_not_le_false this

-- Helper lemma: a state with c=true cannot be ≤ a state with c=false
lemma state_true_not_le_false {p₁ p₂ : Permissions} : ¬(State.mk p₁ true ≤ State.mk p₂ false) := by
  intro h
  show False
  cases h with
  | inl hlt => exact state_true_not_lt_false hlt
  | inr heq =>
    injection heq with _ hc
    exact Bool.noConfusion hc

-- Helper lemma: I is not ≥ Vc (I < Vc but not I ≥ Vc)
lemma I_not_ge_Vc : ¬(Vc ≤ I) := by
  intro h
  show False
  cases h with
  | inl hlt =>
    -- Vc < I means some r ≤ none ∧ false ≤ false ∧ Vc ≠ I
    -- But some r ≤ none is false
    have : (some ReadWritePermissions.r : Permissions) ≤ (none : Permissions) := hlt.left
    cases this
  | inr heq =>
    -- Vc = I is false by definition
    injection heq with hp
    cases hp

-- Helper lemma: I is not ≥ Vd
lemma I_not_ge_Vd : ¬(Vd ≤ I) := by
  intro h
  show False
  cases h with
  | inl hlt =>
    -- Vd < I means some wr ≤ none ∧ false ≤ false ∧ Vd ≠ I
    -- But some wr ≤ none is false
    have : (some ReadWritePermissions.wr : Permissions) ≤ (none : Permissions) := hlt.left
    cases this
  | inr heq =>
    -- Vd = I is false by definition
    injection heq with hp
    cases hp

-- Helper: write permission not ≤ read permission
lemma permission_wr_not_le_r : ¬((some ReadWritePermissions.wr : Permissions) ≤ (some ReadWritePermissions.r : Permissions)) := by
  decide

-- Helper: read permission not ≤ none
lemma permission_r_not_le_none : ¬((some ReadWritePermissions.r : Permissions) ≤ (none : Permissions)) := by
  decide

-- Helper: write permission not ≤ none
lemma permission_wr_not_le_none : ¬((some ReadWritePermissions.wr : Permissions) ≤ (none : Permissions)) := by
  decide

-- Helper lemma: MRS for coherent requests always has c=true
lemma coherent_mrs_has_true_coherence (vr : ValidRequest) (hcoh : vr.val.coherent = true) :
  vr.MRS.c = true := by
  simp [ValidRequest.MRS]
  split
  · -- Case: ⟨⟨rw,true,.SC⟩,_⟩
    rfl
  · -- Case: ⟨⟨.w,true,.Rel⟩,_⟩
    rfl
  · -- Case: ⟨⟨.w,true,.Weak⟩,_⟩
    rfl
  all_goals
    -- All other cases have coherent = false, contradicting hcoh
    simp at hcoh

-- Helper lemma: DowngradeState for coherent SC evict with SW state produces I (c=false)
lemma coherent_sc_evict_downgrade_to_i (vr : ValidRequest)
  (hcoh : vr.val.coherent = true) (hsc : vr.val.consistency = .SC)
  (hwrite : vr.val.rw = .w) (s : State) (hs_p : s.p = some ReadWritePermissions.wr) (hsc_true : s.c = true) :
  (vr.DowngradeState s).c = false := by
  simp [ValidRequest.DowngradeState, hsc]
  split
  · -- s.c = true case
    split
    · -- s ≤ MRS, result is I
      rfl
    · next h_not_le =>
      -- Contradiction: For coherent SC write, MRS = {some .wr, true}
      -- With s = {some .wr, true}, we have s = MRS, so s ≤ MRS must be true
      -- Therefore ¬(s ≤ MRS) leads to contradiction
      have hmrs_true : vr.MRS.c = true := coherent_mrs_has_true_coherence vr hcoh
      -- Need to show this branch returns vr.MRS which has c = false, but we just showed c = true
      -- Actually, let's show s ≤ MRS directly to contradict h_not_le
      have hs_le_mrs : s ≤ vr.MRS := by
        -- s = {some .wr, true} and MRS = {some .wr, true} for coherent SC write
        have hmrs : vr.MRS = State.mk (some ReadWritePermissions.wr) true := by
          cases vr with | mk val prop =>
          simp only [ValidRequest.MRS]
          cases val with | mk rw coh cons =>
          simp only at hcoh hsc hwrite
          subst hcoh hsc hwrite
          rfl
        have hs : s = State.mk (some ReadWritePermissions.wr) true := by
          cases s with | mk p c =>
          simp only at hs_p hsc_true
          subst hs_p hsc_true
          rfl
        rw [hs, hmrs]
        right
        rfl
      exact absurd hs_le_mrs h_not_le
  · next heq_false =>
      -- vr.val.coherent = false: contradicts hcoh
      simp [hcoh] at heq_false

-- Helper lemma: For coherent SC write evicts, DowngradeState SW = I
lemma coherent_sc_write_downgrade_sw_to_i
  (vr : ValidRequest)
  (hcons : vr.val.consistency = .SC)
  (hcoh : vr.val.coherent = true)
  (hwrite : vr.val.rw = .w)
  : vr.DowngradeState SW = I := by
  simp[ValidRequest.DowngradeState, hcoh, hcons,]
  simp[ValidRequest.MRS]
  match hvr : vr with
  | ⟨⟨.w, true, .SC⟩, _⟩ =>
    simp[]
    simp[SW]
    simp[ReadWrite.toPerms, ReadWrite.toRWPerms]
    simp[LE.le, State.le]

-- Helper lemma: Non-coherent request with coherent perms contradicts non-coherent evict result
-- This is only used when the read is actually coherent, showing a direct contradiction
lemma nc_request_coherent_perms_contradiction
  {b : Behaviour n} {init : InitialSystemState n} {e_r_ce ce_evict : CacheEvent n}
  (_hhascoh : Behaviour.reqHasPermsOnCoherentState n b init (Event.cacheEvent e_r_ce))
  (hr_coh : e_r_ce.req.val.coherent = true)
  (hmrs_c_false : e_r_ce.req.MRS.c = false)
  (_hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false)
  (_hevict_leaves_at_least : e_r_ce.req.MRS ≤ ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true })
  : False := by
  -- The non-coherent request is made on a coherent state (hhascoh.onCoherentState)
  -- and must have stateReqMadeOn.c = true
  -- But evict produces DowngradeState.c = false
  -- With MRS ≤ DowngradeState and MRS.c = false, we get a permission constraint
  -- that contradicts the specific MRS values for Rel/Weak writes
  have hmrs_true : e_r_ce.req.MRS.c = true := coherent_mrs_has_true_coherence e_r_ce.req hr_coh
  rw [hmrs_true] at hmrs_c_false
  exact Bool.noConfusion hmrs_c_false

-- For Rel/Acq consistency with coherent writes, DowngradeState returns Vc (c=false)
-- For Weak consistency with coherent writes, DowngradeState returns Vd (c=false)
lemma coherent_rel_acq_weak_write_downgrade_to_false (vr : ValidRequest)
  (hcoh : vr.val.coherent = true) (_hwrite : vr.val.rw = .w)
  (hcons : vr.val.consistency = .Rel ∨ vr.val.consistency = .Acq ∨ vr.val.consistency = .Weak)
  (s : State) (hsc_true : s.c = true) :
  (vr.DowngradeState s).c = false := by
  -- For coherent Rel/Acq/Weak, DowngradeState is: if s ≤ Vc then s else Vc
  -- With s = {wr, true}, we need to show either s.c = false (impossible since hsc_true)
  -- or s > Vc (which means result is Vc with c=false)
  simp [ValidRequest.DowngradeState, hcoh]
  cases hcons with
  | inl hrel =>
      -- Rel case: result is if s ≤ Vc then s else Vc
      simp [hrel]
      split
      · -- s ≤ Vc: result is s
        -- But s has c=true and Vc has c=false, so s ≤ Vc requires true ≤ false, impossible
        next h_le =>
          have : s.c ≤ Vc.c := by
            cases h_le with
            | inl hlt => exact hlt.right.left
            | inr heq => rw [heq]
          simp at this
          rw [hsc_true] at this
          exact absurd this bool_true_not_le_false
      · -- s > Vc: result is Vc
        rfl
  | inr hrest =>
      cases hrest with
      | inl hacq =>
          -- Acq case: same as Rel
          simp [hacq]
          split
          · next h_le =>
              have : s.c ≤ Vc.c := by
                cases h_le with
                | inl hlt => exact hlt.right.left
                | inr heq => rw [heq]
              simp at this
              rw [hsc_true] at this
              exact absurd this bool_true_not_le_false
          · rfl
      | inr hweak =>
          -- Weak case: same as Rel/Acq
          simp [hweak]
          split
          · next h_le =>
              have : s.c ≤ Vc.c := by
                cases h_le with
                | inl hlt => exact hlt.right.left
                | inr heq => rw [heq]
              simp at this
              rw [hsc_true] at this
              exact absurd this bool_true_not_le_false
          · rfl

lemma read_mrs_le_write_coherent_evict_contradiction (_cmp : CompoundProtocol n)

{b : Behaviour n} {init : InitialSystemState n}
(e_r_ce ce_evict : CacheEvent n)
(hevict_sw_evict : (Event.cacheEvent ce_evict).isEvictSW)
(hreq_r_has_perms : Behaviour.reqHasPerms n b init (Event.cacheEvent e_r_ce))
(hr_coherent : e_r_ce.req.val.coherent = true)
(hevict_is_coherent : ce_evict.req.val.coherent = true)
(hevict_leaves_at_least : e_r_ce.req.MRS ≤ ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true })
  : False := by
  -- The key: MRS for coherent e_r has c=true, DowngradeState for coherent evict produces c=false
  -- This creates an immediate contradiction

  -- Case analysis on how the read request has permissions
  cases hreq_r_has_perms with
  | hasPerms hreq_r_is_coherent hreq_r_state_sufficient =>
      -- For coherent requests, MRS always has c=true
      have hr_coh : e_r_ce.req.val.coherent = true := by
        simp [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at hreq_r_is_coherent
        exact hreq_r_is_coherent

      -- Use our helper lemmas
      have hmrs_true : e_r_ce.req.MRS.c = true := coherent_mrs_has_true_coherence e_r_ce.req hr_coh

      -- For the evict, we know it's a coherent write evict (isEvictSW)
      -- From hevict_sw_evict.coherentWrite, ce_evict is a coherent write
      -- For coherent write evicts that are SC, the DowngradeState produces c=false
      have hevict_coherent_write : ce_evict.req.isCoherentWrite := hevict_sw_evict.coherentWrite

      -- Extract evict consistency - for now focus on SC case
      cases hevict_cons : ce_evict.req.val.consistency
      · -- SC: DowngradeState with SW produces I (c=false)
        have hevict_write : ce_evict.req.val.rw = .w := by
          simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
          exact hevict_coherent_write.right
        have hdowngrade_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false :=
          coherent_sc_evict_downgrade_to_i ce_evict.req hevict_is_coherent hevict_cons hevict_write _ rfl rfl

        -- Now we have MRS.c = true ≤ DowngradeState.c = false, which is a contradiction
        have : e_r_ce.req.MRS.c ≤ (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c := by
          cases hevict_leaves_at_least with
          | inl hlt =>
              -- MRS < DowngradeState
              exact hlt.right.left
          | inr heq =>
              -- MRS = DowngradeState
              rw [heq]
        rw [hmrs_true, hdowngrade_false] at this
        exact bool_true_not_le_false this
      · -- Rel: coherent write evict with Rel downgrade
        have hevict_write : ce_evict.req.val.rw = .w := by
          simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
          exact hevict_coherent_write.right
        have hdowngrade_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false :=
          coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inl hevict_cons) _ rfl

        have : e_r_ce.req.MRS.c ≤ (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c := by
          cases hevict_leaves_at_least with
          | inl hlt => exact hlt.right.left
          | inr heq => rw [heq]
        rw [hmrs_true, hdowngrade_false] at this
        exact bool_true_not_le_false this
      · -- Acq: coherent write evict with Acq downgrade
        have hevict_write : ce_evict.req.val.rw = .w := by
          simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
          exact hevict_coherent_write.right
        have hdowngrade_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false :=
          coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inl hevict_cons)) _ rfl

        have : e_r_ce.req.MRS.c ≤ (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c := by
          cases hevict_leaves_at_least with
          | inl hlt => exact hlt.right.left
          | inr heq => rw [heq]
        rw [hmrs_true, hdowngrade_false] at this
        exact bool_true_not_le_false this
      ·  -- Weak: coherent write evict with Weak downgrade
        have hevict_write : ce_evict.req.val.rw = .w := by
          simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
          exact hevict_coherent_write.right
        have hdowngrade_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false :=
          coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inr hevict_cons)) _ rfl

        have : e_r_ce.req.MRS.c ≤ (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c := by
          cases hevict_leaves_at_least with
          | inl hlt => exact hlt.right.left
          | inr heq => rw [heq]
        rw [hmrs_true, hdowngrade_false] at this
        exact bool_true_not_le_false this

  | ncRelAcqWeakWriteHasCoherentPerms hncraw hhascoh =>
      -- For non-coherent requests on coherent state, MRS has c=false
      -- Evict produces state with c=false (at most), creating permission issues
      have hevict_coherent_write : ce_evict.req.isCoherentWrite := hevict_sw_evict.coherentWrite

      simp [Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite] at hncraw
      cases hncraw with
      | inl hrel =>
          -- Acq: MRS = Vc = {some .r, false}
          have hmrs_vc : e_r_ce.req.MRS = Vc := by
            simp only [CacheEvent.isAcquire, ValidRequest.isAcquire] at hrel
            rw [hrel]; rfl
          cases hevict_cons : ce_evict.req.val.consistency
          · -- SC evict: DowngradeState = I, so Vc ≤ I requires r ≤ none (contradiction)
            have hevict_write : ce_evict.req.val.rw = .w := by
              simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
              exact hevict_coherent_write.right
            have hdowngrade_i : ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true } = I := by
              exact coherent_sc_write_downgrade_sw_to_i ce_evict.req hevict_cons hevict_is_coherent hevict_write
            have : e_r_ce.req.MRS ≤ I := by rw [← hdowngrade_i]; exact hevict_leaves_at_least
            rw [hmrs_vc] at this
            exact I_not_ge_Vc this
          · -- Rel evict: DowngradeState = Vc (c=false), but e_r has coherent perms
            have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
              have hevict_write : ce_evict.req.val.rw = .w := by
                simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                exact hevict_coherent_write.right
              exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inl hevict_cons) _ rfl
            exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least
          · -- Acq evict: DowngradeState = Vc (c=false), but e_r has coherent perms
            have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
              have hevict_write : ce_evict.req.val.rw = .w := by
                simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                exact hevict_coherent_write.right
              exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inl hevict_cons)) _ rfl
            exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least
          · -- Weak evict: DowngradeState = Vc (c=false), but e_r has coherent perms
            have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
              have hevict_write : ce_evict.req.val.rw = .w := by
                simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                exact hevict_coherent_write.right
              exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inr hevict_cons)) _ rfl
            exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least
      | inr hrest =>
          cases hrest with
          | inl hrel =>
              -- Rel write: MRS = Vd = {some .wr, false}
              have hmrs_vd : e_r_ce.req.MRS = Vd := by
                simp only [CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hrel
                rw [hrel]; rfl
              cases hevict_cons : ce_evict.req.val.consistency
              · -- SC evict: DowngradeState = I, so Vd ≤ I requires wr ≤ none (contradiction)
                have hevict_write : ce_evict.req.val.rw = .w := by
                  simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                  exact hevict_coherent_write.right
                have hdowngrade_i : ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true } = I := by
                  exact coherent_sc_write_downgrade_sw_to_i ce_evict.req hevict_cons hevict_is_coherent hevict_write
                have : e_r_ce.req.MRS ≤ I := by rw [← hdowngrade_i]; exact hevict_leaves_at_least
                rw [hmrs_vd] at this
                exact I_not_ge_Vd this
              · -- Rel evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inl hevict_cons) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vd];) hdowngrade_c_false hevict_leaves_at_least
              · -- Acq evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inl hevict_cons)) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vd];) hdowngrade_c_false hevict_leaves_at_least
              · -- Weak evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inr hevict_cons)) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vd];) hdowngrade_c_false hevict_leaves_at_least
          | inr hweakwrite =>
              -- Weak write: MRS = Vc = {some .r, false}
              have hmrs_vc : e_r_ce.req.MRS = Vc := by
                simp only [CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at hweakwrite
                rw [hweakwrite]; rfl
              cases hevict_cons : ce_evict.req.val.consistency
              · -- SC evict: DowngradeState = I, so Vc ≤ I requires r ≤ none (contradiction)
                have hevict_write : ce_evict.req.val.rw = .w := by
                  simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                  exact hevict_coherent_write.right
                have hdowngrade_i : ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true } = I := by
                  exact coherent_sc_write_downgrade_sw_to_i ce_evict.req hevict_cons hevict_is_coherent hevict_write
                have : e_r_ce.req.MRS ≤ I := by rw [← hdowngrade_i]; exact hevict_leaves_at_least
                rw [hmrs_vc] at this
                exact I_not_ge_Vc this
              · -- Rel evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inl hevict_cons) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least
              · -- Acq evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inl hevict_cons)) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least
              · -- Weak evict: DowngradeState = Vc (c=false), but e_r has coherent perms
                have hdowngrade_c_false : (ce_evict.req.DowngradeState { p := some ReadWritePermissions.wr, c := true }).c = false := by
                  have hevict_write : ce_evict.req.val.rw = .w := by
                    simp [ValidRequest.isCoherentWrite, Request.isCoherentWrite, Request.isWrite] at hevict_coherent_write
                    exact hevict_coherent_write.right
                  exact coherent_rel_acq_weak_write_downgrade_to_false ce_evict.req hevict_is_coherent hevict_write (Or.inr (Or.inr hevict_cons)) _ rfl
                exact nc_request_coherent_perms_contradiction hhascoh hr_coherent (by rw [hmrs_vc];) hdowngrade_c_false hevict_leaves_at_least

  | ncWeakReadHasPermsNotVd hncwr hhaspermsnvd =>
      -- A non-coherent weak read implies coherent=false, contradicting hr_coherent
      have hr_coh_false : e_r_ce.req.val.coherent = false := by
        simp only [Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at hncwr
        simp [hncwr]
      rw [hr_coherent] at hr_coh_false
      exact Bool.noConfusion hr_coh_false


/- Helper lemma: coherent downgrade cannot maintain state >= required -/
lemma coherent_evict_downgrade_contradiction

  (cmp : CompoundProtocol n)
  {b : Behaviour n} {init : InitialSystemState n}
  {e_evict e_r : Event n}
  (hr_is_cache : e_r.isClusterCache)
  (hr_is_read : e_r.isRead)
  (hreq_r_has_perms : b.reqHasPerms n init e_r)
  (hr_coherent : e_r.isCoherent)
  (hevict_sw_evict : e_evict.isEvictSW)
  (hevict_in_b : e_evict ∈ b)
  (hevict_is_coherent : e_evict.isCoherent)
  (hevict_is_cache : e_evict.isCacheEvent)
  (hevict_leaves_at_least : b.reqLeavesStateAtLeast n e_evict init e_r.req.MRS)
  : False := by
  -- Unfold reqLeavesStateAtLeast: state after evict >= required state
  unfold Behaviour.reqLeavesStateAtLeast at hevict_leaves_at_least

  -- We know e_evict.isCoherent means e_evict_coherent = true
  -- and e_evict.isEvict means this is an evict request
  -- For a coherent evict (downgrade), the state after must be reduced
  -- But hevict_leaves_at_least says state after >= required
  -- This creates the contradiction

  -- Unfold stateAfter to see the downgrade transition
  unfold Behaviour.stateAfter at hevict_leaves_at_least

  -- Now we need to see how state changes through the evict
  -- For coherent downgrades, the state is reduced by the downgrade semantics
  -- unfold List.stateAfter at hevict_leaves_at_least

  -- cases es_up_to_evict : Behaviour.eventsUpToEvent n b e_evict
  -- . case nil =>
  -- TODO: Use the state before `e_evict` (it has permissions at least `e_r`'s MRS)
  --
  have evict_dir_access := cmp.dirAccessOfRequest n b init e_evict hevict_in_b
  obtain ⟨e_evict_cle, hevict_cle_in_b, hevict_cle_spec⟩ := evict_dir_access

  -- Use the "has permissions" fact for `e_evict` during a case analysis on
  -- the state before `e_evict`. Then unfold and show the state after `e_evict` is
  -- reduced lower than `e_r`'s MRS, contradicting the `hevict_leaves_state_at_least` "leaves state at least" fact.
  cases hevict_cle_spec
  . case encapDir hreq_missing_perms hencap_dir =>
    cases hreq_missing_perms
    . case downgrade hreq_is_down hreq_on_mrs_state  =>
      simp[Behaviour.evictOnMRSState] at hreq_on_mrs_state
      simp[Behaviour.stateBefore] at hreq_on_mrs_state

      rw[Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore] at hevict_leaves_at_least
      simp[Behaviour.stateBefore] at hevict_leaves_at_least
      -- Use Behaviour.wrap_cache_state_to_entry_state
      have hunwrap_EntryCache.state := Behaviour.unwrap_cache_state_to_entry_state n (hevict_is_cache) (b.initCacheStateIsCache e_evict init hevict_is_cache) hreq_on_mrs_state
      rw[hunwrap_EntryCache.state] at hevict_leaves_at_least
      -- Use `hevict_least_state_at_least` to show a contradiction; `e_r`'s MRS will be higher than `e_evict`'s state after
      -- TODO: finish this case.
      cases e_evict with
      | directoryEvent de =>
        -- impossible: e_evict is a cache event
        simp [Event.isCacheEvent] at hevict_is_cache
      | cacheEvent ce_evict =>
        -- reduce with the coherence bit from `hevict_is_coherent`
        cases hevict_coherence : ce_evict.req.val.coherent with
        | false =>
          simp [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at hevict_is_coherent
          absurd hevict_coherence
          simp[hevict_is_coherent]
        | true =>
          -- have hevict_down := hevict_is_evict.downgrade
          simp[Event.isEvictSW,] at hevict_sw_evict
          -- have hevict_down := hevict_sw_evict.evict.downgrade

          /- Open up the e_r.MRS ≤ e_evict.stateAfter hypothesis `hevict_leaves_at_least` -/
          simp[Event.req, Event.MRS,] at hevict_leaves_at_least
          simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hevict_leaves_at_least
          simp[Event.down] at hevict_leaves_at_least
          simp[hevict_sw_evict.evict.downgrade] at hevict_leaves_at_least

          /- `e_r` is a cache event. -/
          have hr_cache := hr_is_cache.eAtCache
          simp[Event.isCacheEvent] at hr_cache
          cases he_r : e_r <;> simp[he_r] at hr_cache

          rename_i e_r_ce
          case cacheEvent.true.cacheEvent =>
            --
            simp[he_r] at hevict_leaves_at_least
            simp[List.stateAfter, Event.SucceedingState, CacheEvent.SucceedingState, hevict_sw_evict.evict.downgrade] at hevict_leaves_at_least
            simp[EntryState.cache] at hevict_leaves_at_least

            have hevict_is_write := hevict_sw_evict.coherentWrite.right
            simp[Request.isWrite] at hevict_is_write
            have hevict_is_coherent := hevict_sw_evict.coherentWrite.left
            simp[Request.isCoherent] at hevict_is_coherent

            simp[hevict_is_write] at hevict_leaves_at_least
            simp[hevict_is_coherent] at hevict_leaves_at_least

            simp[he_r] at hreq_r_has_perms

            simp[he_r] at hr_coherent

            exact read_mrs_le_write_coherent_evict_contradiction cmp e_r_ce ce_evict hevict_sw_evict hreq_r_has_perms hr_coherent hevict_is_coherent hevict_leaves_at_least
    . case noPermsForNonNcRelAcqWeakWrite hreq_not_down hreq_not_nc_rel_acq_ww hno_perms =>
      -- Contradiction: `e_evict` is a downgrade ^ `hreq_not_down` says it's not a downgrade
      have hevict_down : e_evict.down := by
        cases e_evict with
        | cacheEvent ce_evict =>
            have hsw : ce_evict.isEvictSW := by
              simpa [Event.isEvictSW] using hevict_sw_evict
            exact hsw.evict.downgrade
        | directoryEvent de =>
            simp [Event.isCacheEvent] at hevict_is_cache
      exact hreq_not_down hevict_down
    . case ncRelAcqWeakWriteNotOnCoherentState hreq_not_down hreq_nc_rel_acq hno_perms =>
      -- Contradiction: `e_evict` is a downgrade ^ `hreq_not_down` says it's not a downgrade
      have hevict_down : e_evict.down := by
        cases e_evict with
        | cacheEvent ce_evict =>
            have hsw : ce_evict.isEvictSW := by
              simpa [Event.isEvictSW] using hevict_sw_evict
            exact hsw.evict.downgrade
        | directoryEvent de =>
            simp [Event.isCacheEvent] at hevict_is_cache
      exact hreq_not_down hevict_down
  . case orderBeforeDir hreq_has_perms hexists_pred_getting_perms
    hpred_accesses_dir hinter_leaves_state_at_least hpred_same_protocol hnot_down =>

    simp[Event.isEvictSW] at hevict_sw_evict
    cases e_evict with
    | directoryEvent _ =>
        simp [Event.isCacheEvent] at hevict_is_cache
    | cacheEvent ce_evict =>
      simp[] at hevict_sw_evict
      have hce_evict := hevict_sw_evict.evict.downgrade
      simp[Event.down] at hnot_down
      absurd hnot_down
      simp [hce_evict]
  . case orderAfterDir hweak_read_on_vd hsucc_encap_dir hsucc_same_protocol hnot_down =>
    -- Contradiction: `e_evict` is a downgrade ^ `hnot_down` says it's not a downgrade
    simp[Event.isEvictSW] at hevict_sw_evict
    cases e_evict with
    | directoryEvent _ =>
        simp [Event.isCacheEvent] at hevict_is_cache
    | cacheEvent ce_evict =>
      simp[] at hevict_sw_evict
      have hce_evict := hevict_sw_evict.evict.downgrade
      simp[Event.down] at hnot_down
      absurd hnot_down
      simp [hce_evict]

/-- Helper: Construct sameEntry from successive entries in a chain. -/
lemma same_entry_from_double_trans
  {e_1 e_2 e_3 : Event n}
  (h_12 : e_1.sameEntry n e_2)
  (h_23 : e_2.sameEntry n e_3)
  : e_1.sameEntry n e_3 :=
  ⟨h_12.sameStruct.trans h_23.sameStruct,
   h_12.sameAddr.trans h_23.sameAddr⟩

/-- From an immediate bottom predecessor spec, extract the predecessor ordering. -/
lemma pred_ord_impl (hpred : Behaviour.ImmediateBottomPredSatisfyingProp n b e_pred e  (b.predHasNoPermsAndLeavesStateAtLeastReq n init · e)) :
    e_pred.OrderedBefore n e := by
  simp only[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast, Behaviour.ImmediateBottomPredSatisfyingProp] at hpred
  have hpred_imm := hpred.isImmPred
  have hpred_is := hpred_imm.bPred.isPred
  simp only[Event.Predecessor] at hpred_is ⊢
  exact hpred_is

/-- From an immediate bottom successor spec, extract the successor ordering. -/
lemma succ_ord_impl (hsucc : Behaviour.ImmediateBottomSuccSatisfyingProp n b e e_succ (b.succOnVdWithCorrespondingDir n init · e_dir)) :
    e.OrderedBefore n e_succ := by
  simp only[Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc
  have hsucc_is := hsucc.isImmBottomSucc.isSucc
  simp only[Event.Successor, Event.Predecessor] at hsucc_is ⊢
  exact hsucc_is

/-- General version: extract ordering from any ImmediateBottomSuccSatisfyingProp. -/
lemma succ_ord_impl_general {P : Event n → Prop}
    (hsucc : Behaviour.ImmediateBottomSuccSatisfyingProp n b e e_succ P) :
    e.OrderedBefore n e_succ := by
  have hsucc_is := hsucc.isImmBottomSucc.isSucc
  exact hsucc_is

/-- Extract encapsulation from cacheEncapsulatesCorrespondingDirEvent with CLE equality. -/
lemma encap_from_dir_access_with_cle_eq
    {b : Behaviour n}
    {init : EntryState n}
    {rel_wb : Bool}
    {e_cle e_cle' : Event n}
    {e_req : Event n}
    (hdir_access : b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e_req e_cle)
    (hcle_eq : e_cle = e_cle')
    : e_req.Encapsulates n e_cle' := by
  have := hdir_access.reqEncapDir
  simpa [hcle_eq] using this

/-- Extract encapsulation from successor spec with CLE equality. -/
lemma encap_from_succ_spec_with_cle_eq
    {b : Behaviour n}
    {init : InitialSystemState n}
    {e_req e_cle e_cle' : Event n}
    (hsucc : b.immBottomSuccOnVdEncapCorrDir n init e_req e_cle)
    (hcle_eq : e_cle = e_cle')
    : hsucc.choose.Encapsulates n e_cle' := by
  have hsucc_encap_cle' := hsucc.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
  simpa [hcle_eq] using hsucc_encap_cle'

/-- Two events that both access the same directory (via encapsulation) must be the same event. -/
lemma same_dir_encap_events_eq
    {e1 e2 e_cle : Event n}
    {b : Behaviour n}
    {init : EntryState n}
    {rel_wb : Bool}
    (h1 : b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e1 e_cle)
    (h2 : b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e2 e_cle)
    : e1 = e2 := by
  have hdir1 := h1.dirOfReq
  have hdir2 := h2.dirOfReq
  exact dir_event_of_req_event_unique hdir1 hdir2

/-- Build an ordering chain and derive contradiction from dual encapsulation.
    Pattern: e1 < e_mid < e2, where e1 encaps CLE and e2's related event encaps same CLE. -/
lemma dual_encap_via_ordering_chain
    {e1 e_mid e2 e2_related : Event n}
    (he1_encap : e1.Encapsulates n e_cle)
    (he2_related_encap : e2_related.Encapsulates n e_cle)
    (h1_before_mid : e1.OrderedBefore n e_mid)
    (hmid_before_2 : e_mid.OrderedBefore n e2)
    (h2_related : e2.OrderedBefore n e2_related)
    : False :=
  let h1_before_2 := Event.ordered_trans (n := n) h1_before_mid hmid_before_2
  let h1_before_related := Event.ordered_trans (n := n) h1_before_2 h2_related
  dual_encap_ordered_contradiction he1_encap he2_related_encap h1_before_related
