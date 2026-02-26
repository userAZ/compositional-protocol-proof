import CMCM.Rf

variable {n : ℕ}

/-
Intervening writes:
for all writes `e_w_inter` in the behaviour (that are not `e_w`):
- GLE `e_w_inter` is not between `e_w`'s GLE and `e_r`'s GLE
- if CLE `e_w` and CLE `e_r` are in the same cluster, then CLE `e_w_inter` is not between CLE `e_w` and CLE `e_r`
-/

def NotBetweenGLEs (e_inter_gle e_w_gle e_r_gle : Event n)
  /-
  (e_inter e_w e_r : Event n)
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hinter_cluster : e_inter.isClusterCache}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hinter_is_write : e_inter.isWrite)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hinter_not_down : ¬ e_inter.down}
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter hinter_cluster hinter_not_down)
  -/
  : Prop := ¬ e_inter_gle.OrderedBetween n e_w_gle e_r_gle

def SameClusterCLE.NotBetweenCLEs (e_inter_cle e_w_cle e_r_cle : Event n) : Prop :=
  e_inter_cle.protocol = e_w_cle.protocol ∧ e_inter_cle.protocol = e_r_cle.protocol
  ∧ e_inter_cle.isDirWrite →
--   ¬ e_inter_cle.OrderedBefore n e_r_cle
  ¬ e_inter_cle.OrderedBetween n e_w_cle e_r_cle

structure DiffClusterCLE.NotBetweenCLEs.constraints (e_inter e_w e_r e_inter_down : Event n) : Prop where
  diffProtocol : e_inter.diffProtocol n e_w ∧ e_inter.diffProtocol n e_r
  downToW : e_inter_down.sameProtocol n e_w
  isWrite : e_inter_down.isWrite
  downIsDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  interEncapDown : e_inter.Encapsulates n e_inter_down

def DiffClusterCLE.NotBetweenCLEs (e_inter e_w e_r e_inter_down e_w_cle e_r_cle : Event n) : Prop :=
  DiffClusterCLE.NotBetweenCLEs.constraints e_inter e_w e_r e_inter_down →
--   ¬ e_inter_cle.OrderedBefore n e_r_cle
  e_inter_down.OrderedBetween n e_w_cle e_r_cle
/-- Helper lemma: constructs constraints from dirWriteDowngradeFromDiffCluster and protocol equalities -/
lemma DiffClusterCLE.NotBetweenCLEs.constraints_of_downgrade
  {e_inter e_w e_r e_inter_down : Event n}
  (hdown : Event.dirWriteDowngradeFromDiffCluster e_inter_down e_inter e_w e_r)
  (hediff_w : e_inter.protocol ≠ e_w.protocol) (hediff_r : e_inter.protocol ≠ e_r.protocol)
  : DiffClusterCLE.NotBetweenCLEs.constraints e_inter e_w e_r e_inter_down :=
  ⟨⟨hediff_w, hediff_r⟩, hdown.downToW, hdown.isWrite, hdown.isDown, hdown.isDir, hdown.interEncapDown⟩

structure NoInterveningWrites.constraints
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Prop where
  interWrite : e_w_inter.isWrite
--   notDown : ¬ e_w_inter.down
--   clusterW : e_w_inter.isClusterCache
  notSameAsW : e_w_inter ≠ e_w
  notBetweenGles :
    NotBetweenGLEs
      (hknow_dir_access cmp b init e_w_inter).hreq's_global_lin.choose
      hw_c_and_g_lin.hreq's_global_lin.choose
      hr_c_and_g_lin.hreq's_global_lin.choose
  notBetweenCles :
    SameClusterCLE.NotBetweenCLEs
      (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hr_c_and_g_lin.hreq's_dir_access.choose
  diffClusterNotBetweenCles:
    ¬ ∃ e_inter_down ∈ b,
      DiffClusterCLE.NotBetweenCLEs.constraints e_w_inter e_w e_r e_inter_down ∧
      e_inter_down.OrderedBetween n hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose
--   sameCacheNoInterWrite:
--     e_w.sameStructure n e_r →
--       ∀ e_inter_w ∈ b, e_inter_w.isClusterCache → e_inter_w.isWrite →
--         ¬ e_inter_w.sameStructure n e_w ∨
--         ¬ e_inter_w.sameStructure n e_r ∨
--         ¬ (hknow_dir_access cmp b init e_inter_w e_inter_w.isClusterCache (¬ e_inter_w.down)).hreq's_dir_access.choose.OrderedBetween n hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose

def NoInterveningWrites
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop :=
  ∀ e_w_inter ∈ b, e_w_inter.isClusterCache → e_w_inter.isWrite →
    NoInterveningWrites.constraints hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin e_w_inter hknow_dir_access

-- Helper lemmas for the main theorem

/-- When GLEs are equal, no event can be between them -/
lemma not_between_equal_events {e e₁ : Event n} : ¬ e.OrderedBetween n e₁ e₁ := by
  intro ⟨h_pred, h_succ⟩
  unfold Event.OrderedBefore at h_pred h_succ
  -- e₁.oEnd < e.oStart and e.oEnd < e₁.oStart
  -- This is a contradiction since we'd have e₁.oEnd < e.oStart < e.oEnd < e₁.oStart
  have : e₁.oEnd < e₁.oStart := calc
    e₁.oEnd < e.oStart := h_pred
    _ < e.oEnd := e.oWellFormed
    _ < e₁.oStart := h_succ
  have hwf : e₁.oStart < e₁.oEnd := e₁.oWellFormed
  simp only [TimeStart, TimeEnd] at *
  linarith

/-- Same structure (cache) implies same protocol -/
lemma sameStructure_implies_sameProtocol {e₁ e₂ : Event n}
  (hsame : e₁.sameStructure n e₂) : e₁.sameProtocol n e₂ := by
  unfold Event.sameStructure Event.sameProtocol at *
  -- e₁.struct = e₂.struct
  -- Need to show e₁.protocol = e₂.protocol
  cases e₁ with
  | cacheEvent ce₁ =>
    cases e₂ with
    | cacheEvent ce₂ =>
      -- Both are cache events
      -- struct equality means ce₁.cid = ce₂.cid
      simp [Event.struct] at hsame
      -- protocol is derived from cid
      simp [Event.protocol, hsame]
    | directoryEvent de₂ =>
      -- e₁ is cache, e₂ is directory - impossible with same struct
      simp [Event.struct] at hsame
  | directoryEvent de₁ =>
    cases e₂ with
    | cacheEvent ce₂ =>
      -- e₁ is directory, e₂ is cache - impossible with same struct
      simp [Event.struct] at hsame
    | directoryEvent de₂ =>
      -- Both are directory events
      simp [Event.struct] at hsame
      simp [Event.protocol, hsame]

/-- Extract protocol equality from dirAccessOfRequest for write request -/
lemma write_cle_protocol_eq_write_protocol {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w) :
  hw_c_and_g_lin.hreq's_dir_access.choose.protocol = e_w.protocol := by
  have hdir_access_w := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
  cases hdir_access_w with
  | encapDir _ hencap_dir =>
    exact hencap_dir.sameProtocol.symm
  | orderBeforeDir hreq_has_perms hexists_pred hpred_accesses_dir hinter_leaves hpred_same_protocol =>
    have h1 : hexists_pred.choose.protocol = hw_c_and_g_lin.hreq's_dir_access.choose.protocol := hpred_accesses_dir.sameProtocol
    have h2 : hexists_pred.choose.protocol = e_w.protocol := by
      unfold Event.sameProtocol at hpred_same_protocol
      exact hpred_same_protocol
    exact h1.symm.trans h2
  | orderAfterDir _ hsucc_encap_dir hsucc_same_protocol =>
    have h1 : hsucc_encap_dir.choose.protocol = hw_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.sameProtocol
    have h2 : hsucc_encap_dir.choose.protocol = e_w.protocol := by
      unfold Event.sameProtocol at hsucc_same_protocol
      exact hsucc_same_protocol
    exact h1.symm.trans h2

/-- Extract protocol equality from dirAccessOfRequest for read request -/
lemma read_cle_protocol_eq_read_protocol {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_r : Event n}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r) :
  hr_c_and_g_lin.hreq's_dir_access.choose.protocol = e_r.protocol := by
  have hdir_access_r := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right
  cases hdir_access_r with
  | encapDir _ hencap_dir =>
    exact hencap_dir.sameProtocol.symm
  | orderBeforeDir hreq_has_perms hexists_pred hpred_accesses_dir hinter_leaves hpred_same_protocol =>
    have h1 : hexists_pred.choose.protocol = hr_c_and_g_lin.hreq's_dir_access.choose.protocol := hpred_accesses_dir.sameProtocol
    have h2 : hexists_pred.choose.protocol = e_r.protocol := by
      unfold Event.sameProtocol at hpred_same_protocol
      exact hpred_same_protocol
    exact h1.symm.trans h2
  | orderAfterDir _ hsucc_encap_dir hsucc_same_protocol =>
    have h1 : hsucc_encap_dir.choose.protocol = hr_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.sameProtocol
    have h2 : hsucc_encap_dir.choose.protocol = e_r.protocol := by
      unfold Event.sameProtocol at hsucc_same_protocol
      exact hsucc_same_protocol
    exact h1.symm.trans h2

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
  . -- TODO [AZ]; Fill in this case where e_interis in a different protocol than e_w.
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

/-- When CLEs are different but in same GLE, events are in same cluster -/
lemma diff_cle_same_gle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  : e_w.protocol = e_r.protocol := by
  -- Both linearize to the same global directory event
  -- This means they're both in the same cluster protocol since the global directories
  -- handle requests from specific cluster protocols
  -- The cluster requests get forwarded to global directory which tracks which cluster they're from
  sorry

-- Helper lemma: true is not ≤ false for Bool
private lemma bool_true_not_le_false : ¬(true ≤ false) := by decide

-- Helper lemma: a state with c=true cannot be < a state with c=false
private lemma state_true_not_lt_false {p₁ p₂ : Permissions} : ¬(State.mk p₁ true < State.mk p₂ false) := by
  intro h
  show False
  have : true ≤ false := h.right.left
  exact bool_true_not_le_false this

-- Helper lemma: a state with c=true cannot be ≤ a state with c=false
private lemma state_true_not_le_false {p₁ p₂ : Permissions} : ¬(State.mk p₁ true ≤ State.mk p₂ false) := by
  intro h
  show False
  cases h with
  | inl hlt => exact state_true_not_lt_false hlt
  | inr heq =>
    injection heq with _ hc
    exact Bool.noConfusion hc

-- Helper lemma: I is not ≥ Vc (I < Vc but not I ≥ Vc)
private lemma I_not_ge_Vc : ¬(Vc ≤ I) := by
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
private lemma I_not_ge_Vd : ¬(Vd ≤ I) := by
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
private lemma permission_wr_not_le_r : ¬((some ReadWritePermissions.wr : Permissions) ≤ (some ReadWritePermissions.r : Permissions)) := by
  decide

-- Helper: read permission not ≤ none
private lemma permission_r_not_le_none : ¬((some ReadWritePermissions.r : Permissions) ≤ (none : Permissions)) := by
  decide

-- Helper: write permission not ≤ none
private lemma permission_wr_not_le_none : ¬((some ReadWritePermissions.wr : Permissions) ≤ (none : Permissions)) := by
  decide

-- Helper lemma: MRS for coherent requests always has c=true
private lemma coherent_mrs_has_true_coherence (vr : ValidRequest) (hcoh : vr.val.coherent = true) :
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
private lemma coherent_sc_evict_downgrade_to_i (vr : ValidRequest)
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
private lemma coherent_sc_write_downgrade_sw_to_i
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
private lemma nc_request_coherent_perms_contradiction
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
private lemma coherent_rel_acq_weak_write_downgrade_to_false (vr : ValidRequest)
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
private lemma coherent_evict_downgrade_contradiction

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
  . case intro.intro.encapDir hreq_missing_perms hencap_dir =>
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
  . case intro.intro.orderBeforeDir hreq_has_perms hexists_pred_getting_perms
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
  . case intro.intro.orderAfterDir hweak_read_on_vd hsucc_encap_dir hsucc_same_protocol hnot_down =>
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


/- ========== START CMCM.RF case lemmas ========== -/

lemma CMCM.rf.sameGle.sameCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hsame_cle : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  {hr_not_ob_w : ¬ e_r.OrderedBefore n e_w}
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- Prove RF case for same GLE and same CLE
  apply Behaviour.readsFrom.cases.wEqRGle hsame_gle (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) (hw_not_down := hw_not_down) (r_not_down := hr_not_down)

  apply Behaviour.readsFrom.wEqRGle.cases.wEqRCle hsame_cle

  -- Show `e_w` and `e_r` must be in the same protocol/cluster
  -- because they have the same GLE and CLE.
  . case hwr_same_cluster =>
    apply same_cle_implies_same_protocol hw_c_and_g_lin hr_c_and_g_lin hsame_cle
  . case hwr_com =>
    constructor
    . case sameCache =>
      exact same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle
    . case wObR =>
      exact eq_gle_cle_implies_write_before_read (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle hr_not_ob_w
    . case writeRead =>
      apply Event.writeReadPair.mk hw_is_write hw_not_down hr_is_read hr_not_down
    . case noBetween =>
      constructor
      . case noWrite =>
        -- The following cases are considered in `noInterveningWrites_implies_no_writes_between`:
        -- (1) Case analysis on the dirAccessOfRequest of `e_w` and `e_r`
        -- (2) The fact that `hsame_cle` holds rules out many cases of dirAccessOfRequest
        -- (3) `NoInterveningWrites` from the main theorem rules out intervening writes
        -- (4) `hsame_cle` also rules out intervening writes at the CLE level
        have hsame_struct : e_w.struct = e_r.struct := same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle
        exact noInterveningWrites_implies_no_writes_between hw_is_write hr_is_read hsame_struct hw_not_down hr_not_down
          hw_c_and_g_lin hr_c_and_g_lin hsame_cle hknow_dir_access hno_intervening_writes hr_not_ob_w hsucc_w_of_w_after_r
      . case noEvict =>
        -- No coherent evicts can occur between e_w and e_r when they have the same CLE.
        intro e_evict hevict_in_b hbetween_w_r hevict_sw

        -- Case analysis on dirAccessOfRequest of e_w and e_r (3x3 = 9 cases)
        have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
        have hr_dir_access := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right

        -- We already proved e_w.OrderedBefore n e_r in the wObR case
        have hw_ob_r : e_w.OrderedBefore n e_r :=
          eq_gle_cle_implies_write_before_read (hw_cluster := hw_cluster) (hr_cluster := hr_cluster)
            hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle hr_not_ob_w

        -- Since hsame_cle, the directory events are the same
        cases hw_dir_access with
        -- Case 1: e_w encapDir
        | encapDir _ hw_encap =>
          cases hr_dir_access with
          -- Case 1.1: e_w encapDir, e_r encapDir
          | encapDir _ hr_encap =>
            -- Contradiction: if both encapsulate their directory events, then the directory events
            -- must be ordered with respect to e_w and e_r (since e_w OB e_r).
            -- But hsame_cle says they're the same event!
            exfalso
            -- e_w encapsulates e_w_cle and e_r encapsulates e_r_cle
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir
            have hr_encap_cle : e_r.Encapsulates n (hr_c_and_g_lin.hreq's_dir_access.choose) := hr_encap.reqEncapDir

            -- Unfold Encapsulates to get the two inequalities
            simp only [Event.Encapsulates] at hw_encap_cle hr_encap_cle

            -- From hw_encap_cle: e_w.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart and
            --                    (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_w.oEnd
            have hw_encap_1 := hw_encap_cle.1
            have hw_encap_2 := hw_encap_cle.2

            -- From hr_encap_cle: e_r.oStart < (hr_c_and_g_lin.hreq's_dir_access.choose).oStart and
            --                    (hr_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_r.oEnd
            have hr_encap_1 := hr_encap_cle.1
            have hr_encap_2 := hr_encap_cle.2

            -- From hsame_cle, substitute to replace hr_cle with hw_cle where it appears
            rw [← hsame_cle] at hr_encap_1 hr_encap_2

            -- From hw_ob_r (e_w OB e_r): e_w.oEnd < e_r.oStart
            simp only [Event.OrderedBefore] at hw_ob_r

            -- Extract well-formedness constraints
            have hw_cle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed

            -- Now we have all the linear constraints:
            -- hw_encap_1: e_w.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart
            -- hw_encap_2: (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_w.oEnd
            -- hr_encap_1: e_r.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart
            -- hr_encap_2: (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_r.oEnd
            -- hw_ob_r: e_w.oEnd < e_r.oStart
            -- hw_cle_wf: (hw_c_and_g_lin.hreq's_dir_access.choose).oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd

            -- Since omega doesn't see these, let me state the contradiction more explicitly
            -- From hr_encap_1 and hr_encap_2, combined with substitution:
            -- The CLE event (which is the same for both) must satisfy:
            --   e_w.oStart < cle.oStart  [from hw_encap_1]
            --   cle.oEnd < e_w.oEnd      [from hw_encap_2]
            --   e_r.oStart < cle.oStart  [from hr_encap_1]
            --   cle.oEnd < e_r.oEnd      [from hr_encap_2]
            -- And: e_w.oEnd < e_r.oStart [from hw_ob_r]

            -- From hw_ob_r and hr_encap_1: e_w.oEnd < e_r.oStart < cle.oStart
            have step1 : e_w.oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_ob_r hr_encap_1

            -- From step1 and hw_encap_2: e_w.oEnd < cle.oStart and cle.oEnd < e_w.oEnd
            -- So: cle.oEnd < e_w.oEnd < cle.oStart
            have step2 : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_encap_2 step1

            -- But this contradicts hw_cle_wf: cle.oStart < cle.oEnd
            exact Nat.lt_asymm step2 hw_cle_wf
          -- Case 1.2: e_w encapDir, e_r orderBeforeDir
          | orderBeforeDir hreq_r_has_perms hexists_pred_r hpred_r_accesses_dir hinter_leaves_r hpred_r_same_protocol =>
            exfalso
            -- Both e_w and e_r's predecessor encapsulate the same CLE
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir
            have hpred_encap_cle : hexists_pred_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hpred_encap_cle' := hpred_r_accesses_dir.reqEncapDir
              simpa [hsame_cle] using hpred_encap_cle'

            -- Since both events are at the same cache entry and both encapsulate the same CLE,
            -- they must correspond to the same request event (by the uniqueness of dirEventOfReqEvent).
            -- Therefore: hexists_pred_r.choose = e_w
            have hpred_eq_ew : hexists_pred_r.choose = e_w := by
              have hw_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n e_w :=
                hw_encap.dirOfReq
              have hpred_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hexists_pred_r.choose := by
                convert hpred_r_accesses_dir.dirOfReq using 2
              exact (dir_event_of_req_event_unique hw_dir_of_req hpred_dir_of_req).symm

            -- Now substitute: hexists_pred_r.choose := e_w
            rw [hpred_eq_ew] at hinter_leaves_r

            -- After the fix, we have a direct contradiction:
            -- hreq_r_has_perms says: e_r was made on a state with coherent required permissions
            -- hinter_leaves_r says: all events between e_w (pred) and e_r leave state >= e_r.req.MRS
            --
            -- The contradiction: if all intermediates maintain the required permissions,
            -- and the state at e_r already has those permissions (from hreq_r_has_perms),
            -- then e_r doesn't need orderBeforeDir (its predecessor) to get permissions.
            -- But we're in the orderBeforeDir case, which contradicts this.
            --
            -- More formally:
            -- - hreq_r_has_perms encodes: state_before_e_r >= e_r.req.MRS (and coherent)
            -- - hinter_leaves_r on all intermediate events: state preserved as >= e_r.req.MRS
            -- - Therefore: e_r has no need for a predecessor to grant permissions
            -- - But orderBeforeDir requires such a predecessor
            -- - Contradiction!
            have hevict_perms := hinter_leaves_r e_evict hevict_in_b hbetween_w_r.interBetween
            have hevict_perms_after := hevict_perms.hinter_leaves_state_at_least

            -- The contradiction:
            -- hevict_perms_after says: state after evict >= e_r.req.MRS
            -- hreq_r_has_perms says: state before e_r is coherent with required perms
            --
            -- But a coherent downgrade (evict) MUST drop permissions.
            -- So we cannot have both:
            --   (1) state after evict >= required
            --   (2) state before e_r with required
            -- if an evict in between reduces permissions
            --
            -- This contradicts the orderBeforeDir assumption that e_r gets perms from predecessor
            -- (which we proved is e_w), because e_w already had them (via encapsulation).

            -- From hreq_r_has_perms (after unfolding), state before e_r has the perms
            -- From hevict_perms_after, state after evict maintains perms >= required
            -- But a coherent downgrade (evict) MUST drop permissions.
            -- This creates a contradiction.

            -- Extract what we need: e_evict must be a cache event from hbetween_w_r
            have hevict_is_cache : e_evict.isCacheEvent := hbetween_w_r.isCache
            have hevict_is_coherent : e_evict.isCoherent := by
              simp [Event.isEvictSW, Event.isCacheEvent] at hevict_sw hevict_is_cache
              cases hevict_is_cache_case : e_evict with
              | cacheEvent ce =>
                simp [hevict_is_cache_case, Event.isEvictSW] at hevict_sw
                simp [Event.isCoherent, hevict_is_cache_case]
                exact hevict_sw.coherentWrite.left
              | directoryEvent de =>
                simp [Event.isCacheEvent, hevict_is_cache_case] at hevict_is_cache

            -- Apply the helper lemma to derive False
            exact coherent_evict_downgrade_contradiction
              (cmp := cmp)
              hr_cluster
              hr_is_read
              hreq_r_has_perms
              hbetween_w_r.coherentRead
              hevict_sw
              hevict_in_b
              hevict_is_coherent
              hevict_is_cache
              hevict_perms_after
          -- Case 1.3: e_w encapDir, e_r orderAfterDir
          | orderAfterDir hreq_r_on_vd hsucc_encap_dir_r hsucc_same_protocol_r =>
            exfalso
            -- e_w encapsulates the CLE
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir

            -- e_r's successor encapsulates the same CLE (after substitution with hsame_cle)
            have hsucc_encap_cle : hsucc_encap_dir_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap_cle' := hsucc_encap_dir_r.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap_cle'

            -- e_r is ordered before its successor
            have hsucc_spec := hsucc_encap_dir_r.choose_spec.right
            simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
            have hr_ob_succ : e_r.OrderedBefore n hsucc_encap_dir_r.choose := by
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ

            -- From e_w < e_r and e_r < e_succ, we have e_w < e_succ
            have hw_ob_succ : e_w.OrderedBefore n hsucc_encap_dir_r.choose :=
              Event.ordered_trans (n := n) hw_ob_r hr_ob_succ

            -- Unfold encapsulation constraints
            simp only [Event.Encapsulates] at hw_encap_cle hsucc_encap_cle
            have hw_encap_2 := hw_encap_cle.2
            have hsucc_encap_1 := hsucc_encap_cle.1

            -- e_w.oEnd < e_succ.oStart < cle.oStart
            have h1 : e_w.oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_ob_succ hsucc_encap_1

            -- cle.oEnd < e_w.oEnd < cle.oStart
            have h2 : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_encap_2 h1

            -- But cle is well-formed: oStart < oEnd
            have hw_cle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
            exact Nat.lt_asymm h2 hw_cle_wf
        -- Case 2: e_w orderBeforeDir
        | orderBeforeDir _ _ _ _ =>
          cases hr_dir_access with
          -- Case 2.1: e_w orderBeforeDir, e_r encapDir
          | encapDir _ _ =>
            sorry
          -- Case 2.2: e_w orderBeforeDir, e_r orderBeforeDir
          | orderBeforeDir _ _ _ _ =>
            sorry
          -- Case 2.3: e_w orderBeforeDir, e_r orderAfterDir
          | orderAfterDir _ _ _ =>
            sorry
        -- Case 3: e_w orderAfterDir
        | orderAfterDir _ _ _ =>
          cases hr_dir_access with
          -- Case 3.1: e_w orderAfterDir, e_r encapDir
          | encapDir _ _ =>
            sorry
          -- Case 3.2: e_w orderAfterDir, e_r orderBeforeDir
          | orderBeforeDir _ _ _ _ =>
            sorry
          -- Case 3.3: e_w orderAfterDir, e_r orderAfterDir
          | orderAfterDir _ _ _ =>
            sorry

lemma CMCM.rf.sameGle.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.sameCluster.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_down : ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

/- ========== END CMCM.RF case lemmas ========== -/


theorem CMCM.rf_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  /- Synchronization conditions -/
  (hgle_cle_rf_constraints : CompoundProtocol.gleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- probably want to start with cases of `e_w` and `e_r`'s GLEs.
  -- Only expand cases of `e_w` and `e_r`'s requests (coherent, non-coherent, release, acquire...) further into the subcases.

  let e_w_gle := hw_c_and_g_lin.hreq's_global_lin.choose
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose


  let test := hw_c_and_g_lin.hreq's_global_lin.choose_spec.right.isDirEvent

  cases hgle_cle_rf_constraints
  . case sameGle hsame_gle hcle_cases =>
    cases hcle_cases
    . case wEqRCle hsame_cle =>
      apply CMCM.rf.sameGle.sameCle hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) (hw_not_down := hw_not_down) (hr_not_down := hr_not_down) (hr_not_ob_w := hr_not_ob_w) hknow_dir_access hno_intervening_writes hsucc_w_of_w_after_r
    . case otherCases hsame_as_gle_ob_cases =>
      cases hsame_as_gle_ob_cases
      . case wImmPredRCle hw_imm_pred_r_cle =>
        apply CMCM.rf.sameGle.wImmPredRCle hw_c_and_g_lin hr_c_and_g_lin
        . case hsame_gle => exact hsame_gle
        . case hw_imm_pred_r_cle => exact hw_imm_pred_r_cle
      . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
        apply CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster hw_c_and_g_lin hr_c_and_g_lin
        . case hsame_gle => exact hsame_gle
        . case hevict_or_read_between_w_r_cle => exact hevict_or_read_between_w_r_cle
  . case wImmPredRGle hw_imm_pred_r_gle hcle_cases =>
      cases hcle_cases
      . case sameCluster hsame_cluster hsame_cluster_cases =>
        -- NOTE: potential to reuse some of the same cluster case lemmas
        -- from the same GLE & CLE case
        cases hsame_cluster_cases
        . case wImmPredRCle hw_imm_pred_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.wImmPredRCle hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hw_imm_pred_r_cle => exact hw_imm_pred_r_cle
        . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hevict_or_read_between_w_r_cle => exact hevict_or_read_between_w_r_cle
      . case diffCluster hdiff_cluster hdiff_cluster_cases =>
        cases hdiff_cluster_cases
        . case wCleImmPredDown hw_cle_imm_pred_r_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_r_down => exact hw_cle_imm_pred_r_down
        . case evictOrReadBetweenWAndRDown hw_cle_imm_pred_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_down => exact hw_cle_imm_pred_down
