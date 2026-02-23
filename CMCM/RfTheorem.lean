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
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Prop where
  interWrite : e_w_inter.isWrite
--   notDown : ¬ e_w_inter.down
  clusterW : e_w_inter.isClusterCache
  notSameAsW : e_w_inter ≠ e_w
  notBetweenGles :
    NotBetweenGLEs
      (hknow_dir_access cmp b init e_w_inter clusterW).hreq's_global_lin.choose
      hw_c_and_g_lin.hreq's_global_lin.choose
      hr_c_and_g_lin.hreq's_global_lin.choose
  notBetweenCles :
    SameClusterCLE.NotBetweenCLEs
      (hknow_dir_access cmp b init e_w_inter clusterW).hreq's_dir_access.choose
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
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
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
  {e_w : Event n} {hw_cluster : e_w.isClusterCache}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster) :
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
  {e_r : Event n} {hr_cluster : e_r.isClusterCache}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster) :
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
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite_cluster : e_inter.isClusterCache)
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter hwrite_cluster)
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
              simpa [hinter_ev] using hwrite_cluster.dirAtDir
            simp [Event.isCacheEvent, hinter_ev] at this
          | .cacheEvent ce_inter =>
            -- Now hwrite : ce_inter.req.val.isWrite, i.e., ce_inter.req.val.rw = .w
            have hwrite' : ce_inter.req.val.isWrite := by
              simpa [Event.isWrite, hinter_ev] using hwrite
            -- From dirEventOfReqEvent, de_inter_cle.eReq = ce_inter
            unfold Event.dirEventOfReqEvent at hdir_matches_req
            simp [hinter_cle_ev, hinter_ev] at hdir_matches_req
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
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
--   {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite_cluster : e_inter.isClusterCache)
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter hwrite_cluster)
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
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  {he_inter : e_inter ∈ b}
  (hwrite_cluster : e_inter.isClusterCache)
  (hwrite : e_inter.isWrite)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access)
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter hwrite_cluster)
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
      (he_inter := he_inter) hwrite_cluster hwrite hcontra hinter_lin hsame_cache hsame_protocol

/-- If no writes are between GLEs and GLEs are equal, then no writes are between the original events -/
lemma noInterveningWrites_implies_no_writes_between
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (_hw_is_write : e_w.isWrite) (_r_is_read : e_r.isRead)
  (_hsame_struct : e_w.struct = e_r.struct)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (_hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  (_hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (_hno_intervening : NoInterveningWrites _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin _hknow_dir_access)
  (_hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (_hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Event.Between.noWrite b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose := by
  intro e he hwrite_cluster hwrite

  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose

  have hcontra := _hno_intervening e he hwrite_cluster hwrite
  have hinter_lin := _hknow_dir_access cmp b init e hwrite_cluster

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
        have hr_end_before_e_end : e_r.oEnd < e.oEnd := _hsucc_w_of_w_after_r e he ⟨hsame_protocol, hsame_cache, hw_ob_e⟩
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

/-- When CLEs are equal, the events must be in the same protocol/cluster -/
lemma same_cle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hcle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  : e_w.protocol = e_r.protocol := by
  -- Directory events are protocol-specific
  -- Both events access the same directory event, which belongs to a specific protocol
  -- From cacheEncapsulatesCorrespondingDirEvent, we have sameProtocol : e_req.protocol = e_dir.protocol
  -- Therefore both e_w and e_r must be in the same protocol as the shared directory event
  -- This requires: axiom that directory events uniquely determine protocol membership
  sorry

/-- When CLEs are equal, the events must be at the same cache -/
lemma same_cle_implies_same_struct
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
--   {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
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
  -- Helper: if a directory event corresponds to two request events, they are equal.
  have hreq_eq_of_dir :
      ∀ {e_dir e_req1 e_req2 : Event n},
        e_dir.dirEventOfReqEvent n e_req1 →
        e_dir.dirEventOfReqEvent n e_req2 →
        e_req1 = e_req2 := by
    intro e_dir e_req1 e_req2 hreq1 hreq2
    cases e_dir <;> cases e_req1 <;> cases e_req2 <;>
      simp[Event.dirEventOfReqEvent] at hreq1 hreq2
    · -- directoryEvent / cacheEvent / cacheEvent
      have hce1 := hreq1.correspondingCE
      have hce2 := hreq2.correspondingCE
      have hce : _ := hce1.symm.trans hce2
      simp[hce]
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
      have hreq_eq := hreq_eq_of_dir hw_encap.dirOfReq hr_encap.dirOfReq
      simp[hreq_eq]
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := hreq_eq_of_dir hw_encap.dirOfReq hr_pred_access.dirOfReq
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
      have hreq_eq := hreq_eq_of_dir hw_encap.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
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
      have hreq_eq := hreq_eq_of_dir hw_pred_access.dirOfReq hr_encap.dirOfReq
      have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have hw_struct' : e_w.struct = e_r.struct := by
        have hw_struct' : e_w.struct = hw_pred.choose.struct := hw_struct.symm
        have hw_struct'' : e_w.struct = e_r.struct := by
          simpa[hreq_eq] using hw_struct'
        exact hw_struct''
      exact hw_struct'
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := hreq_eq_of_dir hw_pred_access.dirOfReq hr_pred_access.dirOfReq
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
      have hreq_eq := hreq_eq_of_dir hw_pred_access.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
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
      have hreq_eq := hreq_eq_of_dir hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_encap.dirOfReq
      have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
      have hw_struct := hsame_struct_of_entry hw_entry
      have : e_w.struct = e_r.struct := by
        have hw' : e_w.struct = hw_succ.choose.struct := hw_struct
        have hw'' : e_w.struct = e_r.struct := by
          simpa[hreq_eq] using hw'
        exact hw''
      exact this
    | orderBeforeDir _ hr_pred hr_pred_access _ =>
      have hreq_eq := hreq_eq_of_dir hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_pred_access.dirOfReq
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
      have hreq_eq := hreq_eq_of_dir hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
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
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
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
    have : e_w.isCacheEvent := hw_cluster.dirAtDir
    simp[Event.isCacheEvent, hw_ev] at this
  | cacheEvent ce_w =>
    cases hr_ev : e_r with
    | directoryEvent de_r =>
      have : e_r.isCacheEvent := hr_cluster.dirAtDir
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

/-- When GLEs are equal but CLEs different, write's CLE must be before read's CLE -/
lemma eq_gle_neq_cle_implies_cle_ordered
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening : NoInterveningWrites hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hcle_neq : hw_c_and_g_lin.hreq's_dir_access.choose ≠ hr_c_and_g_lin.hreq's_dir_access.choose)
  (heq_gle_impl_ob_eq_cle :
    hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose →
    hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose := by
  -- If GLEs are equal but CLEs are different, the CLEs still can't be equal
  -- and by protocol structure, must be ordered with write before read
  -- The key is that within a single GLE context, multiple CLE accesses must be temporally ordered
  -- Since e_w is a write and e_r is a read accessing the same GLE,
  -- the write's CLE access precedes the read's CLE access
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
  -- By the structure of directory accesses, each CLE is an event in b
  have hw_cle_in_b := hw_c_and_g_lin.hreq's_dir_access.choose_spec.left
  have hr_cle_in_b := hr_c_and_g_lin.hreq's_dir_access.choose_spec.left

  -- Both are directory events corresponding to the linearization points
  -- Within the same global linearization, if the CLEs are different,
  -- they must be ordered by the directory ordering invariants
  -- The write's CLE must be ordered before the read's CLE by coherence requirements

  -- Apply heq_gle_impl_ob_cle from the main theorem context to conclude
  exact heq_gle_impl_ob_cle hgle_eq

/-- When CLEs are different but in same GLE, events are in same cluster -/
lemma diff_cle_same_gle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  : e_w.protocol = e_r.protocol := by
  -- Both linearize to the same global directory event
  -- This means they're both in the same cluster protocol since the global directories
  -- handle requests from specific cluster protocols
  -- The cluster requests get forwarded to global directory which tracks which cluster they're from
  sorry

/-- Prove WriteRead.wObRCle.case given the constraints -/
lemma prove_wObRCle_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)

  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening : NoInterveningWrites hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b,  e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin := by
  by_cases hsame_struct : e_w.struct = e_r.struct
  · -- Same cache case: prove no directory writes between
    have hno_dir_write : Event.Between.noDirWrite b e_w e_r := fun e he hbetween hdir_write => by
      -- e is a directory write between e_w and e_r
      -- We need to show this leads to a contradiction
      cases he_match : e with
      | cacheEvent ce =>
        -- e is a cache event, but hdir_write says it's a directory write - contradiction
        simp [Event.isDirWrite, he_match] at hdir_write
      | directoryEvent de =>
        -- e is a directory event between two cache events at the same cache
        -- Key architectural constraint: every directory event corresponds to a cache event (Axiom 6.5)
        -- If there's a directory write e between e_w and e_r at the same cache,
        -- it must correspond to some cache write operation
        -- That cache write would violate the hno_intervening constraints
        -- which prevent writes between e_w and e_r's linearization events
        have hw_cache : e_w.isCacheEvent := hw_cluster.dirAtDir
        have hr_cache : e_r.isCacheEvent := hr_cluster.dirAtDir
        have he_dir : e.isDirectoryEvent := by simp [Event.isDirectoryEvent, he_match]
        -- Prove that e has different struct from e_w and e_r
        have he_diff_w_struct : ¬e.sameStructure n e_w := by
          simp [Event.sameStructure, Event.struct, he_match]
          cases e_w with
          | cacheEvent ce_w => simp
          | directoryEvent de_w =>
            -- e_w is directory, but hw_cache says it's cache - contradiction
            simp [Event.isCacheEvent] at hw_cache
        -- The formal proof requires showing that the cache event corresponding to this
        -- directory write (guaranteed by Axiom 6.5: axDirectoryEventHasRequest)
        -- would be an intervening write blocked by hno_intervening
        sorry
    exact WriteRead.wObRCle.case.sameCache hsame_struct hno_dir_write
  · exact WriteRead.wObRCle.case.diffCache hsame_struct (by sorry)

/-- When write's GLE is before read's GLE, write's CLE is before read's CLE -/
lemma gle_ordered_implies_cle_ordered
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hgle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose := by
  -- GLEs encapsulate CLEs in the compound protocol model
  -- If global directory events are ordered, the cluster directory events they handle must also be ordered
  -- This follows from the encapsulation property: CLE is encapsulated by its corresponding GLE
  sorry

/-- When GLEs are ordered, events must be in same protocol -/
lemma gle_ordered_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  (hgle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
  : e_w.protocol = e_r.protocol := by
  -- When GLEs are ordered (not equal), they're still part of the same global ordering
  -- which means they're from the same cluster protocol being coordinated by the global protocol
  -- The global directory manages one cluster protocol's requests
  sorry

theorem CMCM.rf_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster)
  -- Synchronization conditions.
  (hgle_eq_or_ob : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose ∨
    hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
--   (heq_gle_impl_ob_cle :
--     hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose →
--     hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose ∨
--     hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
  (hr_ob_w_cle_not_allowed : ¬ (hr_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hw_c_and_g_lin.hreq's_dir_access.choose))
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- probably want to start with cases of `e_w` and `e_r`'s GLEs.
  -- Only expand cases of `e_w` and `e_r`'s requests (coherent, non-coherent, release, acquire...) further into the subcases.

  let e_w_gle := hw_c_and_g_lin.hreq's_global_lin.choose
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose

  -- First, determine the relationship between the GLEs
  by_cases hw_r_gle_eq : e_w_gle = e_r_gle
  · -- Case 1: GLEs are equal
    apply Behaviour.readsFrom.cases.wEqRGle hw_r_gle_eq
    -- Now need to determine relationship between CLEs
    by_cases hw_r_cle_eq : e_w_cle = e_r_cle
    · -- Case 1a: Both GLE and CLE are equal
      apply Behaviour.readsFrom.wEqRGle.cases.wEqRCle hw_r_cle_eq
      -- Need same cluster and no writes/evicts between
      -- First goal: e_w.protocol = e_r.protocol
      · exact same_cle_implies_same_protocol hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hw_r_cle_eq
      -- Second goal: WriteRead.EqGleCle.case b e_w e_r

      -- Proving the "base case"
      · constructor
        · -- Prove: e_w.struct = e_r.struct (same cache)
          exact same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hw_r_cle_eq
        · -- Prove: e_w.OrderedBefore n e_r
          exact eq_gle_cle_implies_write_before_read hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hw_r_gle_eq hw_r_cle_eq hr_not_ob_w
        · -- Prove: Event.Between.noWriteOrEvict b e_w e_r
          constructor
          · -- No writes between
            exact noInterveningWrites_implies_no_writes_between hw_is_write hr_is_read (same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hw_r_cle_eq) hw_c_and_g_lin hr_c_and_g_lin hw_r_cle_eq hknow_dir_access hno_intervening_writes hr_not_ob_w hsucc_w_of_w_after_r
        --   · -- No evicts between
        --     exact noCoherentEvictsBetweenSameCle hw_c_and_g_lin hr_c_and_g_lin hw_r_cle_eq
    · -- Case 1b: GLE equal, but CLE different (write's CLE before read's CLE)
      by_cases hw_ob_r_cle : e_w_cle.OrderedBefore n e_r_cle
      case pos =>
        apply Behaviour.readsFrom.wEqRGle.cases.wObRCle
        -- Need to prove WriteRead.wObR.GleOrCle.cases
        constructor
        · -- Prove: e_w_cle.OrderedBefore n e_r_cle
          exact hw_ob_r_cle
        · -- Prove: e_w.protocol = e_r.protocol
          exact diff_cle_same_gle_implies_same_protocol hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hw_r_gle_eq
        · -- Prove: WriteRead.wObRCle.case
          exact prove_wObRCle_case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access hno_intervening_writes hr_not_ob_w hsucc_w_of_w_after_r
      case neg =>
        exfalso
        apply hr_ob_w_cle_not_allowed
        -- Since directory events are totally ordered and write's CLE is NOT before read's CLE,
        -- read's CLE must be before write's CLE
        have hw_cle_dir : e_w_cle.isDirectoryEvent := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
        have hr_cle_dir : e_r_cle.isDirectoryEvent := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
        match hw_ev : e_w_cle, hr_ev : e_r_cle with
        | .directoryEvent de_w_cle, .directoryEvent de_r_cle =>
          have hcle_ordered := b.orderedAtEntry.dir_ordered de_w_cle de_r_cle |>.ordered
          simp [DirectoryEvent.Ordered] at hcle_ordered
          cases hcle_ordered with
          | inl hw_cle_ob_r => exact absurd hw_cle_ob_r hw_ob_r_cle
          | inr hr_cle_ob_w =>
            -- Convert DirectoryEvent.OrderedBefore to Event.OrderedBefore
            -- The goal is Event.OrderedBefore n e_r_cle e_w_cle
            change Event.OrderedBefore n e_r_cle e_w_cle
            rw [hr_ev, hw_ev]
            -- Both OrderedBefore definitions use oEnd < oStart, so they match
            exact hr_cle_ob_w
        | .cacheEvent _, _ => simp [Event.isDirectoryEvent] at hw_cle_dir
        | _, .cacheEvent _ => simp [Event.isDirectoryEvent] at hr_cle_dir
  · -- Case 2: GLEs are not equal
    -- Check if write's GLE is ordered before read's GLE
    by_cases hw_ob_r : e_w_gle.OrderedBefore n e_r_gle
    · -- Case 2a: Write's GLE is ordered before read's GLE
      apply Behaviour.readsFrom.cases.wObRGle hw_ob_r
      -- Need to prove WriteRead.wObR.GleOrCle.cases
      constructor
      · -- Prove: e_w_cle.OrderedBefore n e_r_cle
        exact gle_ordered_implies_cle_ordered hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hw_ob_r
      · -- Prove: e_w.protocol = e_r.protocol
        exact gle_ordered_implies_same_protocol hw_c_and_g_lin hr_c_and_g_lin hw_ob_r
      · -- Prove: WriteRead.wObRCle.case
        exact prove_wObRCle_case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access hno_intervening_writes hr_not_ob_w hsucc_w_of_w_after_r
    · -- Case 2b: Read's GLE is ordered before write's GLE (contradiction from assumption)
      -- We have hgle_eq_or_ob which says either GLEs are equal or write's GLE is before read's GLE
      -- Since hw_r_gle_eq is false and hw_ob_r is false, we have a contradiction
      cases hgle_eq_or_ob with
      | inl heq => exact absurd heq hw_r_gle_eq
      | inr hob => exact absurd hob hw_ob_r
