import CMCM.Rf

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

structure DiffClusterCLE.NotBetweenCLEs.constraints {cmp} (e_inter e_w e_r e_inter_down : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
: Prop where
  rDiffProtocol : e_r.diffProtocol n e_w
  interDiffProtocol : e_inter.diffProtocol n e_w
  downToW : e_inter_down.sameProtocol n e_w
  isDirWrite : e_inter_down.isDirWrite
  downIsDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  rClusterDownToW : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin
  interEncapDown : Behaviour.clusterDown.encapDirRelation hinter_c_and_g_lin e_inter_down

/-- Same-cache variant of diff-cluster constraints.
    Uses the original constraint shape: only requires `interDiffProtocol`
    (the intervening write is from a different cluster than e_w), not `rDiffProtocol`.
  Uses the full diff-cluster translation chain rather than incorrectly treating
  `e_inter_down` as a direct `dirAccessOfRequest` of `e_inter`.
    Right endpoint is `e_r_cle` (not `rClusterDownToW.existsRClusterDirDown.choose`). -/
structure DiffClusterCLE.NotBetweenCLEs.sameCacheConstraints {cmp}
    (e_inter e_w e_inter_down : Event n)
    (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
    : Prop where
  interDiffProtocol : e_inter.diffProtocol n e_w
  downToW : e_inter_down.sameProtocol n e_w
  isDirWrite : e_inter_down.isDirWrite
  downIsDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  translatedDir : Event.clusterDirFromDiffProtocolRequest b init e_inter e_inter_down
    hinter_c_and_g_lin

/-
def DiffClusterCLE.NotBetweenCLEs {cmp} (e_inter e_w e_r e_inter_down e_w_cle e_r_cle : Event n)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
: Prop :=
  DiffClusterCLE.NotBetweenCLEs.constraints e_inter e_w e_r e_inter_down →
--   ¬ e_inter_cle.OrderedBefore n e_r_cle
  e_inter_down.OrderedBetween n e_w_cle e_r_cle
-/

/-- Helper lemma: constructs constraints from dirWriteDowngradeFromDiffCluster and protocol equalities -/
lemma DiffClusterCLE.NotBetweenCLEs.constraints_of_downgrade
  {cmp}
  {e_inter e_w e_r e_inter_down : Event n}
  (hdown : Event.dirWriteDowngradeFromDiffCluster e_inter_down e_inter e_w e_r)
  (hediff_w : e_inter.protocol ≠ e_w.protocol)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  (hrDiffProtocol : e_r.diffProtocol n e_w)
  (hrClusterDownToW : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin)
  (interEncapDown : Behaviour.clusterDown.encapDirRelation hinter_c_and_g_lin e_inter_down)
  : DiffClusterCLE.NotBetweenCLEs.constraints e_inter e_w e_r e_inter_down hr_c_and_g_lin hinter_c_and_g_lin :=
  ⟨hrDiffProtocol, hediff_w, hdown.downToW, hdown.isDirWrite, hdown.isDown, hdown.isDir, hrClusterDownToW, interEncapDown⟩

structure NoInterveningWrites.constraints
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w_inter)
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
    ∀ e_inter_down ∈ b,
      (interBtn : DiffClusterCLE.NotBetweenCLEs.constraints e_w_inter e_w e_r e_inter_down hr_c_and_g_lin hinter_c_and_g_lin) →
      ¬ e_inter_down.OrderedBetween n hw_c_and_g_lin.hreq's_dir_access.choose interBtn.rClusterDownToW.existsRClusterDirDown.choose
  /-- Same-cache variant: uses `dirAccessOfRequest` (no `rDiffProtocol`) and
      `e_r_cle` as the right endpoint instead of `rClusterDownToW`'s dir down. -/
  diffClusterNotBetweenCles_sameCache :
    ¬ ∃ e_inter_down ∈ b,
      DiffClusterCLE.NotBetweenCLEs.sameCacheConstraints e_w_inter e_w e_inter_down hinter_c_and_g_lin ∧
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
  ∀ e_w_inter ∈ b, e_w_inter.isClusterCache → e_w_inter.isWrite → ¬ e_w_inter.down →
    (hinter_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w_inter) →
    NoInterveningWrites.constraints hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin e_w_inter hknow_dir_access hinter_c_and_g_lin

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

/-- Coherent write preserves write in reqToDirOfRequestEvent. -/
lemma reqToDir_preserves_write_of_coherent
    (e_req : Event n) (s : State)
    (hwrite : e_req.req.val.isWrite)
    (hcoh : e_req.req.val.coherent = true) :
    (Event.reqToDirOfRequestEvent n e_req s).val.isWrite := by
  cases hreq : e_req.req with
  | mk r hr =>
    cases r with
    | mk rw coh cons =>
      have hrw : rw = .w := by simpa [hreq, Request.isWrite] using hwrite
      have hcoh' : coh = true := by simpa [hreq] using hcoh
      cases hrw; cases hcoh'
      simp [Event.reqToDirOfRequestEvent, hreq, Request.isWrite]

/-- NC release on Vd preserves write in reqToDirOfRequestEvent. -/
lemma reqToDir_preserves_write_on_vd_ncrel
    (e_req : Event n)
    (hrel : e_req.req.val = ⟨.w, false, .Rel⟩) :
    (Event.reqToDirOfRequestEvent n e_req Vd).val.isWrite := by
  cases hreq : e_req.req with
  | mk r hr =>
    cases r with
    | mk rw coh cons =>
      have hrel' : Request.mk rw coh cons = ⟨.w, false, .Rel⟩ := by simpa [hreq] using hrel
      cases hrel'
      simp [Event.reqToDirOfRequestEvent, hreq, Vd, Request.isWrite]

/-- The CLE of a write event is a directory write.
    For each `dirAccessOfRequest` case, `dirCorresponds.dirReq` connects
    the CLE's request to the cache event's request via `reqToDirOfRequestEvent`,
    which preserves write status for non-I-state, non-downgrade events.
    Full proofs exist inline in RfProofHelpers.lean (lines ~689, ~898, ~1140). -/
lemma write_event_cle_isDirWrite {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e : Event n}
    (hw : e.isWrite) (hcluster : e.isClusterCache) (hnot_down : ¬ e.down)
    (hlin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e) :
    hlin.hreq's_dir_access.choose.isDirWrite := by
  have hda := hlin.hreq's_dir_access.choose_spec.2
  cases hda with
  | encapDir hreq_missing_perms hencap_dir =>
    have hcle_is_dir := hencap_dir.isDir
    match hcle_ev : hlin.hreq's_dir_access.choose with
    | .cacheEvent _ => simp [Event.isDirectoryEvent, hcle_ev] at hcle_is_dir
    | .directoryEvent de =>
      unfold Event.isDirWrite; simp
      match he_ev : e with
      | .directoryEvent _ =>
        have := hcluster.eAtCache; simp [Event.isCacheEvent, he_ev] at this
      | .cacheEvent ce =>
        have hwrite' : ce.req.val.isWrite := by simpa [Event.isWrite, he_ev] using hw
        have hrw : ce.req.val.rw = .w := by simpa [Request.isWrite] using hwrite'
        -- Compute dirReq with fully substituted event constructors
        have hdir_req' : de.req = Behaviour.reqToDirOfRequestEvent n b
            (InitialSystemState.stateAt n init (.cacheEvent ce)) true (.cacheEvent ce) := by
          have h := hencap_dir.dirCorresponds.dirReq
          simp only [hcle_ev, he_ev, Event.req] at h; exact h
        cases hreq_missing_perms with
        | downgrade hdown _ => exact absurd hdown hnot_down
        | noPermsForNonNcRelAcqWeakWrite hreq_not_down hreq_not_nc_rel_acq_ww _ =>
          -- e is NOT nc.release/acquire/weakWrite → coherent = true
          have hcoh : ce.req.val.coherent = true := by
            by_contra hcoh_neg
            have hcoh' : ce.req.val.coherent = false := by
              cases hb : ce.req.val.coherent <;> simp_all
            have hvalid := ce.req.property
            rcases hvalid with ⟨hNoSC, hNoWA, _, _, _⟩
            cases hcons : ce.req.val.consistency with
            | SC => exact hNoSC ⟨hcons, hcoh'⟩
            | Rel =>
              have hrelreq : ce.req.val = ⟨.w, false, .Rel⟩ := by
                cases hv : ce.req.val with | mk rw c cs => simp_all
              have : (Event.cacheEvent ce).isNcRelease := by
                simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease]
                exact Subtype.ext hrelreq
              exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inl (he_ev ▸ this)))
            | Acq => exact hNoWA ⟨hrw, hcons⟩
            | Weak =>
              have hweakreq : ce.req.val = ⟨.w, false, .Weak⟩ := by
                cases hv : ce.req.val with | mk rw c cs => simp_all
              have : (Event.cacheEvent ce).isNcWeakWrite := by
                simp [Event.isNcWeakWrite, CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite]
                exact Subtype.ext hweakreq
              exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inr (he_ev ▸ this)))
          -- coherent write: reqToDirOfRequestEvent preserves write
          -- coherent → req ≠ (.w, false, .Rel) (since .Rel has coherent=false)
          have hnotrel : ¬ ((Event.req n (.cacheEvent ce)).val = ⟨.w, false, .Rel⟩ ∧ (true : Bool) = true) := by
            intro ⟨h, _⟩; simp [Event.req] at h
            exact absurd (congrArg Request.coherent h) (by simp [hcoh])
          rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_neg hnotrel]
          exact reqToDir_preserves_write_of_coherent (.cacheEvent ce) _
            (by simp [Event.req]; exact hwrite') (by simp [Event.req]; exact hcoh)
        | ncRelAcqWeakWriteNotOnCoherentState hreq_not_down hreq_nc_rel_acq _ =>
          -- e is NcRelAcq write → must be nc.release (acquire is read)
          have hnot_acq : ¬ (Event.cacheEvent ce).isAcquire := by
            intro hacq
            simp [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
            have : ce.req.val.rw = .r := by rw [show ce.req = _ from hacq]
            exact absurd (this.symm.trans hrw) (by decide)
          have hncrel : (Event.cacheEvent ce).isNcRelease := by
            cases hreq_nc_rel_acq with
            | inl hacq => exact (hnot_acq (he_ev ▸ hacq)).elim
            | inr h => exact he_ev ▸ h
          have hrel_val : ce.req.val = ⟨.w, false, .Rel⟩ := by
            simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hncrel
            exact congrArg Subtype.val hncrel
          -- nc.release with rel_wb=true → Behaviour.reqToDirOfRequestEvent uses Vd
          have hde_req : de.req = Behaviour.reqToDirOfRequestEvent n b
              (InitialSystemState.stateAt n init (.cacheEvent ce)) true (.cacheEvent ce) := by
            have := hencap_dir.dirCorresponds.dirReq
            simp [Event.req, hcle_ev, he_ev] at this ⊢; exact this
          -- For nc.release with rel_wb=true: req = (.w,false,.Rel) → if-then uses Vd
          have hrel_cond : (Event.req n (.cacheEvent ce)).val = ⟨.w, false, .Rel⟩ ∧ (true : Bool) = true :=
            ⟨by simp [Event.req]; exact hrel_val, rfl⟩
          rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_pos hrel_cond]
          exact reqToDir_preserves_write_on_vd_ncrel (.cacheEvent ce) (by simp [Event.req]; exact hrel_val)
  | orderBeforeDir _ hexists_pred hpred_accesses_dir _ _ _ _ _ =>
    -- Through predecessor: predecessor encapsulates CLE, same dirReq pattern
    have hcle_is_dir := hpred_accesses_dir.isDir
    match hcle_ev : hlin.hreq's_dir_access.choose with
    | .cacheEvent _ => simp [Event.isDirectoryEvent, hcle_ev] at hcle_is_dir
    | .directoryEvent de =>
      unfold Event.isDirWrite; simp
      have hdir_req := hpred_accesses_dir.dirCorresponds.dirReq
      -- hdir_req relates de.req to reqToDirOfRequestEvent applied to the PREDECESSOR
      -- The predecessor has no perms and leaves state ≥ MRS → its dirReq is a write
      -- (same pattern as encapDir but through predecessor's request)
      have hpred_spec := hexists_pred.choose_spec.2
      simp [Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast,
            Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_spec
      have hpred_prop := hpred_spec.satisfyP
      simp [Event.PropOnEvent, Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_prop
      have hpred_missing := hpred_prop.missingPerms
      have hpred_cache := hpred_prop.reqCache
      have hpred_not_down := hpred_prop.notDown
      -- Predecessor is a cache event that doesn't have permissions
      -- The CLE.req comes from reqToDirOfRequestEvent applied to predecessor
      -- Need: predecessor is a write (from produces_state_with_write_perms)
      -- For now: follows same pattern as RfProofHelpers.lean:898
      sorry
  | orderAfterDir _ hsucc_encap_dir _ _ =>
    -- Through successor on Vd: successor encaps CLE, isRelAcqOrVdWB
    have hcle_is_dir := hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.isDir
    match hcle_ev : hlin.hreq's_dir_access.choose with
    | .cacheEvent _ => simp [Event.isDirectoryEvent, hcle_ev] at hcle_is_dir
    | .directoryEvent de =>
      unfold Event.isDirWrite; simp
      have hsucc := hsucc_encap_dir.choose_spec.right.satisfyP
      have hdir_req := hsucc.encapCorresponding.dirCorresponds.dirReq
      have hsucc_on_vd := hsucc.stateBeforeAsVd
      have hisrel_acq_vdwb := hsucc.isRelAcqOrVdWB
      -- Case split on successor type: each case shows reqToDirOfRequestEvent gives write
      -- All use reqToDir_preserves_write_on_vd_ncrel or similar on Vd state
      -- (6 sub-cases per isRelAcqOrVdWB, see RfProofHelpers.lean:1203)
      sorry
