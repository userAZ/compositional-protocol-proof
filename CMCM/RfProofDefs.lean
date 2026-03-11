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
    Uses `e_inter.Encapsulates` directly instead of `clusterDown.encapDirRelation`.
    Right endpoint is `e_r_cle` (not `rClusterDownToW.existsRClusterDirDown.choose`). -/
structure DiffClusterCLE.NotBetweenCLEs.sameCacheConstraints
    (e_inter e_w e_inter_down : Event n) : Prop where
  interDiffProtocol : e_inter.diffProtocol n e_w
  downToW : e_inter_down.sameProtocol n e_w
  isDirWrite : e_inter_down.isDirWrite
  downIsDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  interEncapDown : e_inter.Encapsulates n e_inter_down

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
  /-- Same-cache variant: uses simpler constraints (no `rDiffProtocol`) and
      `e_r_cle` as the right endpoint instead of `rClusterDownToW`'s dir down. -/
  diffClusterNotBetweenCles_sameCache :
    ¬ ∃ e_inter_down ∈ b,
      DiffClusterCLE.NotBetweenCLEs.sameCacheConstraints e_w_inter e_w e_inter_down ∧
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
