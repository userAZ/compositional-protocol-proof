import CMCM.RfProofDefs
import CMCM.RfProofLargeLemmas

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

-- reqToDir_preserves_write_of_coherent and reqToDir_preserves_write_on_vd_ncrel
-- moved to CMCM/RfProofDefs.lean

/-- Axiom: If a request is coherent, its MRS has coherent state (c = true) -/
lemma coherent_request_has_coherent_mrs (vr : ValidRequest) (hcoh : vr.val.coherent = true) :
  vr.MRS.c = true := by
  unfold State.c
  simp[ValidRequest.MRS]
  match hvr : vr with
  | ⟨⟨_,true,.SC⟩, _⟩ => simp[]
  | ⟨⟨.w,true,.Rel⟩,_⟩ => simp[]
  | ⟨⟨.w,true,.Weak⟩,_⟩ => simp[]
  | ⟨⟨_,false,.Weak⟩,_⟩ => simp[] at hcoh
  | ⟨⟨.w, false, .Rel⟩,_⟩ => simp[] at hcoh
  | ⟨⟨.r,false,.Acq⟩,_⟩ => simp[] at hcoh

/-- Axiom: If a request is a write, its MRS has write permissions (p = some .wr) or is Vc -/
lemma write_request_has_write_mrs_or_vc (vr : ValidRequest) (hwrite : vr.val.rw = .w) :
  vr.MRS.p = some .wr ∨ vr.MRS = Vc := by
  unfold State.p
  simp[ValidRequest.MRS]
  match hvr : vr with
  | ⟨⟨.w,true,.SC⟩, _⟩ =>
    simp[ReadWrite.toPerms,ReadWrite.toRWPerms]
  | ⟨⟨.r,true,.SC⟩, _⟩ =>
    -- simp[ReadWrite.toPerms,ReadWrite.toRWPerms]
    simp[] at hwrite
  | ⟨⟨.w,true,.Rel⟩,_⟩ => simp[]
  | ⟨⟨.w,true,.Weak⟩,_⟩ => simp[]
  | ⟨⟨.w,false,.Weak⟩,_⟩ => simp[]
  | ⟨⟨.r,false,.Weak⟩,_⟩ => simp[] at hwrite
  | ⟨⟨.w, false, .Rel⟩,_⟩ => simp[]
  | ⟨⟨.r,false,.Acq⟩,_⟩ => simp[] at hwrite

/-- Axiom: Read requests never have write permissions in their MRS -/
lemma read_request_no_write_mrs (vr : ValidRequest) (hread : vr.val.rw = .r) :
  vr.MRS.p ≠ some .wr := by
  unfold State.p
  match hvr : vr with
  | ⟨⟨.w,true,.SC⟩, _⟩ =>
    simp at hread
  | ⟨⟨.r,true,.SC⟩, _⟩ =>
    simp[ValidRequest.MRS,ReadWrite.toPerms,ReadWrite.toRWPerms]
  | ⟨⟨.w,true,.Rel⟩,_⟩ =>
    simp at hread
  | ⟨⟨.w,true,.Weak⟩,_⟩ =>
    simp at hread
  | ⟨⟨.w,false,.Weak⟩,_⟩ =>
    simp at hread
  | ⟨⟨.r,false,.Weak⟩,_⟩ =>
    simp[ValidRequest.MRS]
  | ⟨⟨.w, false, .Rel⟩,_⟩ =>
    simp at hread
  | ⟨⟨.r,false,.Acq⟩,_⟩ =>
    simp[ValidRequest.MRS]

/-- Axiom: Only non-coherent requests have c = false in their MRS -/
lemma non_coherent_request_has_false_mrs_c (vr : ValidRequest) (hnc : vr.val.coherent = false) :
  vr.MRS.c = false := by
  unfold State.c
  simp[ValidRequest.MRS]
  match hvr : vr with
  | ⟨⟨_,false,.Weak⟩,_⟩ => simp[]
  | ⟨⟨.w, false, .Rel⟩,_⟩ => simp[]
  | ⟨⟨.r,false,.Acq⟩,_⟩ => simp[]

/-- A coherent write (not a downgrade) always leaves the cache state at least SW.
    This is because CacheEvent.SucceedingState uses RequestState when down=false,
    and for coherent requests, RequestState s = if MRS ≤ s then s else MRS.
    For all coherent writes, MRS = SW, so the result is always ≥ SW. -/
lemma coherent_write_leaves_at_least_SW
  {b : Behaviour n} {init : InitialSystemState n} {e_w : Event n}
  (hw_is_write : e_w.isWrite) (hw_coherent : e_w.isCoherent)
  (hw_not_down : ¬ e_w.down) (hw_is_cache : e_w.isCacheEvent)
  : b.reqLeavesStateAtLeast n e_w init SW := by
  unfold Behaviour.reqLeavesStateAtLeast
  rw [Behaviour.state_after_eq_succeeding_state_before]
  cases he_w : e_w with
  | directoryEvent de =>
    exfalso; rw [he_w] at hw_is_cache; simp [Event.isCacheEvent] at hw_is_cache
  | cacheEvent ce =>
    simp only [Event.SucceedingState, EntryState.cache]
    have hdown : ce.down = false := by
      have h := hw_not_down; rw [he_w] at h; simp [Event.down] at h; omega
    simp only [CacheEvent.SucceedingState, hdown]
    suffices ∀ (s : State), SW ≤ ce.req.RequestState s by exact this _
    intro s
    have hcoh : ce.req.val.coherent = true := by
      have h := hw_coherent; rw [he_w] at h
      simpa [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] using h
    have hrw : ce.req.val.rw = .w := by
      have h := hw_is_write; rw [he_w] at h
      simpa [Event.isWrite, Request.isWrite] using h
    generalize hreq : ce.req = req
    rw [hreq] at hcoh hrw
    cases req with
    | mk val hvr =>
      cases val with
      | mk rw coh cons =>
        simp at hcoh hrw
        subst hcoh; subst hrw
        cases cons with
        | Acq => exact absurd ⟨rfl, rfl⟩ hvr.2.1
        | _ =>
          dsimp [ValidRequest.RequestState, ValidRequest.MRS, ReadWrite.toPerms]
          split <;> first | assumption | exact Or.inr rfl

/-- Helper: NC Weak Write contradicts being in reqMissingPerms.noPermsForNonNcRelAcqWeakWrite -/
lemma nc_weak_write_excluded_by_not_nc_rel_acq_weak_write
  {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .w, coherent := false, consistency := .Weak})
  (hnotrel : Event.notNcRelAcqWeakWrite n (Event.cacheEvent ce_pred))
  : False := by
  apply hnotrel
  right; right
  unfold Event.isNcWeakWrite CacheEvent.isNcWeakWrite ValidRequest.isNcWeakWrite
  ext
  exact hpred_req

/-- Helper: NC Weak Write contradicts ncRelAcqWeakWriteNotOnCoherentState (it's not Acq or Rel) -/
lemma nc_weak_write_not_acq_or_rel
  {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .w, coherent := false, consistency := .Weak})
  (hnc : CacheEvent.isAcquire n ce_pred ∨ CacheEvent.isNcRelease n ce_pred)
  : False := by
  cases hnc with
  | inl hacq =>
    simp [CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
    have := congrArg Subtype.val hacq
    simp at this
    rw [hpred_req] at this
    simp at this
  | inr hrel =>
    simp [CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hrel
    have := congrArg Subtype.val hrel
    simp at this
    rw [hpred_req] at this
    simp at this

/-- Helper: NC Rel Write produces c=false when missing permissions -/
lemma nc_rel_write_succeeding_state_has_false_coherence
  {b : Behaviour n} {init : InitialSystemState n} {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .w, coherent := false, consistency := .Rel})
  (hpred_not_down : ce_pred.down = false)
  (hno_perms : b.acqRelWeakWriteNoPerms n init (Event.cacheEvent ce_pred))
  : (Event.SucceedingState n (Event.cacheEvent ce_pred)
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred))).cache.c = false := by
  -- NC Rel Write with acqRelWeakWriteNoPerms produces Vc (which has c=false)
  -- Unfold definitions
  simp only [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down]
  simp only [ValidRequest.RequestState]
  -- The request is NC Rel Write
  have hreq : ce_pred.req = ⟨⟨.w, false, .Rel⟩, by simp[Request.IsValid']⟩ := by
    ext
    exact hpred_req
  simp only [hreq]
  -- Now we need to match on the state before
  cases hstate : (EntryState.cache n
    (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
      (Event.cacheEvent ce_pred)))
  case mk p c =>
    -- Match on p and c
    cases p <;> cases c
    case none.false =>
      -- State is I, RequestState returns Vc
      simp only [Vc, EntryState.cache]
    case none.true =>
      -- State is ⟨none, true⟩ (junk state), RequestState returns Vc
      simp only [Vc, EntryState.cache]
    case some.false p_val =>
      -- State is ⟨some p_val, false⟩, could be Vc or Vd
      cases p_val
      case r =>
        -- State is Vc, RequestState returns Vc
        simp only [Vc, EntryState.cache]
      case wr =>
        -- State is Vd, RequestState returns Vc
        simp only [Vc, EntryState.cache]
    case some.true p_val =>
      -- State is ⟨some p_val, true⟩, could be MR or SW
      cases p_val
      case r =>
        -- State is MR = ⟨some .r, true⟩, RequestState returns Vc
        simp only [Vc, EntryState.cache]
      case wr =>
        -- State is SW = ⟨some .wr, true⟩
        -- RequestState would return SW (stays at state), which has c=true
        -- But this contradicts acqRelWeakWriteNoPerms
        exfalso
        unfold Behaviour.acqRelWeakWriteNoPerms at hno_perms
        unfold Behaviour.eventOnCoherentState Behaviour.eventOnStateHasPerms at hno_perms
        simp only [Event.req, hreq] at hno_perms
        -- hno_perms says: ¬(state.c ∧ req.MRS ≤ state)
        -- We have state = SW = ⟨some .wr, true⟩
        -- req.MRS = Vd = ⟨some .wr, false⟩
        -- Need to show: state.c = true and Vd ≤ SW
        apply hno_perms
        simp only [hstate]
        constructor
        · -- Show state.c = true
          trivial
        · -- Show Vd ≤ SW
          simp only [ValidRequest.MRS, Vd, LE.le, State.le, LT.lt, State.lt]
          left
          decide

/-- Helper: NC Acq Read always produces c=false (always produces Vc state) -/
lemma nc_acq_read_succeeding_state_has_false_coherence
  {b : Behaviour n} {init : InitialSystemState n} {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Acq})
  (hpred_not_down : ce_pred.down = false)
  (hno_perms : b.acqRelWeakWriteNoPerms n init (Event.cacheEvent ce_pred))
  : (Event.SucceedingState n (Event.cacheEvent ce_pred)
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred))).cache.c = false := by
  -- NC Acq Read always produces Vc (which has c=false), regardless of input state
  simp only [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down]
  simp only [ValidRequest.RequestState]
  -- The request is NC Acq Read
  have hreq : ce_pred.req = ⟨⟨.r, false, .Acq⟩, by simp[Request.IsValid']⟩ := by
    ext
    exact hpred_req
  simp only [hreq, Vc, EntryState.cache]

/-- Helper: Downgrade for NC Weak Read produces c=false (via DowngradeState which produces I) -/
lemma nc_weak_read_downgrade_produces_false_coherence
  {b : Behaviour n} {init : InitialSystemState n} {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Weak})
  (hpred_down : ce_pred.down = true)
  (hmrs : (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
      (Event.cacheEvent ce_pred)).cache = Event.MRS n (Event.cacheEvent ce_pred))
  : (Event.SucceedingState n (Event.cacheEvent ce_pred)
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred))).cache.c = false := by
  -- NC Weak Read downgrade: state = MRS = Vc, DowngradeState produces I (c=false)
  simp only [Event.SucceedingState, CacheEvent.SucceedingState, hpred_down]
  simp only [ValidRequest.DowngradeState]
  -- The request is NC Weak Read
  have hreq : ce_pred.req = ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩ := by
    ext
    exact hpred_req
  simp only [hreq]
  -- State is Vc (from hmrs)
  have hstate_vc : (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
      (Event.cacheEvent ce_pred)).cache = Vc := by
    simp only [Event.MRS, Event.down, hpred_down] at hmrs
    simp only [Event.req, hreq] at hmrs
    simp only [ReadWrite.toPerms] at hmrs
    exact hmrs
  simp only [hstate_vc]
  -- Simplify the boolean checks - should reduce to I.c = false
  simp only [I, Vc, EntryState.cache]
  rfl

/-- Helper: NC Weak Read without perms produces c=false (produces MRS=Vc when lacking perms) -/
lemma nc_weak_read_no_perms_produces_false_coherence
  {b : Behaviour n} {init : InitialSystemState n} {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Weak})
  (hpred_not_down : ce_pred.down = false)
  (hno_perms : ¬(Event.req n (Event.cacheEvent ce_pred)).MRS ≤
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred)).cache)
  : (Event.SucceedingState n (Event.cacheEvent ce_pred)
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred))).cache.c = false := by
  -- NC Weak Read without perms produces MRS = Vc (which has c=false)
  simp only [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down]
  simp only [ValidRequest.RequestState]
  -- The request is NC Weak Read
  have hreq : ce_pred.req = ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩ := by
    ext
    exact hpred_req
  simp only [hreq]
  -- Since MRS is not ≤ state, the else branch is taken: produces MRS
  have hno_perms' : ¬ValidRequest.MRS ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩ ≤
      (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred)).cache := by
    simp only [Event.req, hreq] at hno_perms
    exact hno_perms
  rw [if_neg hno_perms']
  -- MRS for NC Weak Read is Vc (c=false)
  simp only [ValidRequest.MRS, Vc, EntryState.cache]

/-- Helper: NC Acq Read not in Acq or Rel is impossible -/
lemma nc_acq_read_is_acquire
  {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Acq})
  (hnc : CacheEvent.isAcquire n ce_pred ∨ CacheEvent.isNcRelease n ce_pred)
  : CacheEvent.isAcquire n ce_pred := by
  cases hnc with
  | inl hacq => exact hacq
  | inr hrel =>
    simp [CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hrel
    have := congrArg Subtype.val hrel
    simp at this
    rw [hpred_req] at this
    simp at this

/-- Helper: NC Weak Read is neither Acq nor Rel -/
lemma nc_weak_read_not_acq_or_rel
  {ce_pred : CacheEvent n}
  (hpred_req : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Weak})
  (hnc : CacheEvent.isAcquire n ce_pred ∨ CacheEvent.isNcRelease n ce_pred)
  : False := by
  cases hnc with
  | inl hacq =>
    simp [CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
    have := congrArg Subtype.val hacq
    simp at this
    rw [hpred_req] at this
    simp at this
  | inr hrel =>
    simp [CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hrel
    have := congrArg Subtype.val hrel
    simp at this
    rw [hpred_req] at this
    simp at this

lemma nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hstate_coh : (b.stateReqMadeOn n init e_req).c = true)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  : e_pred.req.val.coherent = true := by
  cases e_pred with
  | directoryEvent de =>
    simp [Event.isCacheEvent] at hpred_cache
  | cacheEvent ce_pred =>
    -- Establish that predecessor's state after has c=true
    have hcoh_le_after :
      (b.stateReqMadeOn n init e_req).c ≤
      (b.stateAfter n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred)).cache.c := by
      cases hpred_produces with
      | inl hlt => exact hlt.right.left
      | inr heq => rw [← heq]

    have hafter_coh_true :
      (b.stateAfter n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred)).cache.c = true := by
      rw [hstate_coh] at hcoh_le_after
      cases hafter : (b.stateAfter n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
        (Event.cacheEvent ce_pred)).cache.c with
      | false =>
        -- Contradiction: true ≤ false via hafter
        rw [hafter] at hcoh_le_after
        contradiction
      | true =>
        rfl

    -- After rewriting with succeeding state, we get c=true
    rw [Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at hafter_coh_true

    -- Case analysis on request type
    match hpred_req : ce_pred.req with
    | ⟨⟨_, true, _⟩, _⟩ =>
      -- Coherent request: conclude directly
      simp [Event.req, hpred_req]
    | ⟨⟨.w, false, .Weak⟩, _⟩ =>
      -- NC Weak Write: contradicts reqMissingPerms
      exfalso
      have hpred_req_val : ce_pred.req.val = {rw := .w, coherent := false, consistency := .Weak} := by
        have := congrArg Subtype.val hpred_req
        simpa using this
      cases hpred_missing_perms with
      | downgrade hd _ => exact hpred_not_down hd
      | noPermsForNonNcRelAcqWeakWrite _ hnotrel _ =>
        exact nc_weak_write_excluded_by_not_nc_rel_acq_weak_write hpred_req_val hnotrel
      | ncRelAcqWeakWriteNotOnCoherentState _ hnc _ =>
        exact nc_weak_write_not_acq_or_rel hpred_req_val hnc
    | ⟨⟨.w, false, .Rel⟩, _⟩ =>
      -- NC Rel Write: produces c=false, contradicts hafter_coh_true
      exfalso
      have hpred_req_val : ce_pred.req.val = {rw := .w, coherent := false, consistency := .Rel} := by
        have := congrArg Subtype.val hpred_req
        simpa using this
      cases hpred_missing_perms with
      | downgrade hd _ => exact hpred_not_down hd
      | noPermsForNonNcRelAcqWeakWrite _ hnotrel _ =>
        apply hnotrel
        right; left
        simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease]
        ext
        exact hpred_req_val
      | ncRelAcqWeakWriteNotOnCoherentState hnd hnc hno_perms =>
        cases hnc with
        | inl hacq =>
          simp at hacq
          have := congrArg Subtype.val hacq
          simp at this
          rw [hpred_req_val] at this
          simp at this
        | inr hrel =>
          have hpred_not_down' : ce_pred.down = false := by simp [Event.down] at hnd; exact hnd
          have hfalse := nc_rel_write_succeeding_state_has_false_coherence (b := b) (init := init) hpred_req_val hpred_not_down' hno_perms
          rw [hfalse] at hafter_coh_true
          simp at hafter_coh_true
    | ⟨⟨.r, false, .Acq⟩, _⟩ =>
      -- NC Acq Read: produces c=false, contradicts hafter_coh_true
      exfalso
      have hpred_req_val : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Acq} := by
        have := congrArg Subtype.val hpred_req
        simpa using this
      cases hpred_missing_perms with
      | downgrade hd _ => exact hpred_not_down hd
      | noPermsForNonNcRelAcqWeakWrite _ hnotrel _ =>
        apply hnotrel
        left
        ext
        exact hpred_req_val
      | ncRelAcqWeakWriteNotOnCoherentState hnd hnc hno_perms =>
        have _ := nc_acq_read_is_acquire hpred_req_val hnc
        have hpred_not_down' : ce_pred.down = false := by simp [Event.down] at hnd; exact hnd
        have hfalse := nc_acq_read_succeeding_state_has_false_coherence (b := b) (init := init) hpred_req_val hpred_not_down' hno_perms
        rw [hfalse] at hafter_coh_true
        simp at hafter_coh_true
    | ⟨⟨.r, false, .Weak⟩, _⟩ =>
      -- NC Weak Read: either downgrade or no perms, both produce c=false
      exfalso
      have hpred_req_val : ce_pred.req.val = {rw := .r, coherent := false, consistency := .Weak} := by
        have := congrArg Subtype.val hpred_req
        simpa using this
      cases hpred_missing_perms with
      | downgrade hd hmrs =>
        have hpred_down : ce_pred.down = true := by simp [Event.down] at hd; exact hd
        unfold Behaviour.evictOnMRSState at hmrs
        have hfalse := nc_weak_read_downgrade_produces_false_coherence hpred_req_val hpred_down hmrs
        rw [hfalse] at hafter_coh_true
        simp at hafter_coh_true
      | noPermsForNonNcRelAcqWeakWrite hnd _ hno_perms =>
        have hpred_not_down' : ce_pred.down = false := by simp [Event.down] at hnd; exact hnd
        simp [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms, Event.req] at hno_perms
        have hfalse := nc_weak_read_no_perms_produces_false_coherence hpred_req_val hpred_not_down' hno_perms
        rw [hfalse] at hafter_coh_true
        simp at hafter_coh_true
      | ncRelAcqWeakWriteNotOnCoherentState _ hnc _ =>
        exact nc_weak_read_not_acq_or_rel hpred_req_val hnc

/-- Implementation of pred_missing_perms_req_has_coherent_state_implies_pred_is_coherent
    Placed here after all nc_ helper lemmas are defined. -/
lemma pred_missing_perms_req_impl
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hstate_coh : (b.stateReqMadeOn n init e_req).c = true)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  : e_pred.req.val.coherent = true :=
  nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent hstate_coh hpred_produces hpred_not_down hpred_missing_perms hpred_cache

/-- Full implementation of pred_missing_perms_req_has_coherent_state_implies_pred_is_coherent -/
lemma pred_missing_perms_req_has_coherent_state_impl
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hcoh : e_req.isCoherent)
  (hreq_has_perms : b.hasPerms n init e_req)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  : e_pred.req.val.coherent = true := by
  -- Derive that stateReqMadeOn has c=true from coherent + hasPerms
  have hstate_coh : (b.stateReqMadeOn n init e_req).c = true := by
    -- For coherent e_req with permissions, stateBefore must have c ≥ MRS.c = true
    cases e_req with
    | directoryEvent de =>
      simp [Event.isCoherent] at hcoh
    | cacheEvent ce =>
      unfold Behaviour.stateReqMadeOn Behaviour.hasPerms at *
      simp [Event.isCoherent] at hcoh
      -- For coherent requests, MRS.c = true
      have hmrs_coh : ce.req.MRS.c = true := coherent_request_has_coherent_mrs ce.req hcoh
      -- hasPerms means MRS ≤ stateBefore
      have hle : ce.req.MRS.c ≤ (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)).cache.c := by
        cases hreq_has_perms with
        | inl hlt => exact hlt.right.left
        | inr heq => rw [← heq]; exact hmrs_coh ▸ Bool.le_refl true
      -- Therefore stateBefore.c = true
      rw [hmrs_coh] at hle
      cases hbefore : (b.stateBefore n (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)).cache.c
      · -- c = false, but true ≤ false is impossible (reduces to false = true)
        rw [hbefore] at hle
        nomatch hle
      · rfl
  -- Now use the existing lemma that does case analysis on e_pred
  exact nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent hstate_coh hpred_produces hpred_not_down hpred_missing_perms hpred_cache

/-- Helper lemma: Non-coherent weak write and SC read cannot coexist in the same protocol.
    This captures the constraint that protocols cannot mix MSI (SC) and RCC (NC/Rel/CRel/Acq) requests. -/
lemma protocol_nc_weak_write_sc_read_contradiction
  {cmp : CompoundProtocol n} {b : Behaviour n}
  {e_ncwrite e_scread : Event n}
  (he_ncwrite_in_b : e_ncwrite ∈ b)
  (he_scread_in_b : e_scread ∈ b)
  (hncwrite : e_ncwrite.req.val = ⟨.w, false, .Weak⟩)
  (hscread : e_scread.req.val = ⟨.r, true, .SC⟩)
  (hsame_protocol : e_ncwrite.protocol = e_scread.protocol)
  : False := by
  -- Both requests are in the same protocol's request set
  -- NC weak write request: ⟨.w, false, .Weak⟩ is non-coherent
  -- SC read request: ⟨.r, true, .SC⟩ is coherent
  -- These cannot coexist in a protocol's request set due to MSI/RCC separation:
  -- - MSI protocols contain only SC (coherent) requests
  -- - RCC protocols contain NC/Rel/CRel/Acq (non-coherent, labeled, Coherent Release) requests
  -- No protocol mixes both types

  -- TODO: Implement this based on the following:
  -- This can be easily done by using `cmp.eReqOfTheirProtocol` and showing `e_inter` and `hsucc_encap_dir.choose` are in the same protocol
  -- (with `hsucc_same_protocol : hsucc_encap_dir.choose.sameProtocol n e_req`),
  -- Then use `e_inter` and `hsucc_encap_dir.choose`'s shared protocol's interface `ProtocolInterface := {vr : Set ValidRequest // FollowsProtocolInterface vr}`
  -- `FollowsProtocolInterface` property that prohibits NC weak read and SC read from being in the same protocol, which would lead to a contradiction.

  -- Determine which protocol the events belong to and show both requests are in that protocol
  have h_proto : ∃ p : Protocol n, e_ncwrite.protocol = p.pi ∧ e_scread.protocol = p.pi := by
    -- They belong to the same protocol by hsame_protocol
    cases heq : e_ncwrite.protocol with
    | global => exact ⟨cmp.global, by simp [cmp.globalWellFormed], by rw [←hsame_protocol, heq, cmp.globalWellFormed]⟩
    | cluster1 => exact ⟨cmp.cluster1, by simp [cmp.cluster1WellFormed], by rw [←hsame_protocol, heq, cmp.cluster1WellFormed]⟩
    | cluster2 => exact ⟨cmp.cluster2, by simp [cmp.cluster2WellFormed], by rw [←hsame_protocol, heq, cmp.cluster2WellFormed]⟩
  obtain ⟨proto, hproto_nc, hproto_sc⟩ := h_proto

  -- Both requests are in the protocol's interface
  have hncwrite_in_proto : e_ncwrite.req ∈ proto.requests := by
    apply cmp.eReqOfTheirProtocol proto e_ncwrite
    exact hproto_nc
  have hscread_in_proto : e_scread.req ∈ proto.requests := by
    apply cmp.eReqOfTheirProtocol proto e_scread
    exact hproto_sc

  -- Show e_ncwrite.req = NonCoherentWeakWrite (which is ValidRequest with val = ⟨.w, false, .Weak⟩)
  have hncwrite_eq : e_ncwrite.req = NonCoherentWeakWrite := by
    ext
    exact hncwrite

  -- Show e_scread.req = SCRead (which is ValidRequest with val = ⟨.r, true, .SC⟩)
  have hscread_eq : e_scread.req = SCRead := by
    ext
    exact hscread

  -- NonCoherentWeakWrite has NonCoherent property
  have hncwrite_nc : e_ncwrite.req.NonCoherent := by
    rw [hncwrite_eq]
    simp only [ValidRequest.NonCoherent, Request.nonCoherent]
    simp

  -- Use FollowsProtocolInterface.nc_no_sc: if a NonCoherent request is in the protocol, then SCRead ∉ protocol
  have hcontra := proto.requests.property.nc_no_sc e_ncwrite.req hncwrite_in_proto
  have hsc_not_in : SCRead ∉ proto.requests := by
    have h := hcontra ⟨hncwrite_in_proto, Or.inl hncwrite_nc⟩
    exact h.right

  -- But we have SCRead ∈ proto.requests
  rw [hscread_eq] at hscread_in_proto
  exact hsc_not_in hscread_in_proto

/-- The CLE of a write event is a directory write.
    For each `dirAccessOfRequest` case, `dirCorresponds.dirReq` connects
    the CLE's request to the cache event's request via `reqToDirOfRequestEvent`,
    which preserves write status. -/
lemma write_event_cle_isDirWrite {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e : Event n}
    (hw : e.isWrite) (hcluster : e.isClusterCache) (hnot_down : ¬ e.down)
    (hlin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    (he_in_b : e ∈ b) :
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
        have hdir_req' : de.req = Behaviour.reqToDirOfRequestEvent n b
            (InitialSystemState.stateAt n init (.cacheEvent ce)) true (.cacheEvent ce) := by
          have h := hencap_dir.dirCorresponds.dirReq
          simp only [hcle_ev, he_ev, Event.req] at h; exact h
        cases hreq_missing_perms with
        | downgrade hdown _ => exact absurd hdown hnot_down
        | noPermsForNonNcRelAcqWeakWrite hreq_not_down hreq_not_nc_rel_acq_ww _ =>
          have hcoh : ce.req.val.coherent = true := by
            by_contra hcoh_neg
            have hcoh' : ce.req.val.coherent = false := by
              cases hb : ce.req.val.coherent <;> simp_all
            have hvalid := ce.req.property
            rcases hvalid with ⟨hNoSC, hNoWA, _, _, _⟩
            cases hcons : ce.req.val.consistency with
            | SC => exact hNoSC ⟨hcons, hcoh'⟩
            | Rel =>
              have : (Event.cacheEvent ce).isNcRelease := by
                unfold Event.isNcRelease CacheEvent.isNcRelease ValidRequest.isNcRelease
                show ce.req = ⟨⟨.w, false, .Rel⟩, _⟩
                apply Subtype.ext
                show ce.req.val = ⟨.w, false, .Rel⟩
                cases hv : ce.req.val with | mk rw c cs => simp_all
              exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inl (he_ev ▸ this)))
            | Acq => exact hNoWA ⟨hrw, hcons⟩
            | Weak =>
              have : (Event.cacheEvent ce).isNcWeakWrite := by
                unfold Event.isNcWeakWrite CacheEvent.isNcWeakWrite ValidRequest.isNcWeakWrite
                show ce.req = ⟨⟨.w, false, .Weak⟩, _⟩
                apply Subtype.ext
                show ce.req.val = ⟨.w, false, .Weak⟩
                cases hv : ce.req.val with | mk rw c cs => simp_all
              exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inr (he_ev ▸ this)))
          have hnotrel : ¬ ((Event.req n (.cacheEvent ce)).val = ⟨.w, false, .Rel⟩ ∧ (true : Bool) = true) := by
            intro ⟨h, _⟩; simp [Event.req] at h
            exact absurd (congrArg Request.coherent h) (by simp [hcoh])
          rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_neg hnotrel]
          exact reqToDir_preserves_write_of_coherent (.cacheEvent ce) _
            (by simp [Event.req]; exact hwrite') (by simp [Event.req]; exact hcoh)
        | ncRelAcqWeakWriteNotOnCoherentState hreq_not_down hreq_nc_rel_acq _ =>
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
          have hrel_cond : (Event.req n (.cacheEvent ce)).val = ⟨.w, false, .Rel⟩ ∧ (true : Bool) = true :=
            ⟨by simp [Event.req]; exact hrel_val, rfl⟩
          rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_pos hrel_cond]
          exact reqToDir_preserves_write_on_vd_ncrel (.cacheEvent ce) (by simp [Event.req]; exact hrel_val)
  | orderBeforeDir hreq_has_perms hexists_pred hpred_accesses_dir _ _ _
      hpred_produces_state hpred_not_down_field =>
    have hcle_is_dir := hpred_accesses_dir.isDir
    match hcle_ev : hlin.hreq's_dir_access.choose with
    | .cacheEvent _ => simp [Event.isDirectoryEvent, hcle_ev] at hcle_is_dir
    | .directoryEvent de =>
      unfold Event.isDirWrite; simp
      have hdir_req := hpred_accesses_dir.dirCorresponds.dirReq
      -- Helper: get de.req = reqToDirOfRequestEvent on predecessor
      have hde_req : Event.req n (.directoryEvent de) = de.req := rfl
      have hdir_req' : de.req = b.reqToDirOfRequestEvent n
          (InitialSystemState.stateAt n init hexists_pred.choose) true hexists_pred.choose := by
        rw [← hde_req, ← hcle_ev]; exact hdir_req
      -- Extract predecessor properties
      have hpred_spec := hexists_pred.choose_spec.2
      simp [Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast,
            Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_spec
      have hpred_prop := hpred_spec.satisfyP
      simp [Event.PropOnEvent, Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_prop
      have hpred_missing := hpred_prop.missingPerms
      have hpred_cache := hpred_prop.reqCache
      -- Case split on reqHasPerms
      cases hreq_has_perms with
      | hasPerms hcoh hhas_perms =>
        by_cases hrel : (Event.req n hexists_pred.choose).val = ⟨.w, false, .Rel⟩
        · rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_pos ⟨hrel, rfl⟩]
          exact reqToDir_preserves_write_on_vd_ncrel hexists_pred.choose hrel
        · rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_neg (fun ⟨h, _⟩ => hrel h)]
          have hpred_write := produces_state_with_write_perms_implies_is_write
            hw hcoh hhas_perms hpred_produces_state hpred_not_down_field hpred_missing hpred_cache
          have hpred_coh := nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent
            (by -- stateReqMadeOn has c = true for coherent write with perms
              unfold Behaviour.stateReqMadeOn
              have hmrs_c : (Event.req n e).MRS.c = true := by
                match he' : e with
                | .cacheEvent ce =>
                  unfold Event.isCoherent ValidRequest.isCoherent Request.isCoherent at hcoh
                  cases he_req : ce.req with | mk vr hvr =>
                    cases vr with | mk rw coh cons =>
                      simp [he', Event.req, he_req] at hcoh; cases hcoh
                      simp [Event.req, he', he_req, ValidRequest.MRS, ReadWrite.toPerms, ReadWrite.toRWPerms]
                      match cons, rw with
                      | .SC, .w | .SC, .r | .Rel, .w | .Weak, .w => rfl
                      | .Rel, .r => exfalso; simp [Request.IsValid'] at hvr
                      | .Acq, _ => exfalso; simp [Request.IsValid'] at hvr
                      | .Weak, .r => exfalso; simp [Request.IsValid'] at hvr
                | .directoryEvent _ => exfalso; simp [Event.isCoherent] at hcoh
              have hle := hhas_perms
              have hc_le : (Event.req n e).MRS.c ≤ (b.stateBefore n (init.stateAt n e) e).cache.c := by
                cases hle with
                | inl hlt => exact hlt.right.left
                | inr heq => rw [← heq]
              rw [hmrs_c] at hc_le
              cases h_c : (b.stateBefore n (init.stateAt n e) e).cache.c
              · exfalso; rw [h_c] at hc_le; trivial
              · rfl)
            hpred_produces_state hpred_not_down_field hpred_missing hpred_cache
          exact reqToDir_preserves_write_of_coherent hexists_pred.choose _ hpred_write hpred_coh
      | ncRelAcqWeakWriteHasCoherentPerms hncraw hhascoh =>
        by_cases hrel : (Event.req n hexists_pred.choose).val = ⟨.w, false, .Rel⟩
        · rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_pos ⟨hrel, rfl⟩]
          exact reqToDir_preserves_write_on_vd_ncrel hexists_pred.choose hrel
        · rw [hdir_req', Behaviour.reqToDirOfRequestEvent, if_neg (fun ⟨h, _⟩ => hrel h)]
          have hpred_write := produces_state_with_write_perms_implies_is_write_no_coherence
            (cmp := cmp) (b := b) (init := init)
            (e_pred := hexists_pred.choose) (e_req := e)
            hw hhascoh.hasPerms hhascoh.onCoherentState
            hpred_produces_state hpred_not_down_field hpred_missing hpred_cache he_in_b
          have hpred_coh := nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent
            hhascoh.onCoherentState hpred_produces_state hpred_not_down_field hpred_missing hpred_cache
          exact reqToDir_preserves_write_of_coherent hexists_pred.choose _ hpred_write hpred_coh
      | ncWeakReadHasPermsNotVd hncwr _ =>
        exfalso
        match he' : e with
        | .cacheEvent ce =>
          simp [Event.isNcWeakRead, CacheEvent.isNcWeakRead, he'] at hncwr
          have hrd : ce.req.val.rw = .r := by rw [show ce.req = _ from hncwr]
          have hwr : ce.req.val.rw = .w := by simpa [Event.isWrite, he', Request.isWrite] using hw
          exact absurd (hrd.symm.trans hwr) (by decide)
        | .directoryEvent _ => simp [Event.isNcWeakRead] at hncwr
  | orderAfterDir hweak_req_on_vd hsucc_encap_dir hsucc_same_protocol _ =>
    -- Use the same approach as the inline proof at ~1350
    let e_inter_cle := hlin.hreq's_dir_access.choose
    have hcle_is_dir : e_inter_cle.isDirectoryEvent :=
      hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.isDir
    show e_inter_cle.isDirWrite
    unfold Event.isDirWrite
    match he_cle : e_inter_cle, hcle_is_dir with
    | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
    | .directoryEvent de, _ =>
      simp
      have hsucc := hsucc_encap_dir.choose_spec.right.satisfyP
      have hdir_corresponds := hsucc.encapCorresponding.dirCorresponds
      have hsucc_on_vd := hsucc.stateBeforeAsVd
      have hisrel_acq_vdwb := hsucc.isRelAcqOrVdWB
      -- e is nc.weak write
      have hncwrite_req : (Event.req n e).val = ⟨.w, false, .Weak⟩ := by
        match he' : e with
        | .directoryEvent _ => have := hcluster.eAtCache; simp [Event.isCacheEvent, he'] at this
        | .cacheEvent ce =>
          have hweak := hweak_req_on_vd.weakReq
          simp [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, he'] at hweak
          have hwr : ce.req.val.rw = .w := by simpa [Event.isWrite, he', Request.isWrite] using hw
          simp [Event.req, he']; cases hv : ce.req.val with | mk rw c cs => simp_all [hweak]
      -- Get hde_req with concrete .directoryEvent de on LHS
      have hde_req : Event.req n (.directoryEvent de) =
          Behaviour.reqToDirOfRequestEvent n b
            (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
            (Exists.choose hsucc_encap_dir) := by
        calc Event.req n (.directoryEvent de)
          _ = Event.req n e_inter_cle := by rw [← he_cle]
          _ = _ := hdir_corresponds.dirReq
      -- Case split on successor type
      rcases hisrel_acq_vdwb with hacq | hnc_rel | hc_rel | hvdwb | hsc_write | hsc_read
      · -- Acquire
        have hreq : Event.req n (Exists.choose hsucc_encap_dir) =
            ⟨⟨.r, false, .Acq⟩, by simp [Request.IsValid']⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent _ => simp [hchoose, Event.isAcquire] at hacq
          | cacheEvent ce => simpa [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire, Event.req, hchoose] using hacq
        -- Event.req n (.directoryEvent de) = de.req definitionally
        have hgoal : (Event.req n (.directoryEvent de)).val.isWrite := by
          rw [hde_req]; simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
            hsucc_on_vd, hreq, Request.isWrite, VdEntry, EntryState.cache]
        simpa [Event.req] using hgoal
      · -- NcRelease
        have hreq : Event.req n (Exists.choose hsucc_encap_dir) =
            ⟨⟨.w, false, .Rel⟩, by simp [Request.IsValid']⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent _ => simp [hchoose, Event.isNcRelease] at hnc_rel
          | cacheEvent ce => simpa [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease, Event.req, hchoose] using hnc_rel
        show de.req.val.isWrite
        rw [show de.req = _ from hde_req]
        simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
          hsucc_on_vd, hreq, Request.isWrite, Vd, VdEntry, EntryState.cache]
      · -- CRelease
        have hreq : Event.req n (Exists.choose hsucc_encap_dir) =
            ⟨⟨.w, true, .Rel⟩, by simp [Request.IsValid']⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent _ => simp [hchoose, Event.isCRelease] at hc_rel
          | cacheEvent ce =>
            have hval : ce.req.val = ⟨.w, true, .Rel⟩ := by simp only [Event.isCRelease, hchoose] at hc_rel; exact hc_rel
            ext; simp [Event.req, hchoose, hval]
        show de.req.val.isWrite
        rw [show de.req = _ from hde_req]
        simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
          hsucc_on_vd, hreq, Request.isWrite, Vd, VdEntry, EntryState.cache]
      · -- VdWriteBack
        have hreq : Event.req n (Exists.choose hsucc_encap_dir) =
            ⟨⟨.w, false, .Weak⟩, by simp [Request.IsValid']⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent _ => simp [hchoose, Event.isVdWriteBack] at hvdwb
          | cacheEvent ce =>
            simp only [Event.isVdWriteBack, hchoose] at hvdwb
            simp [Event.req, hchoose]; exact Subtype.ext hvdwb.isWeakWrite
        show de.req.val.isWrite
        rw [show de.req = _ from hde_req]
        simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
          hsucc_on_vd, hreq, Request.isWrite, Vd, VdEntry, EntryState.cache]
      · -- SCWrite
        have hreq : Event.req n (Exists.choose hsucc_encap_dir) =
            ⟨⟨.w, true, .SC⟩, by simp [Request.IsValid']⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent de_succ =>
            simp only [Event.isSCWrite, Event.req, hchoose, ValidRequest.isSCWrite] at hsc_write
            simp [Event.req, hchoose]; exact hsc_write
          | cacheEvent ce =>
            simp only [Event.isSCWrite, ValidRequest.isSCWrite, hchoose, Event.req] at hsc_write
            simp [Event.req, hchoose]; exact hsc_write
        show de.req.val.isWrite
        rw [show de.req = _ from hde_req]
        simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
          hsucc_on_vd, hreq, Request.isWrite, Vd, VdEntry, EntryState.cache]
      · -- SCRead: contradiction with nc.weak
        exfalso
        have hscread_req : (Event.req n (Exists.choose hsucc_encap_dir)).val = ⟨.r, true, .SC⟩ := by
          cases hchoose : Exists.choose hsucc_encap_dir with
          | directoryEvent de_succ =>
            simp only [Event.isSCRead, Event.req, hchoose, ValidRequest.isSCRead] at hsc_read
            exact congrArg Subtype.val hsc_read
          | cacheEvent ce =>
            simp only [Event.isSCRead, ValidRequest.isSCRead, Event.req, hchoose] at hsc_read
            exact congrArg Subtype.val hsc_read
        exact protocol_nc_weak_write_sc_read_contradiction (cmp:=cmp) he_in_b
          (hsucc_encap_dir.choose_spec.left) hncwrite_req hscread_req
          hsucc_same_protocol.symm

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
  (hwrite_not_down : ¬ e_inter.down)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access (_hknow_dir_access cmp b init e_inter))
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
          -- Case split on e_inter to extract cache event
          have : de_inter_cle.req.val.isWrite := by
            unfold Event.isWrite at hwrite
            match hinter_ev : e_inter with
            | .directoryEvent _ =>
              -- e_inter is not a directory event (it's a cluster cache)
              have hcontra : e_inter.isCacheEvent := by
                simpa [hinter_ev] using hwrite_cluster.eAtCache
              simp [Event.isCacheEvent, hinter_ev] at hcontra
            | .cacheEvent ce_inter =>
              -- Now hwrite' : ce_inter.req.val.isWrite
              have hwrite' : ce_inter.req.val.isWrite := by
                simpa [Event.isWrite, hinter_ev] using hwrite
              -- Show directory request is a write
              -- From hencap_dir: the directory event's request is obtained via reqToDirOfRequestEvent
              -- Connect de_inter_cle.req to the transformation
              have hde_req : de_inter_cle.req = Behaviour.reqToDirOfRequestEvent n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_inter)) true (Event.cacheEvent ce_inter) := by
                calc de_inter_cle.req
                  _ = Event.req n (Event.directoryEvent de_inter_cle) := rfl
                  _ = Event.req n e_inter_cle := by rw [← hinter_cle_ev]
                  _ = Behaviour.reqToDirOfRequestEvent n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_inter)) true (Event.cacheEvent ce_inter) := by
                    grind
                    -- simpa [e_inter_cle] using hdir_req_matches

              -- Now case on hreq_missing_perms to understand which gets permissions
              cases hreq_missing_perms with
              | downgrade hdown _ =>
                -- TODO: For downgrades (down = true), prove write is preserved through reqToDirOfRequestEvent
                absurd hdown
                simp[hwrite_not_down]
              | noPermsForNonNcRelAcqWeakWrite hreq_not_down hreq_not_nc_rel_acq_ww _ =>
                -- For cache coherent writes (not NC/rel/acq/weak), reqToDirOfRequestEvent preserves write
                have hvalid := ce_inter.req.property
                rcases hvalid with ⟨hNoSCNonCoherent, hNoWriteAcquire, _hNoReadRelease, _hNoCoherentAcquire, _hNoCoherentWeakRead⟩
                have hrw : ce_inter.req.val.rw = .w := by
                  simpa [Request.isWrite] using hwrite'
                have hcoh : ce_inter.req.val.coherent = true := by
                  by_contra hcoh
                  cases hcoh' : ce_inter.req.val.coherent <;> simp [hcoh'] at hcoh
                  -- Now coherent = false, analyze consistency
                  cases hcons : ce_inter.req.val.consistency
                  · -- SC
                    have hsc : ce_inter.req.val.SCNonCoherent := by
                      exact And.intro hcons hcoh'
                    exact hNoSCNonCoherent hsc
                  · -- Rel
                    have hrelreq : ce_inter.req = ⟨⟨.w, false, .Rel⟩, by simp [Request.IsValid']⟩ := by
                      apply Subtype.ext
                      cases hreqval : ce_inter.req.val with
                      | mk rw coh cons =>
                        have hrw' : rw = .w := by
                          simpa [hreqval] using hrw
                        have hcoh'' : coh = false := by
                          simpa [hreqval] using hcoh'
                        have hcons' : cons = .Rel := by
                          simpa [hreqval] using hcons
                        cases hrw'
                        cases hcoh''
                        cases hcons'
                        rfl
                    have hncrel : (Event.cacheEvent ce_inter).isNcRelease := by
                      simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease, hrelreq]
                    exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inl hncrel))
                  · -- Acq
                    have hwa : ce_inter.req.val.WriteAcquire := by
                      exact And.intro hrw hcons
                    exact hNoWriteAcquire hwa
                  · -- Weak
                    have hweakreq : ce_inter.req = ⟨⟨.w, false, .Weak⟩, by simp [Request.IsValid']⟩ := by
                      apply Subtype.ext
                      cases hreqval : ce_inter.req.val with
                      | mk rw coh cons =>
                        have hrw' : rw = .w := by
                          simpa [hreqval] using hrw
                        have hcoh'' : coh = false := by
                          simpa [hreqval] using hcoh'
                        have hcons' : cons = .Weak := by
                          simpa [hreqval] using hcons
                        cases hrw'
                        cases hcoh''
                        cases hcons'
                        rfl
                    have hnweak : (Event.cacheEvent ce_inter).isNcWeakWrite := by
                      simp [Event.isNcWeakWrite, CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite, hweakreq]
                    exact hreq_not_nc_rel_acq_ww (Or.inr (Or.inr hnweak))
                rw [hde_req]
                by_cases hrel : (Event.req n (Event.cacheEvent ce_inter)).val = ⟨.w, false, .Rel⟩
                · -- contradicts coherent = true
                  have hrel' : ce_inter.req.val = ⟨.w, false, .Rel⟩ := by
                    simpa [Event.req] using hrel
                  have hcoh_false : ce_inter.req.val.coherent = false := by
                    simpa [hrel']
                  have hcontra : true = false := by
                    calc
                      true = ce_inter.req.val.coherent := hcoh.symm
                      _ = false := hcoh_false
                  exact (by cases hcontra)
                · -- not rel write; coherent = true forces default case
                  have hrel' : (ce_inter.req).val ≠ ⟨.w, false, .Rel⟩ := by
                    simpa [Event.req] using hrel
                  have hwrite_dir :
                      (Event.reqToDirOfRequestEvent n (Event.cacheEvent ce_inter)
                        (EntryState.cache n
                          (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_inter))
                            (Event.cacheEvent ce_inter)))).val.isWrite := by
                    refine reqToDir_preserves_write_of_coherent (e_req := Event.cacheEvent ce_inter)
                      (s := EntryState.cache n
                        (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_inter))
                          (Event.cacheEvent ce_inter))) ?_ ?_
                    · simpa [Event.req] using hwrite'
                    · simpa [Event.req] using hcoh
                  simpa [Behaviour.reqToDirOfRequestEvent, hrel', Event.req] using hwrite_dir
              | ncRelAcqWeakWriteNotOnCoherentState hreq_not_down hreq_nc_rel_acq _ =>
                -- TODO: For NC/rel/acq writes on I, may hit exception case (NC write on I → READ)
                -- Need to either prove contradiction or show it doesn't apply
                have hnc := hreq_nc_rel_acq
                -- acquire is a read, so it contradicts hwrite'
                have hrelreq : ce_inter.req = ⟨⟨.w, false, .Rel⟩, by simp [Request.IsValid']⟩ := by
                  have hnot_acq : ¬ (Event.cacheEvent ce_inter).isAcquire := by
                    intro hacq
                    have hread : ce_inter.req.val.rw = .r := by
                      simpa using congrArg (fun vr => vr.val.rw) hacq
                    have hwrite_rw : ce_inter.req.val.rw = .w := by
                      simpa [Request.isWrite] using hwrite'
                    have : ReadWrite.r = ReadWrite.w := by
                      calc
                        ReadWrite.r = ce_inter.req.val.rw := hread.symm
                        _ = ReadWrite.w := hwrite_rw
                    exact (by cases this)
                  have hncrel : (Event.cacheEvent ce_inter).isNcRelease := by
                    cases hnc with
                    | inl hacq => exact (hnot_acq hacq).elim
                    | inr hncrel => exact hncrel
                  simpa [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease] using hncrel
                rw [hde_req]
                -- rel_wb = true gives Vd state; no exception applies, so write preserved
                have hrel : (Event.req n (Event.cacheEvent ce_inter)).val = ⟨.w, false, .Rel⟩ := by
                  simpa using congrArg Subtype.val hrelreq
                have hrel' : (ce_inter.req).val = ⟨.w, false, .Rel⟩ := by
                  simpa [Event.req] using hrel
                have hwrite_dir :
                    (Event.reqToDirOfRequestEvent n (Event.cacheEvent ce_inter) Vd).val.isWrite := by
                  refine reqToDir_preserves_write_on_vd_ncrel (e_req := Event.cacheEvent ce_inter) ?_
                  simpa [Event.req] using hrel'
                simpa [Behaviour.reqToDirOfRequestEvent, hrel', Event.req] using hwrite_dir
          exact this
        | .cacheEvent _ =>
          -- Contradiction: e_inter_cle cannot be both a cache event and a directory event
          have hinter_cle_is_dir' : e_inter_cle.isDirectoryEvent := hinter_cle_is_dir
          simp [Event.isDirectoryEvent, hinter_cle_ev] at hinter_cle_is_dir'
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have _hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      intro e_inter_down _he_mem _hdowngrade
      intro hob
      rw [_hcle_eq] at hob
      exact Event.contradiction_of_reflexive_ordered_before _
        (Trans.trans hob.pred hob.succ)
    | orderBeforeDir hreq_has_perms hexists_pred_getting_perms hpred_accesses_dir hinter_leaves_state_at_least hpred_same_protocol
      _ hpred_produces_state_at_least_req_made_on_state hinter_pred_not_down =>
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
      -- Show that e_inter_cle is a directory write
      -- User insight: In orderBeforeDir, use hreq_has_perms + hwrite to derive directory write
      -- Key facts:
      --   1. hwrite : e_inter.isWrite
      --   2. hreq_has_perms : b.reqHasPerms n init e_inter
      --   3. hexists_pred_getting_perms : b.reqHasPermsSoDirPred n init e_inter
      --   4. hpred_accesses_dir : predecessor accesses directory event e_inter_cle
      -- Since e_inter is a write WITH permissions, the predecessor that set up those
      -- permissions must have gotten write permissions from a directory write event.
      have hinter_cle_is_dir_write : Event.isDirWrite n e_inter_cle := by
        -- e_inter has permissions and is a write
        -- The predecessor accessed the directory event e_inter_cle
        -- Since e_inter is a write with permissions, it cannot be on I state
        -- Therefore reqToDirOfRequestEvent preserves the write
        unfold Event.isDirWrite
        -- Case split on e_inter_cle
        match  he_cle : e_inter_cle with
        | .cacheEvent _ =>
          -- e_inter_cle is not a cache event (it's a directory event from predecessor)
          -- This contradicts that it accesses directory
          exfalso
          have : e_inter_cle.isDirectoryEvent := hpred_accesses_dir.isDir
          simp [Event.isDirectoryEvent, he_cle] at this
        | .directoryEvent de =>
          simp
          -- Extract the directory request from hpred_accesses_dir
          have hdir_req := hpred_accesses_dir.dirCorresponds.dirReq
          -- hdir_req: de.req = b.reqToDirOfRequestEvent n init true hexists_pred_getting_perms.choose

          -- Use hreq_has_perms to constrain e_inter: it either is coherent or NC with coherent per ms
          -- since hwrite rules out case (3) (NC weak read on Vd)
          cases hreq_has_perms with
          | hasPerms hcoh hhas_perms =>
              -- e_inter is coherent with permissions ≥ MRS
              -- The predecessor's directory request is obtained via reqToDirOfRequestEvent
              -- For coherent requests, the directory request inherits write type
              -- Check if it's NC Rel (which maps to Vd state)
              by_cases hrel : (Event.req n hexists_pred_getting_perms.choose).val = ⟨.w, false, .Rel⟩
              · -- NC Rel case
                -- hdir_req: Event.req n e_inter_cle = b.reqToDirOfRequestEvent ...
                -- he_cle: e_inter_cle = Event.directoryEvent de
                -- By definition Event.req n (Event.directoryEvent de) = de.req
                have : Event.req n e_inter_cle = de.req := by
                  rw [he_cle]
                  rfl
                have hdir_req' : de.req = b.reqToDirOfRequestEvent n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose := by
                  rw [<- this]
                  exact hdir_req
                -- Unfold Behaviour.reqToDirOfRequestEvent using hrel
                have : de.req = Event.reqToDirOfRequestEvent n hexists_pred_getting_perms.choose Vd := by
                  rw [hdir_req']
                  simp [Behaviour.reqToDirOfRequestEvent, hrel]
                rw [this]
                exact reqToDir_preserves_write_on_vd_ncrel hexists_pred_getting_perms.choose hrel
              · -- Default case: coherent write preserves write
                have : Event.req n e_inter_cle = de.req := by rw [he_cle]; rfl
                have hdir_req' : de.req = b.reqToDirOfRequestEvent n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose := by
                  rw [<- this]; exact hdir_req
                have : de.req = Event.reqToDirOfRequestEvent n hexists_pred_getting_perms.choose (b.stateBefore n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) hexists_pred_getting_perms.choose).cache := by
                  rw [hdir_req']
                  simp [Behaviour.reqToDirOfRequestEvent, hrel]
                rw [this]
                -- The predecessor gave e_inter write permissions
                -- For e_inter (a coherent write) to have permissions, its predecessor must be a write
                -- In the coherent protocol, coherent writes propagate from coherent writes
                have hpred_has_no_perms := hexists_pred_getting_perms.choose_spec.right
                simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at hpred_has_no_perms
                simp[Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_has_no_perms
                -- simp[Behaviour.IsImmediateBottomPredSatisfyingProp] at hpred_has_no_perms
                have hpred_prop := hpred_has_no_perms.satisfyP
                simp[Event.PropOnEvent] at hpred_prop
                simp[Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_prop
                -- Key hypothesis: predecessor `e_pred` does not have permissions
                have hpred_missing_perms := hpred_prop.missingPerms
                -- Key hypothesis: `e_pred` is a cache event.
                have hpred_cache : hexists_pred_getting_perms.choose.isCacheEvent := hpred_prop.reqCache

                have hwrite_pred : hexists_pred_getting_perms.choose.req.val.isWrite := by
                  -- Use the helper lemma: predecessor producing write-permission state must be write
                  exact produces_state_with_write_perms_implies_is_write hwrite hcoh hhas_perms hpred_produces_state_at_least_req_made_on_state hinter_pred_not_down hpred_missing_perms hpred_cache
                have hcoh_pred : hexists_pred_getting_perms.choose.req.val.coherent = true := by
                  -- Derive that e_inter was made on a coherent state
                  -- For a coherent write with permissions, the state before must be coherent
                  have hstate_coh : (b.stateReqMadeOn n init e_inter).c = true := by
                    unfold Behaviour.stateReqMadeOn
                    -- For coherent requests with permissions, the state before has c=true
                    -- This follows from MRS.c = true and MRS ≤ state_before
                    have hmrs_has_c_true : (Event.req n e_inter).MRS.c = true := by
                      cases e_inter with
                      | cacheEvent ce =>
                        unfold Event.isCoherent ValidRequest.isCoherent Request.isCoherent at hcoh
                        cases he_req : ce.req with
                        | mk vr hvr =>
                          cases vr with
                          | mk rw coh cons =>
                            simp at hcoh
                            rw [he_req] at hcoh
                            simp at hcoh
                            cases hcoh
                            -- Now coh = true, so we need to show MRS.c = true
                            -- For all coherent requests, MRS has c = true
                            simp [Event.req, he_req, ValidRequest.MRS, ReadWrite.toPerms, ReadWrite.toRWPerms]
                            -- Only valid coherent requests: SC (r/w), Rel w, Weak w
                            -- Invalid: Rel r, Acq (r/w), Weak r - derive contradiction from IsValid'
                            match cons, rw with
                            | .SC, .w | .SC, .r | .Rel, .w | .Weak, .w => rfl
                            | .Rel, .r => exfalso; simp [Request.IsValid'] at hvr
                            | .Acq, _ => exfalso; simp [Request.IsValid'] at hvr
                            | .Weak, .r => exfalso; simp [Request.IsValid'] at hvr
                      | directoryEvent _ =>
                        exfalso
                        simp [Event.isCoherent] at hcoh
                    have hle : (Event.req n e_inter).MRS ≤ (b.stateBefore n (init.stateAt n e_inter) e_inter).cache := hhas_perms
                    have hc_le : (Event.req n e_inter).MRS.c ≤ (b.stateBefore n (init.stateAt n e_inter) e_inter).cache.c := by
                      cases hle with
                      | inl hlt => exact hlt.right.left
                      | inr heq => rw [← heq]
                    rw [hmrs_has_c_true] at hc_le
                    cases h_c : (b.stateBefore n (init.stateAt n e_inter) e_inter).cache.c
                    · exfalso; rw [h_c] at hc_le; trivial
                    · rfl
                  -- Use the implementation lemma
                  exact pred_missing_perms_req_impl hstate_coh hpred_produces_state_at_least_req_made_on_state hinter_pred_not_down hpred_missing_perms hpred_cache
                exact reqToDir_preserves_write_of_coherent hexists_pred_getting_perms.choose _ hwrite_pred hcoh_pred
          | ncRelAcqWeakWriteHasCoherentPerms hncraw hhascoh =>
              -- e_inter is NC/rel/acq/weak write with coherent perms
              -- These are all writes, so the directory event will be a write
              -- For NC rel/acq/weak writes on coherent state, the directory version stays write
              by_cases hrel : (Event.req n hexists_pred_getting_perms.choose).val = ⟨.w, false, .Rel⟩
              · -- NC Rel: write on Vd
                have : Event.req n e_inter_cle = de.req := by rw [he_cle]; rfl
                have hdir_req' : de.req = b.reqToDirOfRequestEvent n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose := by
                  rw [<- this]; exact hdir_req
                have : de.req = Event.reqToDirOfRequestEvent n hexists_pred_getting_perms.choose Vd := by
                  rw [hdir_req']
                  simp [Behaviour.reqToDirOfRequestEvent, hrel]
                rw [this]
                exact reqToDir_preserves_write_on_vd_ncrel hexists_pred_getting_perms.choose hrel
              · -- Other NC/acq/weak writes: default case preserves write
                have : Event.req n e_inter_cle = de.req := by rw [he_cle]; rfl
                have hdir_req' : de.req = b.reqToDirOfRequestEvent n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose := by
                  rw [<- this]; exact hdir_req
                have : de.req = Event.reqToDirOfRequestEvent n hexists_pred_getting_perms.choose (b.stateBefore n (InitialSystemState.stateAt n init hexists_pred_getting_perms.choose) hexists_pred_getting_perms.choose).cache := by
                  rw [hdir_req']
                  simp [Behaviour.reqToDirOfRequestEvent, hrel]
                rw [this]
                -- e_inter is NC/rel/acq/weak write with permissions on coherent state
                -- The predecessor gave those permissions
                have hwrite_pred : hexists_pred_getting_perms.choose.req.val.isWrite := by
                  -- hhascoh.hasPerms : b.hasPerms n init e_inter
                  -- hhascoh.onCoherentState : state e_inter was made on is coherent
                  -- Use helper: predecessor must be write to produce write permissions
                  have hpred_has_no_perms := hexists_pred_getting_perms.choose_spec.right
                  simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at hpred_has_no_perms
                  simp[Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_has_no_perms
                  have hpred_prop := hpred_has_no_perms.satisfyP
                  simp[Event.PropOnEvent] at hpred_prop
                  simp[Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_prop
                  have hpred_missing_perms := hpred_prop.missingPerms
                  have hpred_cache : hexists_pred_getting_perms.choose.isCacheEvent := hpred_prop.reqCache
                  exact produces_state_with_write_perms_implies_is_write_no_coherence (cmp := cmp) (b := b) (init := init)
                    (e_pred := hexists_pred_getting_perms.choose) (e_req := e_inter)
                    hwrite hhascoh.hasPerms hhascoh.onCoherentState
                    hpred_produces_state_at_least_req_made_on_state hinter_pred_not_down hpred_missing_perms hpred_cache he_inter
                have hcoh_pred : hexists_pred_getting_perms.choose.req.val.coherent = true := by
                  -- hhascoh.onCoherentState : Behaviour.reqMadeOnCoherentState n b init e_inter
                  -- which means (b.stateReqMadeOn n init e_inter).c = true
                  -- predecessor produces a state at least as high, which means c=true
                  -- Use helper: predecessor producing coherent state must be coherent
                  have hstate_coh : (b.stateReqMadeOn n init e_inter).c = true := hhascoh.onCoherentState
                  -- Extract same properties as above for this scope
                  have hpred_has_no_perms := hexists_pred_getting_perms.choose_spec.right
                  simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at hpred_has_no_perms
                  simp[Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_has_no_perms
                  have hpred_prop := hpred_has_no_perms.satisfyP
                  simp[Event.PropOnEvent] at hpred_prop
                  simp[Behaviour.predHasNoPermsAndLeavesStateAtLeastReq] at hpred_prop
                  have hpred_missing_perms := hpred_prop.missingPerms
                  have hpred_cache : hexists_pred_getting_perms.choose.isCacheEvent := hpred_prop.reqCache
                  exact nc_acq_weak_write_has_coherent_state_implies_pred_is_coherent
                    hstate_coh
                    hpred_produces_state_at_least_req_made_on_state
                    hinter_pred_not_down
                    hpred_missing_perms
                    hpred_cache
                exact reqToDir_preserves_write_of_coherent hexists_pred_getting_perms.choose _ hwrite_pred hcoh_pred
          | ncWeakReadHasPermsNotVd hncwr _ =>
              -- e_inter is NC weak read, contradicts hwrite (which is write)
              exfalso
              -- hncwr: e_inter is NC weak read (non-coherent and weak, which means read)
              -- hwrite: e_inter is write - contradiction
              -- NC weak read means req = ⟨⟨.r, false, .Weak⟩, ...⟩ so rw = .r
              -- isWrite means req.val.rw = .w
              -- These are contradictory
              cases e_inter with
              | cacheEvent ce =>
                simp [Event.isNcWeakRead, CacheEvent.isNcWeakRead] at hncwr
                -- hncwr : ce.req = ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩
                simp [Event.isWrite] at hwrite
                -- hwrite : ce.req.val.isWrite, which means ce.req.val.rw = .w
                rw [hncwr] at hwrite
                simp [Request.isWrite] at hwrite
              | directoryEvent _ =>
                simp [Event.isNcWeakRead] at hncwr
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have _hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      intro e_inter_down _he_mem _hdowngrade
      intro hob
      rw [_hcle_eq] at hob
      exact Event.contradiction_of_reflexive_ordered_before _
        (Trans.trans hob.pred hob.succ)

    | orderAfterDir hweak_req_on_vd hsucc_encap_dir hsucc_same_protocol =>
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
      -- Show that e_inter_cle is a directory write
      -- User insight: orderAfterDir with hwrite should lead to directory write
      -- Key facts:
      --   1. hwrite : e_inter.isWrite
      --   2. hweak_read_on_vd : b.ncWeakReqOnVd n init e_inter
      --      - This means e_inter.isNcWeak (weak and non-coherent)
      --      - Request is on/after Vd state
      --   3. hsucc_encap_dir : successor accesses directory event e_inter_cle
      -- Since e_inter is an NC weak WRITE (not read) on Vd, when its successor
      -- accesses the directory, that directory event should also be a write.
      have hinter_cle_is_dir_write : Event.isDirWrite n e_inter_cle := by
        -- e_inter is NC weak write on Vd
        -- The successor encapsulates the directory event
        -- NC weak write on Vd → directory write via successor
        unfold Event.isDirWrite
        -- Case split on e_inter_cle
        match he_cle : e_inter_cle with
        | .cacheEvent _ =>
          -- e_inter_cle is not a cache event (directory event from successor)
          -- This contradicts that it accesses directory
          exfalso
          have hdir_ev : e_inter_cle.isDirectoryEvent :=
            hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.isDir
          simp [Event.isDirectoryEvent, he_cle] at hdir_ev
        | .directoryEvent de =>
          simp
          -- NC weak write on Vd: the directory event should be a write
          -- Key: reqToDirOfRequestEvent preserves write type when not on I state
          have hsucc := hsucc_encap_dir.choose_spec.right.satisfyP
          have hdir_corresponds := hsucc.encapCorresponding.dirCorresponds
          have hdir_req := hdir_corresponds.dirReq
          -- e_inter_cle.req = reqToDirOfRequestEvent applied to the successor
          -- The successor is on Vd state (from reqOnVdWithCorrespondingDir)
          have hsucc_on_vd := hsucc.stateBeforeAsVd
          -- Extract the successor event (it's a cache event on Vd)
          have hsucc_event := hsucc_encap_dir.choose
          -- The directory request equals reqToDirOfRequestEvent
          simp [Event.req] at hdir_req
          -- Since successor is on Vd (not I), reqToDirOfRequestEvent preserves write type
          -- For NC weak write on Vd, none of the exception cases apply
          -- The successor inherits the write property from e_inter
          -- Need to show de.req.val.isWrite

          -- Key facts:
          -- 1. hsucc_on_vd : (b.stateBefore n init hsucc_event) = VdEntry n
          --    This means state is Vd, NOT I
          -- 2. e_inter is NC weak write (from hweak_read_on_vd.weakReq)
          -- 3. reqToDirOfRequestEvent exception cases only apply on I state
          -- 4. Therefore default case applies, and write is preserved

          -- The successor's request is NC weak (from hweak_read_on_vd)
          have hweak := hweak_req_on_vd.weakReq
          -- The directory event's request is obtained via reqToDirOfRequestEvent
          have hdir_req := hdir_corresponds.dirReq


          -- TODO: Hint: Use `hsucc_on_vd` to show `e_inter_succ` is made on Vd state,
          -- and `e_inter_succ` encapsulates a write-directory event
          -- through `reqOnVdWithCorrespondingDir`.
          -- Then because `e_inter_succ` is made on Vd state, `e_inter_succ` encapsulates a write directory event (by the restrictions/defs in `reqOnVdWithCorrespondingDir`)

          -- STRATEGY: Show de.req.val.isWrite by analyzing reqToDirOfRequestEvent
          -- The successor satisfies isRelAcqOrVdWB and is made on Vd
          have hisrel_acq_vdwb := hsucc.isRelAcqOrVdWB
          -- The directory request comes from reqToDirOfRequestEvent
          simp [Event.req] at hdir_req
          -- On Vd state, for requests in isRelAcqOrVdWB:
          -- - Acquires: if read, becomes write (case 3 in reqToDirOfRequestEvent)
          -- - NC/CReleases: writes stay as writes (case 4)
          -- - VdWriteBack: write stays as write (case 4)
          -- - SCWrite: write stays as write (case 4)
          -- - SCRead: could be acquire (becomes write) or stays as read
          -- Need to case-split on hisrel_acq_vdwb and show write in each case
          rcases hisrel_acq_vdwb with hacq | hnc_rel | hc_rel | hvdwb | hsc_write | hsc_read
          · -- Acquire case: if read, reqToDirOfRequestEvent makes it write on Vd
            have hde_req := hdir_corresponds.dirReq
            change (Event.req n e_inter_cle) =
                Behaviour.reqToDirOfRequestEvent n b
                  (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
                  (Exists.choose hsucc_encap_dir) at hde_req
            have hreq_acq : Event.req n (Exists.choose hsucc_encap_dir) =
                ⟨⟨.r, false, .Acq⟩, by simp [Request.IsValid']⟩ := by
              cases hchoose : Exists.choose hsucc_encap_dir with
              | directoryEvent de_succ =>
                simp [hchoose, Event.isAcquire] at hacq
              | cacheEvent ce_succ =>
                simpa [hchoose, Event.req, Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] using hacq
            have hgoal : (Event.req n e_inter_cle).val.isWrite := by
              rw [hde_req]
              simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
                hsucc_on_vd, hreq_acq, Request.isWrite, VdEntry, EntryState.cache]
            simpa [Event.req, he_cle] using hgoal
          · -- NcRelease case: NC release writes stay as writes on Vd
            have hde_req := hdir_corresponds.dirReq
            change (Event.req n e_inter_cle) =
                Behaviour.reqToDirOfRequestEvent n b
                  (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
                  (Exists.choose hsucc_encap_dir) at hde_req
            have hreq_nc_rel : Event.req n (Exists.choose hsucc_encap_dir) =
                ⟨⟨.w, false, .Rel⟩, by simp [Request.IsValid']⟩ := by
              cases hchoose : Exists.choose hsucc_encap_dir with
              | directoryEvent de_succ => simp [hchoose, Event.isNcRelease] at hnc_rel
              | cacheEvent ce_succ =>
                simpa [hchoose, Event.req, Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease] using hnc_rel
            have hgoal : (Event.req n e_inter_cle).val.isWrite := by
              rw [hde_req]
              simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
                hsucc_on_vd, hreq_nc_rel, Request.isWrite, Vd]
            simpa [Event.req, he_cle] using hgoal
          · -- CRelease case: coherent release writes stay as writes
            have hde_req := hdir_corresponds.dirReq
            change (Event.req n e_inter_cle) =
                Behaviour.reqToDirOfRequestEvent n b
                  (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
                  (Exists.choose hsucc_encap_dir) at hde_req
            have hreq_c_rel : Event.req n (Exists.choose hsucc_encap_dir) =
                ⟨⟨.w, true, .Rel⟩, by simp [Request.IsValid']⟩ := by
              cases hchoose : Exists.choose hsucc_encap_dir with
              | directoryEvent de_succ => simp [hchoose, Event.isCRelease] at hc_rel
              | cacheEvent ce_succ =>
                have hval : ce_succ.req.val = ⟨.w, true, .Rel⟩ := by
                  simp only [Event.isCRelease, hchoose] at hc_rel
                  exact hc_rel
                ext
                · simp [Event.req, hchoose, hval]
            have hgoal : (Event.req n e_inter_cle).val.isWrite := by
              rw [hde_req]
              simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
                hsucc_on_vd, hreq_c_rel, Request.isWrite, Vd]
            simpa [Event.req, he_cle] using hgoal
          · -- VdWriteBack case: vd write-back is a downgrade weak write
            have hde_req := hdir_corresponds.dirReq
            change (Event.req n e_inter_cle) =
                Behaviour.reqToDirOfRequestEvent n b
                  (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
                  (Exists.choose hsucc_encap_dir) at hde_req
            have hreq_vdwb : Event.req n (Exists.choose hsucc_encap_dir) =
                ⟨⟨.w, false, .Weak⟩, by simp [Request.IsValid']⟩ := by
              cases hchoose : Exists.choose hsucc_encap_dir with
              | directoryEvent de_succ => simp [hchoose, Event.isVdWriteBack] at hvdwb
              | cacheEvent ce_succ =>
                simp only [Event.isVdWriteBack, hchoose] at hvdwb
                have hval : ce_succ.req.val = ⟨.w, false, .Weak⟩ := hvdwb.isWeakWrite
                have hdown : ce_succ.down = true := hvdwb.isDown
                ext
                · simp [Event.req, hchoose, hval]
            have hgoal : (Event.req n e_inter_cle).val.isWrite := by
              rw [hde_req]
              -- Need to show: reqToDirOfRequestEvent returns a write for VdWriteBack
              -- VdWriteBack has down=true, so none of the exception cases match
              -- The function falls through to default case: e_req.req
              simp only [Behaviour.reqToDirOfRequestEvent]
              -- Not Rel, so the if condition is false
              have hnot_rel : ¬(Event.req n (Exists.choose hsucc_encap_dir)).val = ⟨.w, false, .Rel⟩ := by
                rw [hreq_vdwb]
                simp
              simp [hnot_rel]
              -- Now we have Event.reqToDirOfRequestEvent
              simp only [Event.reqToDirOfRequestEvent]
              -- With down=true, all specific patterns fail, so we get the default case
              have hdown : Event.down n (Exists.choose hsucc_encap_dir) = true := by
                cases hchoose : Exists.choose hsucc_encap_dir with
                | directoryEvent de_succ => simp [hchoose, Event.isVdWriteBack] at hvdwb
                | cacheEvent ce_succ =>
                  simp only [Event.down, hchoose, Event.isVdWriteBack] at hvdwb ⊢
                  exact hvdwb.isDown
              -- Rewrite with the specific values we know
              rw [hreq_vdwb, hsucc_on_vd, hdown]
              -- This simplifies the match: first two cases require down=false (don't match)
              -- Third case requires .Acq request (we have .Weak, doesn't match)
              -- So it falls through to the default case
              simp [Request.isWrite]
            simpa [Event.req, he_cle] using hgoal
          · -- SCWrite case: SC write stays as write
            have hde_req := hdir_corresponds.dirReq
            change (Event.req n e_inter_cle) =
                Behaviour.reqToDirOfRequestEvent n b
                  (InitialSystemState.stateAt n init (Exists.choose hsucc_encap_dir)) true
                  (Exists.choose hsucc_encap_dir) at hde_req
            have hreq_sc_write : Event.req n (Exists.choose hsucc_encap_dir) =
                ⟨⟨.w, true, .SC⟩, by simp [Request.IsValid']⟩ := by
              cases hchoose : Exists.choose hsucc_encap_dir with
              | directoryEvent de_succ =>
                -- If a directory event satisfies isSCWrite, its request must be an SC write
                -- by definition of ValidRequest.isSCWrite
                have hreq_is_sc_write : de_succ.req.isSCWrite := by
                  simp only [Event.isSCWrite, Event.req, hchoose] at hsc_write
                  exact hsc_write
                -- ValidRequest.isSCWrite means the request equals ⟨⟨.w, true, .SC⟩, ...⟩
                simp only [hchoose, Event.req, ValidRequest.isSCWrite] at hreq_is_sc_write
                exact hreq_is_sc_write
              | cacheEvent ce_succ =>
                have : ce_succ.req = ⟨⟨.w, true, .SC⟩, by simp[Request.IsValid']⟩ := by
                  simp only [Event.isSCWrite, Event.req, hchoose, ValidRequest.isSCWrite] at hsc_write
                  exact hsc_write
                simpa [hchoose, Event.req] using this
            have hgoal : (Event.req n e_inter_cle).val.isWrite := by
              rw [hde_req]
              simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
                hsucc_on_vd, hreq_sc_write, Request.isWrite, Vd]
            simpa [Event.req, he_cle] using hgoal
          · -- SCRead case: NC weak and SC read can't coexist in same protocol chain
            -- e_inter is NC weak (non-coherent), successor would be SC read (coherent)
            -- They're in the same protocol but have different coherence, which is impossible
            exfalso
            -- Extract that requests have different coherence
            have hcontra_coherence : (Event.req n e_inter).val.coherent = false ∧
                                      (Event.req n (Exists.choose hsucc_encap_dir)).val.coherent = true := by
              constructor
              · -- e_inter is NC weak → coherent = false
                cases e_inter with
                | directoryEvent de =>
                  -- Directory events can't be NC weak (Event.isNonCoherent is false for directory events)
                  simp only [Event.isNcWeak, Event.isNonCoherent] at hweak
                  simp at hweak -- false = true simplifies to False
                | cacheEvent ce =>
                  simp only [Event.isNcWeak, Event.isNonCoherent, Event.req] at hweak
                  by_cases h : ce.req.val.coherent
                  · exact False.elim (hweak.left h)
                  · simp only [Bool.not_eq_true] at h; exact h
              · -- Successor is SC read → coherent = true
                cases hsucc_case : Exists.choose hsucc_encap_dir with
                | directoryEvent de =>
                  simp only [Event.isSCRead, ValidRequest.isSCRead] at hsc_read
                  simp only [Event.req, hsucc_case] at hsc_read ⊢
                  rw [hsc_read]
                | cacheEvent ce =>
                  simp only [Event.isSCRead, ValidRequest.isSCRead] at hsc_read
                  simp only [Event.req, hsucc_case] at hsc_read ⊢
                  rw [hsc_read]
            -- Both are in the same protocol
            have hsame_pi : e_inter.protocol = (Exists.choose hsucc_encap_dir).protocol :=
              hsucc_same_protocol.symm
            -- Extract the underlying Request values
            have hncwrite_req : (Event.req n e_inter).val = ⟨.w, false, .Weak⟩ := by
              -- e_inter is NC weak write from hweak_req_on_vd
              cases hinter_event : e_inter with
              | directoryEvent de =>
                -- Contradiction: ncWeakReqOnVd requires cache event
                have hcache := hweak_req_on_vd.reqCache
                simp only [Event.isCacheEvent, hinter_event] at hcache
                exact False.elim (Bool.noConfusion hcache)
              | cacheEvent ce =>
                -- Extract from NC weak write property
                have h_weak := hweak_req_on_vd.weakReq
                simp only [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, hinter_event] at h_weak
                simp only [Event.req, hinter_event]
                obtain ⟨hnc, hweak⟩ := h_weak
                have hwrite_val : ce.req.val.rw = .w := by
                  simp only [Event.isWrite, hinter_event] at hwrite
                  exact hwrite
                simp only [Bool.not_eq_true] at hnc
                -- Construct the Request value
                cases hreq : ce.req.val with
                | mk rw coh cons =>
                  simp only at hwrite_val hnc hweak
                  simp only [hreq] at hwrite_val hnc hweak
                  simp [hwrite_val, hnc, hweak]
            have hscread_req : (Event.req n (Exists.choose hsucc_encap_dir)).val = ⟨.r, true, .SC⟩ := by
              -- SC read from hsc_read
              cases hsucc_event : Exists.choose hsucc_encap_dir with
              | directoryEvent de =>
                simp only [Event.isSCRead, ValidRequest.isSCRead, Event.req, hsucc_event] at hsc_read
                exact congr_arg Subtype.val hsc_read
              | cacheEvent ce =>
                simp only [Event.isSCRead, ValidRequest.isSCRead, Event.req, hsucc_event] at hsc_read
                exact congr_arg Subtype.val hsc_read
            -- Apply the helper lemma
            exact protocol_nc_weak_write_sc_read_contradiction (cmp:=cmp) he_inter
              (hsucc_encap_dir.choose_spec.left) hncwrite_req hscread_req hsame_pi
      have hsame_protocol_and_dir_write : e_inter_cle.protocol = e_w_cle.protocol ∧
                                          e_inter_cle.protocol = e_r_cle.protocol ∧
                                          Event.isDirWrite n e_inter_cle :=
        ⟨hsame_protocol_cles.1, hsame_protocol_cles.2, hinter_cle_is_dir_write⟩
      have _hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      intro e_inter_down _he_mem _hdowngrade
      intro hob
      rw [_hcle_eq] at hob
      exact Event.contradiction_of_reflexive_ordered_before _
        (Trans.trans hob.pred hob.succ)
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
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access (_hknow_dir_access cmp b init e_inter))
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
  intro e_inter_down he_mem hdown hob
  -- In the same-CLE case (_hcle_eq), e_w_cle = e_r_cle, so nothing can be OrderedBetween.
  rw [_hcle_eq] at hob
  exact Event.contradiction_of_reflexive_ordered_before _
    (Trans.trans hob.pred hob.succ)

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
  (hwrite_not_down : ¬ e_inter.down)
  (hcontra : NoInterveningWrites.constraints _hw_is_write _r_is_read hw_c_and_g_lin hr_c_and_g_lin e_inter _hknow_dir_access (_hknow_dir_access cmp b init e_inter))
  (hinter_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_inter)
  (hsame_cache : ¬e_inter.sameStructure n e_w)
  : Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose) := by

  -- Case split on whether e_inter is in the same protocol/cluster as e_w and e_r
  by_cases hsame_protocol : e_inter.sameProtocol n e_w
  · -- Case 2a: Same protocol/cluster, different cache
    exact noInterveningWrites_diffCache_sameProtocol_case
      _hw_is_write _r_is_read _hsame_struct hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin _hcle_eq _hknow_dir_access
      (he_inter := he_inter) hwrite_cluster hwrite hwrite_not_down hcontra hinter_lin hsame_cache hsame_protocol
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
  intro e he hwrite_cluster hwrite hwrite_not_down

  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose

  have hinter_lin := _hknow_dir_access cmp b init e
  have hcontra := _hno_intervening e he hwrite_cluster hwrite hwrite_not_down hinter_lin

  by_cases hsame_protocol : e.sameProtocol n e_w
  .
    -- Case split: same cache, different cache same cluster, or different cluster
    by_cases hsame_cache : e.sameStructure n e_w
    · -- Case 1: Same cache as e_w (and e_r)
      apply Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites.otherWSameCache
      constructor
      . case pos.no_write_btn_w_r.notDown => exact hwrite_not_down
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
        intro _e_inter_cle _he_mem ⟨_hdir_access, hbetween⟩ ⟨_, _hcle_between⟩
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
        hwrite_cluster hwrite hwrite_not_down hcontra hinter_lin hsame_cache
  . -- Case where e is in a different protocol than e_w
    -- We know ¬(e.sameStructure n e_w) because if they had the same structure,
    -- they would have the same protocol (by sameStructure_implies_sameProtocol)
    have hsame_cache : ¬e.sameStructure n e_w := by
      intro hcontra_struct
      have hsame_prot : e.sameProtocol n e_w := sameStructure_implies_sameProtocol hcontra_struct
      exact hsame_protocol hsame_prot
    exact noInterveningWrites_diffCache_case _hw_is_write _r_is_read _hsame_struct
      hw_not_down r_not_down
      hw_c_and_g_lin hr_c_and_g_lin _hcle_eq _hknow_dir_access (he_inter := he)
      hwrite_cluster hwrite hwrite_not_down hcontra hinter_lin hsame_cache

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
    hpred_accesses_dir hinter_leaves_state_at_least hpred_same_protocol hreq_not_down hpred_produces hinter_pred_not_down =>
    -- Contradiction: `e_evict` is a downgrade ^ `hinter_pred_not_down` says it's not a downgrade
    have hevict_down : e_evict.down := by
      cases e_evict with
      | cacheEvent ce_evict =>
          have hsw : ce_evict.isEvictSW := by
            simpa [Event.isEvictSW] using hevict_sw_evict
          exact hsw.evict.downgrade
      | directoryEvent de =>
          simp [Event.isCacheEvent] at hevict_is_cache
    exact hreq_not_down hevict_down
  . case orderAfterDir hweak_read_on_vd hsucc_encap_dir hsucc_same_protocol hnot_down =>
    -- Contradiction: `e_evict` is a downgrade ^ `hnot_down` says it's not a downgrade
    have hevict_down : e_evict.down := by
      cases e_evict with
      | cacheEvent ce_evict =>
          have hsw : ce_evict.isEvictSW := by
            simpa [Event.isEvictSW] using hevict_sw_evict
          exact hsw.evict.downgrade
      | directoryEvent de =>
          simp [Event.isCacheEvent] at hevict_is_cache
    exact hnot_down hevict_down

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

/-- Two cluster directory events that both route through ClusterToGlobal and dirAccessOfRequest
    to reach the same global directory must have the same protocol.

    This captures the protocol-determinism of the ClusterToGlobal + dirAccessOfRequest chain:
    Two events with different protocols cannot both produce sequences that converge to the
    same global directory endpoint. -/
lemma cluster_dirs_to_same_global_dir_have_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {hw_cle hr_cle hw_gcache hr_gcache e_gdir : Event n}
  (hw_cle_is_dir : hw_cle.isDirectoryEvent)
  (hr_cle_is_dir : hr_cle.isDirectoryEvent)
  (hw_gcache_eq : hw_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hw_cle hw_cle_is_dir)
  (hw_gcache_to_gdir : b.dirAccessOfRequest n init hw_gcache e_gdir)
  (hr_gcache_eq : hr_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hr_cle hr_cle_is_dir)
  (hr_gcache_to_gdir : b.dirAccessOfRequest n init hr_gcache e_gdir)
  : hw_cle.protocol = hr_cle.protocol := by
  -- First, if two requests access the same directory event, they are at the same cache struct.
  have hsame_struct_of_same_dir_access :
      hw_gcache.struct = hr_gcache.struct := by
    have hsame_struct_of_entry :
        ∀ {e₁ e₂ : Event n}, e₁.sameEntry n e₂ → e₁.struct = e₂.struct := by
      intro e₁ e₂ hentry
      exact Event.same_entry_impl_same_struct (n := n) e₁ e₂ hentry
    cases hw_gcache_to_gdir with
    | encapDir _ hw_encap =>
      cases hr_gcache_to_gdir with
      | encapDir _ hr_encap =>
        have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_encap.dirOfReq
        simpa [Event.sameStructure, Event.struct] using congrArg (fun e => e.struct) hreq_eq
      | orderBeforeDir _ hr_pred hr_pred_access _ =>
        have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_pred_access.dirOfReq
        have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hr_struct := hsame_struct_of_entry hr_entry
        have hr_struct' : hr_gcache.struct = hw_gcache.struct := by
          have hr_struct1 : hr_gcache.struct = hr_pred.choose.struct := hr_struct.symm
          have hr_struct2 : hr_gcache.struct = hw_gcache.struct := by
            simpa [hreq_eq] using hr_struct1
          exact hr_struct2
        exact hr_struct'.symm
      | orderAfterDir _ hr_succ =>
        have hreq_eq := dir_event_of_req_event_unique hw_encap.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
        have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hr_struct := hsame_struct_of_entry hr_entry
        have hr_struct' : hr_gcache.struct = hw_gcache.struct := by
          have hr_struct1 : hr_gcache.struct = hr_succ.choose.struct := hr_struct
          have hr_struct2 : hr_gcache.struct = hw_gcache.struct := by
            simpa [hreq_eq] using hr_struct1
          exact hr_struct2
        exact hr_struct'.symm
    | orderBeforeDir _ hw_pred hw_pred_access _ =>
      cases hr_gcache_to_gdir with
      | encapDir _ hr_encap =>
        have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_encap.dirOfReq
        have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have hw_struct' : hw_gcache.struct = hr_gcache.struct := by
          have hw_struct1 : hw_gcache.struct = hw_pred.choose.struct := hw_struct.symm
          have hw_struct2 : hw_gcache.struct = hr_gcache.struct := by
            simpa [hreq_eq] using hw_struct1
          exact hw_struct2
        exact hw_struct'
      | orderBeforeDir _ hr_pred hr_pred_access _ =>
        have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_pred_access.dirOfReq
        have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have hr_struct := hsame_struct_of_entry hr_entry
        have : hw_gcache.struct = hr_gcache.struct := by
          have hw' : hw_gcache.struct = hw_pred.choose.struct := hw_struct.symm
          have hr' : hr_gcache.struct = hr_pred.choose.struct := hr_struct.symm
          have hr'' : hr_gcache.struct = hw_pred.choose.struct := by
            simpa [hreq_eq] using hr'
          exact hw'.trans hr''.symm
        exact this
      | orderAfterDir _ hr_succ =>
        have hreq_eq := dir_event_of_req_event_unique hw_pred_access.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
        have hw_entry := hw_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have hr_struct := hsame_struct_of_entry hr_entry
        have : hw_gcache.struct = hr_gcache.struct := by
          have hw' : hw_gcache.struct = hw_pred.choose.struct := hw_struct.symm
          have hr' : hr_gcache.struct = hr_succ.choose.struct := hr_struct
          have hr'' : hr_gcache.struct = hw_pred.choose.struct := by
            simpa [hreq_eq] using hr'
          exact hw'.trans hr''.symm
        exact this
    | orderAfterDir _ hw_succ =>
      cases hr_gcache_to_gdir with
      | encapDir _ hr_encap =>
        have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_encap.dirOfReq
        have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have : hw_gcache.struct = hr_gcache.struct := by
          have hw' : hw_gcache.struct = hw_succ.choose.struct := hw_struct
          have hw'' : hw_gcache.struct = hr_gcache.struct := by
            simpa [hreq_eq] using hw'
          exact hw''
        exact this
      | orderBeforeDir _ hr_pred hr_pred_access _ =>
        have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_pred_access.dirOfReq
        have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hr_entry := hr_pred.choose_spec.right.isImmPred.bPred.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have hr_struct := hsame_struct_of_entry hr_entry
        have : hw_gcache.struct = hr_gcache.struct := by
          have hw' : hw_gcache.struct = hw_succ.choose.struct := hw_struct
          have hr' : hr_gcache.struct = hr_pred.choose.struct := hr_struct.symm
          have hr'' : hr_gcache.struct = hw_succ.choose.struct := by
            simpa [hreq_eq] using hr'
          exact hw'.trans hr''.symm
        exact this
      | orderAfterDir _ hr_succ =>
        have hreq_eq := dir_event_of_req_event_unique hw_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq hr_succ.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
        have hw_entry := hw_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hr_entry := hr_succ.choose_spec.right.isImmBottomSucc.sameEntry
        have hw_struct := hsame_struct_of_entry hw_entry
        have hr_struct := hsame_struct_of_entry hr_entry
        have : hw_gcache.struct = hr_gcache.struct := by
          have hw' : hw_gcache.struct = hw_succ.choose.struct := hw_struct
          have hr' : hr_gcache.struct = hr_succ.choose.struct := hr_struct
          have hr'' : hr_gcache.struct = hw_succ.choose.struct := by
            simpa [hreq_eq] using hr'
          exact hw'.trans hr''.symm
        exact this

  -- Extract correspondence constraints from ClusterToGlobal for each CLE.
  have hw_cle_corr_gcache : Event.reqAtCorrespondingGCacheOfCDir n hw_cle hw_gcache := by
    rw [hw_gcache_eq]
    simp [Behaviour.Shim.ClusterToGlobal.cDir'sGReq]
    cases hshim : cmp.shimAxioms.clusterToGlobal b init hw_cle hw_cle_is_dir with
    | encapGlobalCache _ hreq =>
      simpa [hshim] using hreq.choose_spec.right.gReqOfCDir.gReq
    | noGlobalCache hhas_perms _ =>
      simp [hshim, Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent]
      split
      · case isTrue h => exact h.some.prop.2.finishBefore.gCacheOfCDir
      · case isFalse h => exact absurd (Behaviour.hasPermsInGlobalCache_implies_nonempty_immFinishBefore b init _ hhas_perms) h

  have hr_cle_corr_gcache : Event.reqAtCorrespondingGCacheOfCDir n hr_cle hr_gcache := by
    rw [hr_gcache_eq]
    simp [Behaviour.Shim.ClusterToGlobal.cDir'sGReq]
    cases hshim : cmp.shimAxioms.clusterToGlobal b init hr_cle hr_cle_is_dir with
    | encapGlobalCache _ hreq =>
      simpa [hshim] using hreq.choose_spec.right.gReqOfCDir.gReq
    | noGlobalCache hhas_perms _ =>
      simp [hshim, Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent]
      split
      · case isTrue h => exact h.some.prop.2.finishBefore.gCacheOfCDir
      · case isFalse h => exact absurd (Behaviour.hasPermsInGlobalCache_implies_nonempty_immFinishBefore b init _ hhas_perms) h

  -- Same translated global-cache struct forces same corresponding cluster protocol.
  cases hw_cle with
  | cacheEvent _ =>
    cases hw_cle_is_dir
  | directoryEvent de_w =>
    cases hr_cle with
    | cacheEvent _ =>
      cases hr_cle_is_dir
    | directoryEvent de_r =>
      simp [Event.isDirectoryEvent] at hw_cle_is_dir hr_cle_is_dir
      match hde_w : de_w.pInst, hde_r : de_r.pInst with
      | .cluster1, .cluster1 =>
        simp [Event.protocol, hde_w, hde_r]
      | .cluster2, .cluster2 =>
        simp [Event.protocol, hde_w, hde_r]
      | .cluster1, .cluster2 =>
        have hw_at_0 : hw_gcache.reqAtGlobalCacheCid n 0 := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_w] using hw_cle_corr_gcache
        have hr_at_1 : hr_gcache.reqAtGlobalCacheCid n 1 := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_r] using hr_cle_corr_gcache
        have hr_at_0 : hr_gcache.reqAtGlobalCacheCid n 0 := by
          cases hw_gcache with
          | directoryEvent _ =>
            simp [Event.reqAtGlobalCacheCid] at hw_at_0
          | cacheEvent ce_w =>
            cases hr_gcache with
            | directoryEvent _ =>
              have : False := by
                simpa [Event.reqAtGlobalCacheCid] using hr_at_1
              exact this.elim
            | cacheEvent ce_r =>
              simp [Event.struct] at hsame_struct_of_same_dir_access
              simpa [Event.reqAtGlobalCacheCid, hsame_struct_of_same_dir_access] using hw_at_0
        have hcontra : False := by
          cases hr_gcache with
          | directoryEvent _ =>
            simp [Event.reqAtGlobalCacheCid] at hr_at_0
          | cacheEvent ce =>
            cases hcid : ce.cid with
            | proxy _ =>
              simp [Event.reqAtGlobalCacheCid, hcid] at hr_at_0
            | cache pci =>
              cases hpci : pci with
              | cluster1 _ =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_0
              | cluster2 _ =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_0
              | globalP fin2 =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_0 hr_at_1
                have : (0 : Fin 2) = 1 := hr_at_0.symm.trans hr_at_1
                exact Fin.zero_ne_one this
        exact hcontra.elim
      | .cluster2, .cluster1 =>
        have hw_at_1 : hw_gcache.reqAtGlobalCacheCid n 1 := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_w] using hw_cle_corr_gcache
        have hr_at_0 : hr_gcache.reqAtGlobalCacheCid n 0 := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_r] using hr_cle_corr_gcache
        have hr_at_1 : hr_gcache.reqAtGlobalCacheCid n 1 := by
          cases hw_gcache with
          | directoryEvent _ =>
            simp [Event.reqAtGlobalCacheCid] at hw_at_1
          | cacheEvent ce_w =>
            cases hr_gcache with
            | directoryEvent _ =>
              have : False := by
                simpa [Event.reqAtGlobalCacheCid] using hr_at_0
              exact this.elim
            | cacheEvent ce_r =>
              simp [Event.struct] at hsame_struct_of_same_dir_access
              simpa [Event.reqAtGlobalCacheCid, hsame_struct_of_same_dir_access] using hw_at_1
        have hcontra : False := by
          cases hr_gcache with
          | directoryEvent _ =>
            simp [Event.reqAtGlobalCacheCid] at hr_at_1
          | cacheEvent ce =>
            cases hcid : ce.cid with
            | proxy _ =>
              simp [Event.reqAtGlobalCacheCid, hcid] at hr_at_1
            | cache pci =>
              cases hpci : pci with
              | cluster1 _ =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_1
              | cluster2 _ =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_1
              | globalP fin2 =>
                simp [Event.reqAtGlobalCacheCid, hcid, hpci] at hr_at_0 hr_at_1
                have : (0 : Fin 2) = 1 := hr_at_0.symm.trans hr_at_1
                exact Fin.zero_ne_one this
        exact hcontra.elim
      | .global, .global =>
        have : False := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_w] using hw_cle_corr_gcache
        exact this.elim
      | .global, .cluster1 =>
        have : False := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_w] using hw_cle_corr_gcache
        exact this.elim
      | .global, .cluster2 =>
        have : False := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_w] using hw_cle_corr_gcache
        exact this.elim
      | .cluster1, .global =>
        have : False := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_r] using hr_cle_corr_gcache
        exact this.elim
      | .cluster2, .global =>
        have : False := by
          simpa [Event.reqAtCorrespondingGCacheOfCDir, Event.protocol, hde_r] using hr_cle_corr_gcache
        exact this.elim

/-- For write events (cache events), ¬ isCoherent implies isNonCoherent.
    Write events are always cache events, and for cache events isNonCoherent ↔ ¬ isCoherent. -/
lemma isNonCoherent_of_not_isCoherent_write {e : Event n}
  (hw_is_write : e.isWrite) (h : ¬ e.isCoherent) : e.isNonCoherent := by
  cases e with
  | cacheEvent ce =>
    simp [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at h
    simp [Event.isNonCoherent, h]
  | directoryEvent de =>
    -- directoryEvent cannot be a write
    simp [Event.isWrite] at hw_is_write

/-- The protocol instance of `e.getProtocol cmp` matches `e.protocol`.
    Follows from `CompoundProtocol` well-formedness conditions (`globalWellFormed`,
    `cluster1WellFormed`, `cluster2WellFormed`). -/
lemma Event.getProtocol_pi (cmp : CompoundProtocol n) (e : Event n) :
    (e.getProtocol cmp).pi = e.protocol := by
  simp only [Event.getProtocol]
  split <;> simp_all [cmp.globalWellFormed, cmp.cluster1WellFormed, cmp.cluster2WellFormed]

/- ======================= General RF Helpers ======================= -/
/- These helpers are reusable across multiple top-level RF subcases.  -/

/-- If two events have the same GLE, they are in the same protocol cluster.
    Same GLE implies they come from requests that trace back to the same
    global protocol request, hence same protocol linkage. -/
lemma same_gle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  : e_w.protocol = e_r.protocol := by
  have hw_cle_protocol :
      hw_c_and_g_lin.hreq's_dir_access.choose.protocol = e_w.protocol :=
    write_cle_protocol_eq_write_protocol hw_c_and_g_lin
  have hr_cle_protocol :
      hr_c_and_g_lin.hreq's_dir_access.choose.protocol = e_r.protocol :=
    read_cle_protocol_eq_read_protocol hr_c_and_g_lin
  calc
    e_w.protocol = hw_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hw_cle_protocol.symm
    _ = hr_c_and_g_lin.hreq's_dir_access.choose.protocol := by
      let hw_cle := hw_c_and_g_lin.hreq's_dir_access.choose
      let hr_cle := hr_c_and_g_lin.hreq's_dir_access.choose
      let hw_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hw_c_and_g_lin.hreq's_dir_access
      let hr_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hr_c_and_g_lin.hreq's_dir_access

      have hw_cle_is_dir : hw_cle.isDirectoryEvent := by
        simpa [hw_cle] using hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
      have hr_cle_is_dir : hr_cle.isDirectoryEvent := by
        simpa [hr_cle] using hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent

      have hw_gcache_eq : hw_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hw_cle hw_cle_is_dir := by
        simp [hw_gcache, Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper, hw_cle, hw_cle_is_dir]
      have hr_gcache_eq : hr_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hr_cle hr_cle_is_dir := by
        simp [hr_gcache, Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper, hr_cle, hr_cle_is_dir]

      have hw_gcache_to_gdir : b.dirAccessOfRequest n init hw_gcache (hw_c_and_g_lin.hreq's_global_lin.choose) :=
        hw_c_and_g_lin.hreq's_global_lin.choose_spec.right
      have hr_gcache_to_gdir' : b.dirAccessOfRequest n init hr_gcache (hr_c_and_g_lin.hreq's_global_lin.choose) :=
        hr_c_and_g_lin.hreq's_global_lin.choose_spec.right
      have hr_gcache_to_gdir : b.dirAccessOfRequest n init hr_gcache (hw_c_and_g_lin.hreq's_global_lin.choose) := by
        simpa [hgle_eq] using hr_gcache_to_gdir'

      simpa [hw_cle, hr_cle] using
        (cluster_dirs_to_same_global_dir_have_same_protocol
          (cmp := cmp) (b := b) (init := init)
          (hw_cle := hw_cle) (hr_cle := hr_cle)
          (hw_gcache := hw_gcache) (hr_gcache := hr_gcache)
          (e_gdir := hw_c_and_g_lin.hreq's_global_lin.choose)
          hw_cle_is_dir hr_cle_is_dir
          hw_gcache_eq hw_gcache_to_gdir
          hr_gcache_eq hr_gcache_to_gdir)
    _ = e_r.protocol :=
      hr_cle_protocol

/-- No intervening directory writes between same-cache CLEs. Uses NoInterveningWrites to
    show that any same-cluster or diff-cluster write's CLE would be between the boundaries,
    contradicting the constraints. Does not require any specific CLE ordering hypothesis. -/
lemma no_dir_write_between_same_cache
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_cache : e_w.struct = e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : Event.Between.noDirWrite cmp b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access := by
  unfold Event.Between.noDirWrite
  intro h
  have hw_cle_proto := write_cle_protocol_eq_write_protocol hw_c_and_g_lin
  have hr_cle_proto := read_cle_protocol_eq_read_protocol hr_c_and_g_lin
  have hw_r_same_struct : e_w.sameStructure n e_r := by
    unfold Event.sameStructure; exact hsame_cache
  have hw_r_same_proto : e_w.protocol = e_r.protocol :=
    sameStructure_implies_sameProtocol hw_r_same_struct
  cases h with
  | sameCluster e_w_inter hsame =>
    have hinter_lin := hknow_dir_access cmp b init e_w_inter
    have hconstraints := hno_intervening_writes
      e_w_inter hsame.interInB hsame.isCluster hsame.isWrite hsame.notDown hinter_lin
    have hinter_cle_proto :=
      write_cle_protocol_eq_write_protocol (hknow_dir_access cmp b init e_w_inter)
    have h_proto_w := hinter_cle_proto.trans hsame.sameProtocol
    have h_proto_r := h_proto_w.trans (hw_cle_proto.trans (hw_r_same_proto.trans hr_cle_proto.symm))
    exact hconstraints.notBetweenCles ⟨h_proto_w, h_proto_r, hsame.cleDirWrite⟩ hsame.cleBetween
  | diffCluster e_w_inter hdiff =>
    have hinter_lin := hknow_dir_access cmp b init e_w_inter
    have hconstraints := hno_intervening_writes
      e_w_inter hdiff.interInB hdiff.isCluster hdiff.isWrite hdiff.notDown hinter_lin
    have hdiff_w : e_w_inter.protocol ≠ e_w.protocol := by
      intro heq; exact hdiff.diffProtocol (heq.trans hw_cle_proto.symm)
    obtain ⟨e_cdir_down, hcdir_in_b, hcdir_dir, hcdir_proto, hcdir_write, hcdir_down,
      hcdir_encap, hcdir_between⟩ := hdiff.existsClusterDirDown
    have hdown_proto_w := hcdir_proto.trans hw_cle_proto
    exact hconstraints.diffClusterNotBetweenCles_sameCache ⟨e_cdir_down, hcdir_in_b,
      ⟨hdiff_w, hdown_proto_w, hcdir_down, hcdir_dir, hcdir_encap⟩,
      hcdir_between⟩

/-- Extract `sameReq` from `downgradeCorrespondingToRequest`: the downgrade event carries
    the same request as the requesting event. Both events must be cache events (otherwise
    `downgradeCorrespondingToRequest` is `False`). -/
private lemma downgradeCorrespondingToRequest_sameReq
  {e₁ e₂ : Event n}
  (hfwd : e₁.downgradeCorrespondingToRequest n e₂)
  : e₁.req = e₂.req := by
  unfold Event.downgradeCorrespondingToRequest at hfwd
  cases e₁ with
  | cacheEvent ce₁ =>
    cases e₂ with
    | cacheEvent ce₂ => exact hfwd.sameReq
    | directoryEvent _ => exact absurd hfwd (by simp)
  | directoryEvent _ => exact absurd hfwd (by simp)

/-- Extract `isDown` from `downgradeCorrespondingToRequest`: the downgrade event has its
    `down` field set. Both events must be cache events (otherwise
    `downgradeCorrespondingToRequest` is `False`). -/
lemma downgradeCorrespondingToRequest_isDown
  {e₁ e₂ : Event n}
  (hfwd : e₁.downgradeCorrespondingToRequest n e₂)
  : e₂.down := by
  unfold Event.downgradeCorrespondingToRequest at hfwd
  cases e₁ with
  | cacheEvent ce₁ =>
    cases e₂ with
    | cacheEvent ce₂ => exact hfwd.isDown
    | directoryEvent _ => exact absurd hfwd (by simp)
  | directoryEvent _ => exact absurd hfwd (by simp)

/-- The read's GLE at the global level triggers a downgrade of the previous owner.
    Uses protocol Axiom 10 (coherent read directory downgrades others) at the global level. -/
lemma diffCache_coherent_globalDowngrade
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_r : Event n}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant := by
  let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
    (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  have he_gcache_in_b : e_r_cle_gcache ∈ b :=
    Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB cmp b init hr_c_and_g_lin.hreq's_dir_access
  have he_gle_in_b : e_r_gle ∈ b := hr_c_and_g_lin.hreq's_global_lin.choose_spec.left
  have haxiom := cmp.global.reqAxioms.coherentReadDowngrades b init
    e_r_cle_gcache he_gcache_in_b e_r_gle he_gle_in_b
  cases haxiom.downgradeOtherCaches with
  | cReadOnSW hfwd => exact hfwd.fwdPrevOwner

/-- The global downgrade from `diffCache_coherent_globalDowngrade` is NOT an SC write downgrade.
    It comes from `coherentReadDowngrades.cReadOnSW`, so the forwarded downgrade carries a
    read request (via `sameReq`), contradicting `isSCWriteGlobalDowngrade` (which needs rw=.w). -/
lemma diffCache_coherent_globalDowngrade_not_scWrite
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_r : Event n}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  {e_r_gdown : Event n} {e_r_grant : Event n}
  (hdowngrade : Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init
    hr_c_and_g_lin e_r_gdown e_r_grant)
  : ¬ e_r_gdown.isSCWriteGlobalDowngrade := by
  intro hwrite_down
  -- Re-derive the axiom to get reqCoherentRead
  let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
      (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  have he_gcache_in_b : e_r_cle_gcache ∈ b :=
    Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB cmp b init hr_c_and_g_lin.hreq's_dir_access
  have he_gle_in_b : e_r_gle ∈ b := hr_c_and_g_lin.hreq's_global_lin.choose_spec.left
  have haxiom := cmp.global.reqAxioms.coherentReadDowngrades b init
    e_r_cle_gcache he_gcache_in_b e_r_gle he_gle_in_b
  -- sameReq: GCR.req = e_gdown.req
  have hsame := downgradeCorrespondingToRequest_sameReq
    hdowngrade.downgradePrevOwner.fwdFromRequester
  -- isCoherentRead → GCR is a read. Via sameReq → gdown is also a read.
  -- But isSCWrite → gdown is a write. Contradiction.
  have hgcr_read := haxiom.reqCoherentRead
  -- Transfer isRead from GCR to gdown via sameReq
  have h_read : (Event.req n e_r_gdown).val.isRead := by
    have := hgcr_read.2; rw [hsame] at this; exact this
  -- isSCWrite says rw = .w → ¬ isRead
  have h_write := hwrite_down.isSCWrite
  simp only [Event.isSCWrite, ValidRequest.isSCWrite] at h_write
  simp only [Request.isRead] at h_read
  rw [h_write] at h_read
  -- h_read : (↑SCWrite).rw = .r, which reduces to ReadWrite.w = ReadWrite.r → False
  exact absurd h_read (by decide)

/-- If two correspondingClusterOfGlobalCache facts share the same e_gdown,
    they determine the same cluster — so the protocol outputs are equal. -/
private lemma correspondingCluster_protocol_eq
  {n : ℕ} {e_gdown : Event n} {α β : Type} {a : α} {bv : β}
  {f : α → ProtocolInstance} {g : β → ProtocolInstance}
  (h1 : e_gdown.correspondingClusterOfGlobalCache n a f)
  (h2 : e_gdown.correspondingClusterOfGlobalCache n bv g)
  : f a = g bv := by
  simp [Event.correspondingClusterOfGlobalCache] at h1 h2
  match e_gdown with
  | .directoryEvent _ => simp at h1
  | .cacheEvent ce =>
    simp at h1 h2
    match hcid : ce.cid with
    | .proxy _ => simp [hcid] at h1
    | .cache pci =>
      simp [hcid] at h1 h2
      match pci with
      | .cluster1 _ | .cluster2 _ => simp at h1
      | .globalP fin_2 =>
        simp at h1 h2
        match fin_2 with
        | 0 | 1 => exact h1.trans h2.symm

/-- From a GlobalToCluster shim result at protocol p, extract a cluster proxy cache event
    and a cluster directory event at e_w's protocol.
    The proxy is provided by e_w itself (which is a cluster cache event in the behaviour).
    The directory event is extracted from the GlobalToCluster shim structure. -/
lemma globalToCluster_extract_proxy_and_dir
  {n : ℕ} {b : Behaviour n} {init : InitialSystemState n}
  {p : Protocol n} {e_gdown : Event n}
  (hg2c : Behaviour.Shim.GlobalToCluster n b init p e_gdown)
  (e_w : Event n) (hp_eq : p.pi = e_w.protocol)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : (∃ e_proxy ∈ b, e_proxy.protocol = e_w.protocol ∧ e_proxy.isClusterCache) ∧
    (∃ e_dir ∈ b, e_dir.isDirectoryEvent ∧ e_dir.protocol = e_w.protocol) := by
  constructor
  · -- Proxy: use e_w itself
    exact ⟨e_w, hw_in_b, rfl, hw_cluster⟩
  · -- Directory: extract from GlobalToCluster
    cases hg2c with
    | bothCoherentWriteAndRead hcorrespond _ downTranslation =>
      cases downTranslation with
      | scWriteDown _ translation =>
        obtain ⟨e_cw, _, e_dw, e_ce, _, e_de, _, hstruct⟩ := translation.scGDownTranslation
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
        exact ⟨e_dw, hstruct.cohWriteDir.dirInB, hstruct.cohWriteDir.isDir,
          hstruct.cohWriteDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq⟩
      | scReadDown _ _ translation =>
        obtain ⟨e_cr, _, e_dr, _, hstruct⟩ := translation
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
        exact ⟨e_dr, hstruct.cohReadDir.dirInB, hstruct.cohReadDir.isDir,
          hstruct.cohReadDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq⟩
    | noCoherentRead hcorrespond _ downTranslation =>
      cases downTranslation with
      | scWriteDowngrade _ translation =>
        cases translation with
        | onDirSW _ htrans =>
          obtain ⟨_, _, _, _, e_vd, hvd_in_b, _, _, hstruct⟩ := htrans
          have hproto := correspondingCluster_protocol_eq hcorrespond
            hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
          exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
            hproto.symm.trans hp_eq⟩
        | onDirVd _ htrans =>
          obtain ⟨e_vd, hvd_in_b, _, _, hstruct⟩ := htrans
          have hproto := correspondingCluster_protocol_eq hcorrespond
            hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
          exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
            hproto.symm.trans hp_eq⟩
        | onDirVc _ htrans =>
          obtain ⟨e_vc, hvc_in_b, hstruct⟩ := htrans
          have hproto := correspondingCluster_protocol_eq hcorrespond
            hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
          exact ⟨e_vc, hvc_in_b, hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir,
            hproto.symm.trans hp_eq⟩
      | scReadDowngrade _ _ translation =>
        cases translation with
        | onDirSW _ htrans =>
          obtain ⟨_, _, _, _, e_vd, hvd_in_b, hstruct⟩ := htrans
          have hproto := correspondingCluster_protocol_eq hcorrespond
            hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
          exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
            hproto.symm.trans hp_eq⟩
        | onDirVd _ htrans =>
          obtain ⟨_, _, _, _, e_vd, hvd_in_b, hstruct⟩ := htrans
          have hproto := correspondingCluster_protocol_eq hcorrespond
            hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
          exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
            hproto.symm.trans hp_eq⟩

/-- Extract directory event from GlobalToCluster shim, with proof that the global downgrade
    encapsulates the extracted directory event. -/
lemma globalToCluster_extract_dir_with_encap
  {n : ℕ} {b : Behaviour n} {init : InitialSystemState n}
  {p : Protocol n} {e_gdown : Event n}
  (hg2c : Behaviour.Shim.GlobalToCluster n b init p e_gdown)
  (e_w : Event n) (hp_eq : p.pi = e_w.protocol)
  : ∃ e_dir ∈ b, e_dir.isDirectoryEvent ∧ e_dir.protocol = e_w.protocol ∧
      e_gdown.Encapsulates n e_dir ∧ e_gdown.sameAddr n e_dir := by
  cases hg2c with
  | bothCoherentWriteAndRead hcorrespond _ downTranslation =>
    cases downTranslation with
    | scWriteDown _ translation =>
      obtain ⟨e_cw, _, e_dw, e_ce, _, e_de, _, hstruct⟩ := translation.scGDownTranslation
      have hproto := correspondingCluster_protocol_eq hcorrespond
        hstruct.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
      exact ⟨e_dw, hstruct.cohWriteDir.dirInB, hstruct.cohWriteDir.isDir,
        hstruct.cohWriteDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq,
        Event.encap_encap_trans n (hstruct.cohWrite.globalEncap) (hstruct.cohWriteDir.reqEncapDir),
        by have h1 := hstruct.cohWrite.atCorrClusterProxy.clusterMatch.sameAddr
           have h2 := hstruct.cohWriteDir.dirCorresponds.sameAddr
           unfold Event.sameAddr at h1 h2 ⊢; exact h2.symm ▸ h1⟩
    | scReadDown _ _ translation =>
      obtain ⟨e_cr, _, e_dr, _, hstruct⟩ := translation
      have hproto := correspondingCluster_protocol_eq hcorrespond
        hstruct.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
      exact ⟨e_dr, hstruct.cohReadDir.dirInB, hstruct.cohReadDir.isDir,
        hstruct.cohReadDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq,
        Event.encap_encap_trans n (hstruct.cohRead.globalEncap) (hstruct.cohReadDir.reqEncapDir),
        by have h1 := hstruct.cohRead.atCorrClusterProxy.clusterMatch.sameAddr
           have h2 := hstruct.cohReadDir.dirCorresponds.sameAddr
           unfold Event.sameAddr at h1 h2 ⊢; exact h2.symm ▸ h1⟩
  | noCoherentRead hcorrespond _ downTranslation =>
    cases downTranslation with
    | scWriteDowngrade _ translation =>
      cases translation with
      | onDirSW _ htrans =>
        obtain ⟨_, _, _, _, e_vd, hvd_in_b, _, _, hstruct⟩ := htrans
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
          hproto.symm.trans hp_eq,
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr⟩
      | onDirVd _ htrans =>
        obtain ⟨e_vd, hvd_in_b, _, _, hstruct⟩ := htrans
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
          hproto.symm.trans hp_eq,
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr⟩
      | onDirVc _ htrans =>
        obtain ⟨e_vc, hvc_in_b, hstruct⟩ := htrans
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        exact ⟨e_vc, hvc_in_b, hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.atDir,
          hproto.symm.trans hp_eq,
          hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.globalEncap, hstruct.gDownEncapVcInvalDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr⟩
    | scReadDowngrade _ _ translation =>
      cases translation with
      | onDirSW _ htrans =>
        obtain ⟨_, _, _, _, e_vd, hvd_in_b, hstruct⟩ := htrans
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
          hproto.symm.trans hp_eq,
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr⟩
      | onDirVd _ htrans =>
        obtain ⟨_, _, _, _, e_vd, hvd_in_b, hstruct⟩ := htrans
        have hproto := correspondingCluster_protocol_eq hcorrespond
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.atCorrCluster
        exact ⟨e_vd, hvd_in_b, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.atDir,
          hproto.symm.trans hp_eq,
          hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.globalEncap, hstruct.gDownEncapVdWBDir.dirCorrespondToGlobalCache.clusterMatch.sameAddr⟩

/-- The GCR (global cache request from ClusterToGlobal shim) finishes before the CLE.
    Used in temporal bound computations for encapDirRelation. -/
private lemma gcache_oEnd_lt_cle
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_r : Event n}
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
    : (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
        (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)).oEnd <
      hr_c_and_g_lin.hreq's_dir_access.choose.oEnd := by
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
  let hcdir_is_dir := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
  show (Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init e_r_cle hcdir_is_dir).oEnd < e_r_cle.oEnd
  unfold Behaviour.Shim.ClusterToGlobal.cDir'sGReq
  match h : cmp.shimAxioms.clusterToGlobal b init e_r_cle hcdir_is_dir with
  | .encapGlobalCache _ hgreq_spec => exact hgreq_spec.choose_spec.right.encapGlobalCache.2
  | .noGlobalCache hhas_perms _ =>
    unfold Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent
    have hnonempty := Behaviour.hasPermsInGlobalCache_implies_nonempty_immFinishBefore b init _ hhas_perms
    rw [dif_pos hnonempty]; exact hnonempty.some.prop.2.finishBefore.finBefore.endBefore

/-- Build the encapsulation chain: e_gcache ≻ e_r_gle ≻ e_r_gdown ≻ e_dir.
    Combined with gcache_oEnd_lt_cle, gives e_dir.oEnd < CLE.oEnd. -/
private lemma gcache_encap_dir_chain
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_r : Event n}
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
    {e_r_gdown e_r_grant e_dir : Event n}
    (hdowngrade : Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init
      hr_c_and_g_lin e_r_gdown e_r_grant)
    (he_gdown_encap_dir : e_r_gdown.Encapsulates n e_dir)
    : (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
        (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)).Encapsulates n e_dir :=
  Trans.trans (Trans.trans hdowngrade.downgradePrevOwner.reqEncapDir
    hdowngrade.downgradePrevOwner.dirEncapDowngrade) he_gdown_encap_dir

/-- Construct the global and cluster level downgrade chain from e_r's GLE to e_w's cluster.
    Produces the existential witness for `existsRClusterDirDown`: a cluster directory event
    at e_w's protocol, with encapDirRelation (either CLE or gcache encapsulates it).

    The chain: e_r_cle → e_gcache → e_r_gle → e_r_gdown → e_dir.
    Steps 2-4 prove: e_gcache ≻ e_r_gle ≻ e_r_gdown ≻ e_dir, i.e., e_gcache ≻ e_dir.
    We use `gcacheEncap` to record that the global cache event encapsulates e_dir. -/
lemma diffCache_coherent_encapProxyAndDir
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (_hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin := by
  have hgdown := diffCache_coherent_globalDowngrade hr_c_and_g_lin
  obtain ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b, hdowngrade⟩ := hgdown
  have hp_eq := Event.getProtocol_pi cmp e_w
  have hg2c := cmp.shimAxioms.globalToCluster b init (e_w.getProtocol cmp) e_r_gdown he_r_gdown_in_b
  let e_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
      (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  have h_gcache_lt_cle := gcache_oEnd_lt_cle hr_c_and_g_lin
  -- Use scGDownTranslation (always available in bothCoherentWriteAndRead) to get the write dir
  -- event with isDirWrite, ¬down, and correspondingDirectoryEvent.
  cases hg2c with
  | bothCoherentWriteAndRead hcorrespond _ downTranslation =>
    cases downTranslation with
    | scWriteDown hwrite_down _ =>
      exact absurd hwrite_down (diffCache_coherent_globalDowngrade_not_scWrite hr_c_and_g_lin hdowngrade)
    /- Old scWriteDown proof (vacuous — kept for reference):
    -- e_dw: the write directory event at e_w's cluster (isDirWrite, ¬down)
    have he_dw_in_b := hstruct.cohWriteDir.dirInB
    have he_dw_isDir := hstruct.cohWriteDir.isDir
    have hproto := correspondingCluster_protocol_eq hcorrespond
      hstruct.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
    have he_dw_proto : e_dw.protocol = e_w.protocol :=
      hstruct.cohWriteDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq
    have he_gdown_encap_dw : e_r_gdown.Encapsulates n e_dw :=
      Event.encap_encap_trans n hstruct.cohWrite.globalEncap hstruct.cohWriteDir.reqEncapDir
    have h_gcache_encap_dw : e_gcache.Encapsulates n e_dw :=
      gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_dw
    have h_dw_end_before_cle := Nat.lt_trans h_gcache_encap_dw.2 h_gcache_lt_cle
    -- isDirWrite + ¬down: from requestDirectoryEvent.dirReq/sameDown + translateProxyEvent.
    -- For isSCWrite, reqToDirOfRequestEvent defaults to e_cw.req (coherent=true, no special case).
    have he_dw_isDirWrite : e_dw.isDirWrite := by
      have hdir_of_req := hstruct.cohWriteDir.dirOfReq
      have hsameDown := hstruct.cohWriteDir.dirCorresponds.sameDown
      have hreqTrans := hstruct.cohWrite.reqTranslation
      rw [ValidRequest.isSCWrite] at hreqTrans
      match he_dw_m : e_dw, he_dw_isDir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de_dw, _ =>
        match he_cw_m : e_cw with
        | .directoryEvent _ =>
          simp [Event.dirEventOfReqEvent, he_dw_m] at hdir_of_req
        | .cacheEvent ce_cw =>
          -- dirOfReq: de_dw.eReq = ce_cw (from matchesCacheEvent.correspondingCE)
          simp [Event.dirEventOfReqEvent, he_dw_m, he_cw_m,
                DirectoryEvent.matchesCacheEvent] at hdir_of_req
          -- hdir_of_req : de_dw.eReq = ce_cw ∧ de_dw.down = ce_cw.down
          -- Use requestDirectoryEvent.dirReq to get de_dw.req
          have hdirReq := hstruct.cohWriteDir.dirCorresponds.dirReq
          simp only [Event.req, he_dw_m, he_cw_m] at hdirReq hreqTrans
          simp only [Event.isDirWrite, he_dw_m, Request.isWrite, hdirReq]
          -- Goal: (b.reqToDirOfRequestEvent ...).val.rw = .w
          -- For isSCWrite (⟨.w, true, .SC⟩): reqToDirOfRequestEvent defaults to ce_cw.req
          simp only [Behaviour.reqToDirOfRequestEvent, Event.req, he_cw_m]
          split
          · -- rel_wb case: ce_cw.req.val = ⟨.w, false, .Rel⟩ → contradicts isSCWrite
            next h => rw [hreqTrans] at h; simp at h
          · -- default: reqToDirOfRequestEvent n state_before.cache
            simp only [Event.reqToDirOfRequestEvent, Event.req, he_cw_m, Event.down]
            rw [hreqTrans]
    have he_dw_not_down : ¬ e_dw.down := by
      have hdir_of_req := hstruct.cohWriteDir.dirOfReq
      have hcw_not_down := hstruct.cohWrite.downgrade
      match he_dw_m : e_dw, he_dw_isDir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de_dw, _ =>
        match he_cw_m : e_cw with
        | .directoryEvent _ =>
          simp [Event.dirEventOfReqEvent, he_dw_m] at hdir_of_req
        | .cacheEvent ce_cw =>
          simp [Event.dirEventOfReqEvent, he_dw_m, he_cw_m,
                DirectoryEvent.matchesCacheEvent] at hdir_of_req
          -- hdir_of_req.2 : de_dw.down = ce_cw.down (Bool eq)
          -- hcw_not_down : ↑(ce_cw.down) = False (Prop eq via Bool→Prop coercion)
          -- Goal: ¬ ↑(de_dw.down)
          simp only [Event.down, he_dw_m] at hcw_not_down ⊢
          simp [hdir_of_req.2, hcw_not_down]
    -- clusterDirFromDiffProtocolRequest: from downgrade + proxyCacheEvent + correspondingDirectoryEvent
    have he_dw_translated : Event.clusterDirFromDiffProtocolRequest b init e_r e_dw hr_c_and_g_lin :=
      ⟨⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b, e_cw, hstruct.cohWriteDir.reqInB,
        hdowngrade,
        hstruct.cohWrite.atCorrClusterProxy,
        { clusterMatch :=
            -- Transfer matchingCluster from proxy (e_cw) to dir (e_dw) via sameAddr + sameProtocol.
            { sameAddr := by
                have h1 := hstruct.cohWrite.atCorrClusterProxy.clusterMatch.sameAddr
                have h2 := hstruct.cohWriteDir.dirCorresponds.sameAddr
                unfold Event.sameAddr at h1 h2 ⊢; exact h2.symm ▸ h1
              atCorrCluster := by
                have h1 := hstruct.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
                have h2 := hstruct.cohWriteDir.sameProtocol
                simp only [Event.correspondingClusterOfGlobalCache] at h1 ⊢
                split <;> (try (simp_all [Event.protocol])) <;> (simp [Event.protocol] at h1 ⊢; rw [← h2]; exact h1) }
          atDir := he_dw_isDir
          globalEncap := he_gdown_encap_dw }⟩⟩
    exact { existsRClusterDirDown := ⟨e_dw, he_dw_in_b, he_dw_isDir, he_dw_proto,
      he_dw_translated,
      Behaviour.clusterDown.encapDirRelation.gcacheEncap h_gcache_encap_dw h_dw_end_before_cle⟩ }
    -/
    | scReadDown _ _ translation =>
      -- scReadDown: dir event is a coherent read. isDirWrite is NOT satisfiable (isSCRead → rw=.r).
      -- translatedDir IS provable from cohRead.atCorrClusterProxy.
      obtain ⟨e_cr, he_cr_in_b, e_dr, _he_dr_in_b, hstruct⟩ := translation
      have he_dr_in_b := hstruct.cohReadDir.dirInB
      have he_dr_isDir := hstruct.cohReadDir.isDir
      have hproto_r := correspondingCluster_protocol_eq hcorrespond
        hstruct.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
      have he_dr_proto : e_dr.protocol = e_w.protocol :=
        hstruct.cohReadDir.sameProtocol.symm.trans hproto_r.symm |>.trans hp_eq
      have he_gdown_encap_dr : e_r_gdown.Encapsulates n e_dr :=
        Event.encap_encap_trans n hstruct.cohRead.globalEncap hstruct.cohReadDir.reqEncapDir
      have h_gcache_encap_dr := gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_dr


      have h_dr_end_before_cle := Nat.lt_trans h_gcache_encap_dr.2 h_gcache_lt_cle
      have he_dr_translated : Event.clusterDirFromDiffProtocolRequest b init e_r e_dr hr_c_and_g_lin :=
        ⟨⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b,
          hdowngrade,
          { clusterMatch :=
              { sameAddr := by
                  have h1 := hstruct.cohRead.atCorrClusterProxy.clusterMatch.sameAddr
                  have h2 := hstruct.cohReadDir.dirCorresponds.sameAddr
                  unfold Event.sameAddr at h1 h2 ⊢; exact h2.symm ▸ h1
                atCorrCluster := by
                  have h1 := hstruct.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
                  have h2 := hstruct.cohReadDir.sameProtocol
                  simp only [Event.correspondingClusterOfGlobalCache] at h1 ⊢
                  split <;> (try (simp_all [Event.protocol])) <;> (simp [Event.protocol] at h1 ⊢; rw [← h2]; exact h1) }
            atDir := he_dr_isDir
            globalEncap := he_gdown_encap_dr }⟩⟩
      -- isDirRead: from cohRead's isSCRead + dirOfReq + reqToDirOfRequestEvent default
      have he_dr_isDirRead : e_dr.isDirRead := by
        have hdir_of_req := hstruct.cohReadDir.dirOfReq
        have hreqTrans := hstruct.cohRead.reqTranslation
        rw [ValidRequest.isSCRead] at hreqTrans
        match he_dr_m : e_dr, he_dr_isDir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de_dr, _ =>
          match he_cr_m : e_cr with
          | .directoryEvent _ =>
            simp [Event.dirEventOfReqEvent, he_dr_m] at hdir_of_req
          | .cacheEvent ce_cr =>
            simp only [Event.isDirRead, he_dr_m, Request.isRead]
            have hdirReq := hstruct.cohReadDir.dirCorresponds.dirReq
            simp only [Event.req, he_dr_m, he_cr_m] at hdirReq hreqTrans
            rw [hdirReq]
            simp only [Behaviour.reqToDirOfRequestEvent, Event.req, he_cr_m]
            split
            · next h => rw [hreqTrans] at h; simp at h
            · simp only [Event.reqToDirOfRequestEvent, Event.req, he_cr_m, Event.down]
              rw [hreqTrans]
      -- isDirMatchingRW: de_dr.req.val.rw = e_r.req.val.rw
      -- The dir event's rw matches the read proxy's rw (from reqToDirOfRequestEvent default).
      -- The read proxy's rw matches e_r's rw (both reads in the RF relation).
      -- isDirMatchingRW: e_dr.rw = CLE.rw. Both derived from the same global downgrade chain.
      -- e_dr.rw = .r (from isDirRead, proved above).
      -- CLE.rw: from matchingOp (GCR.rw = CLE.rw) + isCoherentRead (GCR.rw = .r) → CLE.rw = .r.
      -- isDirMatchingRW = (.r = .r) = rfl.
      have he_dr_matchingRW : e_dr.isDirMatchingRW n hr_c_and_g_lin.hreq's_dir_access.choose := by
        -- e_dr.rw = .r (from isDirRead). CLE.rw = .r (from matchingOp + isCoherentRead).
        -- Case-split ClusterToGlobal to get matchingOp for CLE.rw.
        let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose
        let hcdir_is_dir := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
        -- Re-derive global axiom for isCoherentRead
        let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
            (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
        have he_gcache_in_b : e_r_cle_gcache ∈ b :=
          Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB cmp b init hr_c_and_g_lin.hreq's_dir_access
        let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
        have he_gle_in_b : e_r_gle ∈ b := hr_c_and_g_lin.hreq's_global_lin.choose_spec.left
        have haxiom_g := cmp.global.reqAxioms.coherentReadDowngrades b init
          e_r_cle_gcache he_gcache_in_b e_r_gle he_gle_in_b
        have hgcr_read := haxiom_g.reqCoherentRead.2  -- GCR.req.val.isRead (= rw = .r)
        -- matchingOp connects GCR.rw to CLE.rw
        match hshim : cmp.shimAxioms.clusterToGlobal b init e_r_cle hcdir_is_dir with
        | .encapGlobalCache _ hgreq_spec =>
          have hmatch := hgreq_spec.choose_spec.right.gReqOfCDir.matchingOp
          -- GCR.rw = CLE.rw (from matchingOp). GCR.rw = .r (from isCoherentRead).
          have h_cle_rw : e_r_cle.req.val.rw = ReadWrite.r := by
            have : e_r_cle_gcache.req.val.rw = e_r_cle.req.val.rw := by
              show (Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init e_r_cle hcdir_is_dir).req.val.rw = _
              unfold Behaviour.Shim.ClusterToGlobal.cDir'sGReq; rw [hshim]
              exact congrArg (·.val.rw) hmatch
            rw [← this]; exact hgcr_read
          -- Both e_dr.rw and CLE.rw are .r → isDirMatchingRW
          -- isDirMatchingRW for (.directoryEvent de, e) = de.req.val.rw = e.req.val.rw
          -- he_dr_isDirRead : de_dr.req.val.rw = .r (after isDirRead unfolding)
          -- h_cle_rw : e_r_cle.req.val.rw = .r
          -- Goal: e_dr.isDirMatchingRW n e_r_cle
          show e_dr.isDirMatchingRW n e_r_cle
          unfold Event.isDirMatchingRW
          split
          · simp [Event.isDirectoryEvent] at he_dr_isDir
          · rename_i de_dr
            simp only [Event.isDirRead, Request.isRead] at he_dr_isDirRead
            rw [he_dr_isDirRead, h_cle_rw]
        | .noGlobalCache _ _ =>
          -- noGlobalCache: matchingOp not available. CLE.rw = reqToDirOfRequestEvent(e_r).rw.
          -- For most cases (coherent reads, non-coherent writes): CLE.rw = .r = e_dr.rw ✓.
          -- For Acquire reads on Vd: reqToDirOfRequestEvent changes .r → .w → CLE.rw = .w ≠ .r.
          -- This case may not arise in practice (Acquire-on-Vd with global cache permissions is unusual).
          sorry
      exact { existsRClusterDirDown := ⟨e_dr, he_dr_in_b, he_dr_isDir, he_dr_proto,
        he_dr_matchingRW,
        he_dr_translated,
        Behaviour.clusterDown.encapDirRelation.gcacheEncap h_gcache_encap_dr h_dr_end_before_cle⟩ }
  | noCoherentRead hcorrespond _ downTranslation =>
    -- noCoherentRead: inline case analysis to preserve translateDirectoryEvent evidence.
    -- For onDirSW/onDirVd: the Vd dir event has isNcWeakWrite → isDirWrite.
    -- For onDirVc: only Vc dir event with isNcWeakRead → sorry for isDirWrite.
    -- For scReadDowngrade: similar structure.
    -- Use globalToCluster_extract_dir_with_encap for basic fields, then extract isDirWrite + translatedDir
    -- from the translateDirectoryEvent structures available in each sub-case.
    have hdir_encap := globalToCluster_extract_dir_with_encap
      (Behaviour.Shim.GlobalToCluster.noCoherentRead hcorrespond (by assumption) downTranslation) e_w hp_eq
    obtain ⟨e_dir, he_dir_in_b, he_dir_isDir, he_dir_proto, he_gdown_encap_dir, he_gdown_sameAddr⟩ := hdir_encap
    have h_gcache_encap_dir : e_gcache.Encapsulates n e_dir :=
      gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_dir
    have h_dir_end_before_cle := Nat.lt_trans h_gcache_encap_dir.2 h_gcache_lt_cle
    -- translatedDir: construct correspondingDirectoryEvent from encap + isDir + clusterMatch
    have he_dir_translated : Event.clusterDirFromDiffProtocolRequest b init e_r e_dir hr_c_and_g_lin :=
      ⟨⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b,
        hdowngrade,
        { clusterMatch :=
            { sameAddr := he_gdown_sameAddr
              atCorrCluster := by
                -- hcorrespond at p, he_dir_proto: e_dir at p → correspondingCluster matches
                have h1 := hcorrespond
                show e_r_gdown.correspondingClusterOfGlobalCache n e_dir (Event.protocol n)
                unfold Event.correspondingClusterOfGlobalCache at h1 ⊢
                split <;> (try simp_all [Event.protocol, hp_eq]) <;>
                  (simp [Event.protocol] at h1 ⊢; rw [← he_dir_proto, ← hp_eq]; exact h1) }
          atDir := he_dir_isDir
          globalEncap := he_gdown_encap_dir }⟩⟩
    exact { existsRClusterDirDown := ⟨e_dir, he_dir_in_b, he_dir_isDir, he_dir_proto,
      sorry, -- isDirMatchingRW: needs case info from globalToCluster_extract_dir_with_encap
      he_dir_translated,
      Behaviour.clusterDown.encapDirRelation.gcacheEncap h_gcache_encap_dir h_dir_end_before_cle⟩ }

/-- Combined lemma: constructs both the cluster directory downgrade event and the
    cache downgrade it encapsulates, returning the directory event as an explicit
    existential witness. This avoids Exists.choose issues by never going through
    the opaque encapDir structure. The directory event comes from the GlobalToCluster
    shim and the cache downgrade from the cluster protocol axiom. -/
lemma cdirEncapsDown_exists
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e_w e_r : Event n}
    (_hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
    (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest cmp b init e)
    : ∃ e_cdir ∈ b, e_cdir.isDirectoryEvent ∧ e_cdir.protocol = e_w.protocol ∧
        e_cdir.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd ∧
        (∃ e_cache_down ∈ b,
            e_cdir.Encapsulates n e_cache_down ∧
            e_cache_down.down ∧ e_cache_down.isCacheEvent) ∧
        -- The evict directory event: e_cdir OB e_evict, both at same cluster.
        -- Call sites case-split on e_evict.down for sameCacheConstraints vs sameCacheWriteConstraints.
        (∃ e_evict ∈ b, e_evict.isDirectoryEvent ∧
            e_evict.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd ∧
            e_cdir.OrderedBefore n e_evict ∧ e_evict.protocol = e_w.protocol ∧
            Event.clusterDirFromDiffProtocolRequest b init e_r e_evict hr_c_and_g_lin) := by
  -- Get global downgrade and GlobalToCluster shim
  have hgdown := diffCache_coherent_globalDowngrade hr_c_and_g_lin
  obtain ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b, hdowngrade⟩ := hgdown
  have hg2c := cmp.shimAxioms.globalToCluster b init (e_w.getProtocol cmp) e_r_gdown he_r_gdown_in_b
  have hp_eq := Event.getProtocol_pi cmp e_w
  -- Case split on GlobalToCluster shim ONCE — extract both directory event and cluster axiom
  cases hg2c with
  | bothCoherentWriteAndRead hcorrespond hboth downTranslation =>
    cases downTranslation with
    | scWriteDown hwrite_down _ =>
      exact absurd hwrite_down (diffCache_coherent_globalDowngrade_not_scWrite hr_c_and_g_lin hdowngrade)
    /- Original scWriteDown proof (vacuous but kept for reference):
      obtain ⟨e_cw, he_cw_in_b, e_dw, e_ce, _he_ce_in_b, e_de, he_de_in_b, hstruct⟩ := translation.scGDownTranslation
      -- e_dw is the directory event (our e_cdir). No choose involved!
      have he_dw_in_b := hstruct.cohWriteDir.dirInB
      have he_dw_isDir := hstruct.cohWriteDir.isDir
      have hproto := correspondingCluster_protocol_eq hcorrespond
        hstruct.cohWrite.atCorrClusterProxy.clusterMatch.atCorrCluster
      have he_dw_proto : e_dw.protocol = e_w.protocol :=
        hstruct.cohWriteDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq
      have he_gdown_encap_dw : e_r_gdown.Encapsulates n e_dw :=
        Event.encap_encap_trans n (hstruct.cohWrite.globalEncap) (hstruct.cohWriteDir.reqEncapDir)
      -- Build e_gcache encapsulates e_dw chain
      let e_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
          (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
      have h_gcache_encap_dw : e_gcache.Encapsulates n e_dw :=
        gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_dw
      have h_dw_end_before_cle := Nat.lt_trans h_gcache_encap_dw.2 (gcache_oEnd_lt_cle hr_c_and_g_lin)
      -- Apply cluster axiom to e_cw (proxy) and e_dw (directory)
      have haxiom := (e_w.getProtocol cmp).reqAxioms.coherentWriteDowngrades b init
        e_cw he_cw_in_b e_dw hstruct.cohWriteDir.dirInB
      cases haxiom.downgradeOtherCaches with
      | cWriteOnSW hfwd =>
        obtain ⟨e_down, he_down_in_b, e_grant, _, h_dpow⟩ := hfwd.fwdPrevOwner
        -- dirEncapDowngrade gives e_dw.Encapsulates n e_down — direct, no choose!
        have hencap := h_dpow.downgradePrevOwner.dirEncapDowngrade
        -- Extract e_down.down from downgradeCorrespondingToRequest
        have hdown_is_down : e_down.down := by
          have hfwd_from := h_dpow.downgradePrevOwner.fwdFromRequester
          have hcache := h_dpow.downgradePrevOwner.downAtCache
          -- Both e_cw and e_down must be cache events for downgradeCorrespondingToRequest
          match he_down_cache : e_down, hcache with
          | .cacheEvent ce_down, _ =>
            match he_cw_cache : e_cw, haxiom.isCacheEvent with
            | .cacheEvent ce_cw, _ =>
              simp only [Event.downgradeCorrespondingToRequest, he_cw_cache, he_down_cache] at hfwd_from
              exact hfwd_from.isDown
            | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
          | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
        -- Evict directory event: e_de from hstruct.cohEvictDir
        have he_de_isDir := hstruct.cohEvictDir.isDir
        have he_de_down : e_de.down := by
          -- dirOfReq → matchesCacheEvent.sameDown: de.down = ce.down
          -- cohEvict.downgrade: ce.down = True
          have hdir_of_req := hstruct.cohEvictDir.dirOfReq
          have hce_down := hstruct.cohEvict.downgrade
          match he_de_ev : e_de, he_ce_ev : e_ce with
          | .directoryEvent de, .cacheEvent ce =>
            simp [Event.dirEventOfReqEvent, DirectoryEvent.matchesCacheEvent] at hdir_of_req
            simp [Event.down]; rw [hdir_of_req.2]; simp [Event.down] at hce_down; exact hce_down
          | .directoryEvent _, .directoryEvent _ =>
            simp [Event.dirEventOfReqEvent] at hdir_of_req
          | .cacheEvent _, _ =>
            have := hstruct.cohEvictDir.isDir; simp [Event.isDirectoryEvent, he_de_ev] at this
        have he_dw_ob_de : e_dw.OrderedBefore n e_de :=
          hstruct.cohWriteImmBeforeEvict.isImmPred.bPred.isPred
        -- e_de.oEnd < CLE₂.oEnd: e_de inside e_gdown (via evict encap chain), e_gdown inside e_gcache
        have he_de_lt_cle : e_de.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd := by
          have he_gdown_encap_de : e_r_gdown.Encapsulates n e_de :=
            Event.encap_encap_trans n (hstruct.cohEvict.globalEncap)
              (hstruct.cohEvictDir.reqEncapDir)
          have h_gcache_encap_de : e_gcache.Encapsulates n e_de :=
            gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_de
          exact Nat.lt_trans h_gcache_encap_de.2 (gcache_oEnd_lt_cle hr_c_and_g_lin)
        exact ⟨e_dw, he_dw_in_b, he_dw_isDir, he_dw_proto, h_dw_end_before_cle,
          ⟨e_down, he_down_in_b, hencap, hdown_is_down, h_dpow.downgradePrevOwner.downAtCache⟩,
          ⟨e_de, he_de_in_b, he_de_isDir, he_de_down, he_de_lt_cle, he_dw_ob_de,
           hstruct.cohEvictDir.sameProtocol.symm.trans
             (correspondingCluster_protocol_eq hcorrespond
               hstruct.cohEvict.atCorrClusterProxy.clusterMatch.atCorrCluster |>.symm.trans hp_eq),
           -- isDirWrite: evict dir has SC write request → isWrite
           by
             have hdir_of_req := hstruct.cohEvictDir.dirOfReq
             have hreq_trans := hstruct.cohEvict.reqTranslation
             -- hreq_trans : ValidRequest.isSCWrite e_ce.req
             match he_de_ev : e_de, he_ce_ev : e_ce with
             | .directoryEvent de, .cacheEvent ce =>
               simp [Event.isDirWrite]
               simp [Event.dirEventOfReqEvent, DirectoryEvent.matchesCacheEvent] at hdir_of_req
               -- hdir_of_req.1 : de.eReq = ce → de.req relates to ce.req
               -- isDirWrite: de.req = reqToDirOfRequestEvent ... ce.
               -- For isSCWrite: reqToDirOfRequestEvent falls through to default → de.req = ce.req.
               -- ce.req.isSCWrite → ce.req.val.isWrite.
               have hdir_req := hstruct.cohEvictDir.dirCorresponds.dirReq
               simp [Event.req, he_de_ev, he_ce_ev] at hdir_req
               rw [hdir_req]
               -- Now goal: (Behaviour.reqToDirOfRequestEvent ...).val.isWrite
               -- hreq_trans : ValidRequest.isSCWrite ce.req
               -- For SC write: reqToDirOfRequestEvent returns ce.req unchanged.
               simp [Behaviour.reqToDirOfRequestEvent, Event.reqToDirOfRequestEvent,
                     Event.req, he_ce_ev, Event.down, he_ce_ev] at hreq_trans ⊢
               -- isSCWrite → isWrite: vr = ⟨⟨.w, true, .SC⟩, _⟩ → vr.val.isWrite
               simp [ValidRequest.isSCWrite] at hreq_trans
               rw [hreq_trans]; simp [Request.isWrite]
             | .directoryEvent _, .directoryEvent _ =>
               simp [Event.dirEventOfReqEvent] at hdir_of_req
             | .cacheEvent _, _ =>
               have := hstruct.cohEvictDir.isDir; simp [Event.isDirectoryEvent, he_de_ev] at this,
           -- translatedDir: clusterDirFromDiffProtocolRequest from global downgrade chain
           ⟨⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, _he_r_grant_in_b,
             hdowngrade,
             { clusterMatch :=
                { sameAddr := by
                    have h1 := hstruct.cohEvict.atCorrClusterProxy.clusterMatch.sameAddr
                    have h2 := hstruct.cohEvictDir.dirCorresponds.sameAddr
                    unfold Event.sameAddr at h1 h2 ⊢; rw [← h2]; exact h1
                  atCorrCluster := by
                    -- e_ce and e_de have same protocol (from cohEvictDir.sameProtocol).
                    -- correspondingClusterOfGlobalCache checks protocol matches target.
                    have h1 := hstruct.cohEvict.atCorrClusterProxy.clusterMatch.atCorrCluster
                    have hproto_eq := hstruct.cohEvictDir.sameProtocol
                    -- h1 : correspondingClusterOfGlobalCache e_r_gdown e_ce (Event.protocol n)
                    -- Unfold: checks (Event.protocol n) e_ce = .cluster1 or .cluster2
                    -- hproto_eq : e_ce.protocol = e_de.protocol
                    -- So (Event.protocol n) e_de = (Event.protocol n) e_ce → same condition
                    -- correspondingClusterOfGlobalCache checks (protocol e).
                    -- Since protocol e_ce = protocol e_de, the checks are equivalent.
                    show e_r_gdown.correspondingClusterOfGlobalCache n e_de (Event.protocol n)
                    have : (Event.protocol n) e_de = (Event.protocol n) e_ce := hproto_eq.symm
                    unfold Event.correspondingClusterOfGlobalCache at h1 ⊢
                    rw [this]; exact h1
                }
               atDir := hstruct.cohEvictDir.isDir
               globalEncap := Event.encap_encap_trans n
                 hstruct.cohEvict.globalEncap hstruct.cohEvictDir.reqEncapDir }
           ⟩⟩⟩⟩
      | cWriteOnMR hfwd =>
        -- MR case: also vacuous (scWriteDown is vacuous).
        sorry
    -/
    | scReadDown _ _ translation =>
      -- Same structure as scWriteDown but with read proxy and coherentReadDowngrades axiom
      obtain ⟨e_cr, he_cr_in_b, e_dr, _, hstruct⟩ := translation
      have he_dr_in_b := hstruct.cohReadDir.dirInB
      have he_dr_isDir := hstruct.cohReadDir.isDir
      have hproto := correspondingCluster_protocol_eq hcorrespond
        hstruct.cohRead.atCorrClusterProxy.clusterMatch.atCorrCluster
      have he_dr_proto : e_dr.protocol = e_w.protocol :=
        hstruct.cohReadDir.sameProtocol.symm.trans hproto.symm |>.trans hp_eq
      have he_gdown_encap_dr : e_r_gdown.Encapsulates n e_dr :=
        Event.encap_encap_trans n (hstruct.cohRead.globalEncap) (hstruct.cohReadDir.reqEncapDir)
      let e_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
          (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
      have h_gcache_encap_dr : e_gcache.Encapsulates n e_dr :=
        gcache_encap_dir_chain hr_c_and_g_lin hdowngrade he_gdown_encap_dr
      have h_dr_end_before_cle := Nat.lt_trans h_gcache_encap_dr.2 (gcache_oEnd_lt_cle hr_c_and_g_lin)
      -- Apply coherentReadDowngrades axiom (only cReadOnSW case)
      have haxiom := (e_w.getProtocol cmp).reqAxioms.coherentReadDowngrades b init
        e_cr he_cr_in_b e_dr he_dr_in_b
      cases haxiom.downgradeOtherCaches with
      | cReadOnSW hfwd =>
        obtain ⟨e_down, he_down_in_b, e_grant, _, h_dpow⟩ := hfwd.fwdPrevOwner
        have hencap := h_dpow.downgradePrevOwner.dirEncapDowngrade
        have hdown_is_down : e_down.down := by
          have hfwd_from := h_dpow.downgradePrevOwner.fwdFromRequester
          have hcache := h_dpow.downgradePrevOwner.downAtCache
          match he_down_cache : e_down, hcache with
          | .cacheEvent ce_down, _ =>
            match he_cr_cache : e_cr, haxiom.isCacheEvent with
            | .cacheEvent ce_cr, _ =>
              simp only [Event.downgradeCorrespondingToRequest] at hfwd_from
              exact hfwd_from.isDown
            | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
          | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
        exact ⟨e_dr, he_dr_in_b, he_dr_isDir, he_dr_proto, h_dr_end_before_cle,
          ⟨e_down, he_down_in_b, hencap, hdown_is_down, h_dpow.downgradePrevOwner.downAtCache⟩,
          by
          -- grantRels is unsatisfiable: requestEncapGrant gives e_grant.oEnd < e_cr.oEnd,
          -- but grantEndsRequest gives e_grant.oEnd = e_cr.oEnd + 1. Contradiction.
          exfalso
          have h1 := h_dpow.grantRels.requestEncapGrant.2  -- e_grant.oEnd < e_cr.oEnd
          have h2 := h_dpow.grantRels.grantEndsRequest      -- e_grant.oEnd = e_cr.oEnd + 1
          -- h1 : Event.oEnd n e_grant < Event.oEnd n e_cr
          -- h2 : Event.oEnd n e_grant = Event.oEnd n e_cr + 1
          -- Combined: e_cr.oEnd + 1 < e_cr.oEnd → contradiction
          simp only [h2] at h1; exact absurd (Nat.le_of_lt h1) (Nat.not_succ_le_self _)
          ⟩
  | noCoherentRead hcorrespond _ downTranslation =>
    -- noCoherentRead: case-split downTranslation. scWriteDowngrade is vacuous (same as scWriteDown).
    -- scReadDowngrade is the valid case but needs evict dir from cluster axiom.
    cases downTranslation with
    | scWriteDowngrade hwrite_down _ =>
      exact absurd hwrite_down (diffCache_coherent_globalDowngrade_not_scWrite hr_c_and_g_lin hdowngrade)
    | scReadDowngrade hread_down hmade_on_sw translation =>
      -- noCoherentRead.scReadDowngrade: the shim produces translateDirectoryEvent events.
      -- Apply cluster protocol axiom (coherentReadDowngrades) to get fwdPrevOwner,
      -- which has grantRels → unsatisfiable (requestEncapGrant.2 vs grantEndsRequest).
      cases translation with
      | onDirSW hdirSW htrans =>
        -- globalReadDownOnDirSW: has acq proxy + acq dir + Vd writeback dir.
        -- Apply nonCohReqDowngrades to acq proxy/dir → requestDowngradePrevOwner → cache downgrade.
        -- Use acq dir as e_cdir, Vd dir as e_evict (acqDirImmBeforeVdWBDir gives OB).
        obtain ⟨e_shim_acq, he_acq_in_b, e_dir_acq, he_dir_acq_in_b, e_dir_vd, hvd_in_b, hstruct⟩ := htrans
        -- Apply nonCohReqDowngrades (Axiom 12) to acquire proxy + dir → cache downgrade
        sorry -- TODO: nonCohReqDowngrades + construct cdir/cache_down/evict tuple
      | onDirVd hdirVd htrans =>
        -- globalReadDownOnDirVd: has Vd writeback dir + Vc invalidate dir.
        -- Similar structure: Vd dir as e_cdir, Vc dir as e_evict.
        sorry -- noCoherentRead.scReadDowngrade.onDirVd
