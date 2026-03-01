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

/-- Helper: Coherent write preserves write in reqToDirOfRequestEvent. -/
lemma reqToDir_preserves_write_of_coherent
  (e_req : Event n) (s : State)
  (hwrite : e_req.req.val.isWrite)
  (hcoh : e_req.req.val.coherent = true) :
  (Event.reqToDirOfRequestEvent n e_req s).val.isWrite := by
  -- Unfold and reduce by cases on the request itself
  cases hreq : e_req.req with
  | mk r hr =>
    cases r with
    | mk rw coh cons =>
      have hrw : rw = .w := by
        simpa [hreq, Request.isWrite] using hwrite
      have hcoh' : coh = true := by
        simpa [hreq] using hcoh
      cases hrw
      cases hcoh'
      simp [Event.reqToDirOfRequestEvent, hreq, Request.isWrite]

/-- Helper: NC release on Vd preserves write in reqToDirOfRequestEvent. -/
lemma reqToDir_preserves_write_on_vd_ncrel
  (e_req : Event n)
  (hrel : e_req.req.val = ⟨.w, false, .Rel⟩) :
  (Event.reqToDirOfRequestEvent n e_req Vd).val.isWrite := by
  cases hreq : e_req.req with
  | mk r hr =>
    cases r with
    | mk rw coh cons =>
      have hrel' : Request.mk rw coh cons = ⟨.w, false, .Rel⟩ := by
        simpa [hreq] using hrel
      cases hrel'
      simp [Event.reqToDirOfRequestEvent, hreq, Vd, Request.isWrite]

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
      have hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      exists e_inter_cle
      constructor
      · exact hinter_lin.hreq's_dir_access.choose_spec.left
      intro hdowngrade
      exact hnot_between
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
                  exact produces_state_with_write_perms_implies_is_write_no_coherence hwrite hhascoh.hasPerms hhascoh.onCoherentState hpred_produces_state_at_least_req_made_on_state hinter_pred_not_down hpred_missing_perms hpred_cache
                    cmp.noNcWeakWriteOnMRState
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
      have hnot_between := hcontra.notBetweenCles hsame_protocol_and_dir_write
      exists e_inter_cle
      constructor
      · exact hinter_lin.hreq's_dir_access.choose_spec.left
      intro hdowngrade
      exact hnot_between

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
  (hwrite_not_down : ¬ e_inter.down)
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

  have hcontra := _hno_intervening e he hwrite_cluster hwrite hwrite_not_down
  have hinter_lin := _hknow_dir_access cmp b init e

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
