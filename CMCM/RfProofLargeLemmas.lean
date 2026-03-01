import CMCM.RfProofDefs

variable {n : ℕ}

/-- Helper: If a request produces a state with write permissions, the request must be a write. -/
lemma produces_state_with_write_perms_implies_is_write
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hwrite : e_req.isWrite)
  (hcoh : Event.isCoherent n e_req)
  (hreq_has_perms : b.hasPerms n init e_req)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  : e_pred.req.val.isWrite := by
  -- Strategy: Show that e_req needs write permissions, and predecessor produced them
  cases e_req with
  | cacheEvent ce =>
    simp [Event.isWrite] at hwrite
    cases e_pred with
    | cacheEvent ce_pred =>
      simp [Event.req, Request.isWrite]
      -- Need to show: ce_pred.req.val.rw = .w
      -- We know:
      -- 1. ce.req.val.isWrite (hwrite)
      -- 2. ce has permissions: ce.req.MRS ≤ stateBefore ce (hreq_has_perms)
      -- 3. predecessor produces: stateBefore ce ≤ stateAfter ce_pred (hpred_produces)
      -- For most writes, MRS.p = some .wr
      -- Therefore stateAfter ce_pred has p = some .wr
      -- Only writes can produce p = some .wr
      unfold Behaviour.hasPerms at hreq_has_perms
      unfold Behaviour.stateReqMadeOn Behaviour.reqLeavesStateAtLeast at hpred_produces
      simp [Event.req] at hreq_has_perms hpred_produces

      have he_req_mrs_le_pred_state_after : ce.req.MRS ≤ (b.stateAfter n (init.stateAt n (Event.cacheEvent ce_pred)) (Event.cacheEvent ce_pred)).cache :=
        State.le_trans hreq_has_perms hpred_produces

      -- simp [Behaviour.stateAfter] at he_req_mrs_le_pred_state_after

      -- match hpred_req : ce_pred.req with
      match he_req : ce.req with
      | ⟨⟨.w,true,.SC⟩, _⟩
      | ⟨⟨.w,true,.Rel⟩, _⟩
      | ⟨⟨.w,true,.Weak⟩, _⟩ =>
        match hpred_req : ce_pred.req with
        | ⟨⟨.w,true,_⟩,_⟩ =>
          simp
        | ⟨⟨.w,false,.Rel⟩,_⟩ =>
          cases hpred_missing_perms with
          | downgrade hd _ =>
            -- ce_pred is a downgrade, contradicts hpred_not_down
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel _ =>
            -- This case is for non-NC-Rel-Acq-WeakWrite requests
            -- But ce_pred is w,false,.Rel which IS in NC-Rel-Acq
            exfalso
            have hpred_is_nc_rel : Event.isNcRelAcqWeakWrite n (Event.cacheEvent ce_pred) := by
              simp only [Event.isNcRelAcqWeakWrite]
              right; left
              simp only [Event.isNcRelease]
              exact hpred_req
            exact hnotrel hpred_is_nc_rel
          | ncRelAcqWeakWriteNotOnCoherentState _ _ hno_perms_acq =>
            simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms_acq
            simp only [Behaviour.eventOnCoherentState] at hno_perms_acq
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
        | ⟨⟨.w,false,.Weak⟩,_⟩ =>
          cases hpred_missing_perms with
          | downgrade hd _ =>
            -- ce_pred is a downgrade, contradicts hpred_not_down
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            -- simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms
            -- simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
          | ncRelAcqWeakWriteNotOnCoherentState _ _ hno_perms_acq =>
            simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms_acq
            simp only [Behaviour.eventOnCoherentState] at hno_perms_acq
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
        | ⟨⟨.r,true,.SC⟩,_⟩ =>
          cases hpred_missing_perms with
          | downgrade hd _ =>
            -- ce_pred is a downgrade, contradicts hpred_not_down
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            -- simp[Behaviour.eventOnStateNoPerms] at hno_perms
            -- simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms
            simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms

            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after

            simp [Event.req,] at hno_perms
            -- TODO:
            -- 1. show cases of ce_pred's state before is lower than it's MRS (using `hno_perms`).
            -- 2. Then show the succeedingState of ce_pred has permissions lower than ce's MRS (at `he_req_mrs_le_pred_state_after`)
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case noPermsForNonNcRelAcqWeakWrite.mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after

              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms, ReadWrite.toRWPerms] at hno_perms
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after

                simp[he_req] at he_req_mrs_le_pred_state_after

                try simp at he_req_mrs_le_pred_state_after
                simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_ack hno_perms_acq =>
            simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, hpred_req] at hnc_rel_ack
        | ⟨⟨.r,false,.Weak⟩,_⟩ =>
          cases hpred_missing_perms with
          | downgrade hd _ =>
            -- ce_pred is a downgrade, contradicts hpred_not_down
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            -- simp[Behaviour.eventOnStateNoPerms] at hno_perms
            -- simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms
            simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms

            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after

            simp [Event.req,] at hno_perms
            -- TODO:
            -- 1. show cases of ce_pred's state before is lower than it's MRS (using `hno_perms`).
            -- 2. Then show the succeedingState of ce_pred has permissions lower than ce's MRS (at `he_req_mrs_le_pred_state_after`)
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case noPermsForNonNcRelAcqWeakWrite.mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after

              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms, ReadWrite.toRWPerms] at hno_perms
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after

                simp[he_req] at he_req_mrs_le_pred_state_after

                try simp at he_req_mrs_le_pred_state_after
                try simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                try simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_ack hno_perms_acq =>
            simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, hpred_req] at hnc_rel_ack
        | ⟨⟨.r,false,.Acq⟩,_⟩ =>
          cases hpred_missing_perms with
          | downgrade hd _ =>
            -- ce_pred is a downgrade, contradicts hpred_not_down
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            -- simp[Behaviour.eventOnStateNoPerms] at hno_perms
            -- simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms
            simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms

            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after

            simp [Event.req,] at hno_perms
            -- TODO:
            -- 1. show cases of ce_pred's state before is lower than it's MRS (using `hno_perms`).
            -- 2. Then show the succeedingState of ce_pred has permissions lower than ce's MRS (at `he_req_mrs_le_pred_state_after`)
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case noPermsForNonNcRelAcqWeakWrite.mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after

              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms, ReadWrite.toRWPerms] at hno_perms
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after

                simp[he_req] at he_req_mrs_le_pred_state_after

                try simp at he_req_mrs_le_pred_state_after
                try simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                try simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_ack hno_perms_acq =>
            simp only [Behaviour.acqRelWeakWriteNoPerms] at hno_perms_acq
            simp only [Behaviour.eventOnStateHasPerms, Behaviour.eventOnCoherentState] at hno_perms_acq

            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after

            simp only [Event.req,] at hno_perms_acq
            -- TODO:
            -- 1. show cases of ce_pred's state before is lower than it's MRS (using `hno_perms`).
            -- 2. Then show the succeedingState of ce_pred has permissions lower than ce's MRS (at `he_req_mrs_le_pred_state_after`)
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after

              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms, ReadWrite.toRWPerms] at hno_perms_acq
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms_acq
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms_acq
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms_acq
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms_acq
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after

                simp[he_req] at he_req_mrs_le_pred_state_after

                -- try simp at he_req_mrs_le_pred_state_after
                -- try simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                -- try simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

      | ⟨⟨.r,true,_⟩, _⟩ =>
        simp[Request.isWrite] at hwrite
        absurd hwrite
        have hreq_read : ce.req.val.rw = .r := by
          simp[he_req]
        simp[hreq_read]
      | ⟨⟨_,false,_⟩,_⟩ =>
        simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at hcoh
        absurd hcoh
        simp[he_req]
    | directoryEvent de_pred =>
      simp[Event.isCacheEvent] at hpred_cache
  | directoryEvent _ =>
    simp [Event.isWrite] at hwrite

lemma pred_is_write_of_req_produces_write_perms_and_has_coherent_perms_before
-- b : Behaviour n
-- init : InitialSystemState n
-- ce : CacheEvent n
-- (hwrite : ce.req.val.isWrite)
-- (hreq_has_perms : ce.req.MRS ≤
--   EntryState.cache n
--     (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
(hreq_on_coherent_state : (EntryState.cache n
      (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce))).c =
  true)
{ce_pred : CacheEvent n}
(hpred_not_down : ¬Event.down n (Event.cacheEvent ce_pred) = true)
-- (hpred_missing_perms : Behaviour.reqMissingPerms n b init (Event.cacheEvent ce_pred))
-- (hpred_cache : Event.isCacheEvent n (Event.cacheEvent ce_pred))
(hreq_has_perms : (Event.req n (Event.cacheEvent ce)).MRS ≤
  EntryState.cache n
    (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
(hpred_produces : EntryState.cache n
    (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)) ≤
  EntryState.cache n
    (Behaviour.stateAfter n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred)) (Event.cacheEvent ce_pred)))
(he_req_mrs_le_pred_state_after : ce.req.MRS ≤
  EntryState.cache n
    (Behaviour.stateAfter n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred)) (Event.cacheEvent ce_pred)))
-- property✝ : { rw := ReadWrite.w, coherent := false, consistency := Consistency.Rel }.IsValid'
(he_req : ce.req = ⟨{ rw := ReadWrite.w, coherent := false, consistency := hreq_consistency }, property1⟩)
(hreq_weak_or_rel : hreq_consistency = .Weak ∨ hreq_consistency = .Rel)
(hno_perms : Behaviour.eventOnStateNoPerms n b init (Event.cacheEvent ce_pred))
(hpred_req : ce_pred.req = ⟨{ rw := ReadWrite.r, coherent := coh, consistency := cons }, property2⟩)
(hno_weak_write_on_coherent_read : Behaviour.stateBefore.CoherentRead.ofWeakWrite.contradiction n)
  : (ce_pred.req.val).rw = ReadWrite.w := by
  -- : ce_pred.req.val.rw = ReadWrite.w := by
  simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
  rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
  rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at hpred_produces
  simp [Event.req] at hno_perms
  cases hstate_before_pred : (EntryState.cache n
    (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
      (Event.cacheEvent ce_pred)))
  . case mk hpred_p hpred_c =>
    have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
      (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
      (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
    have hunwrap' := hunwrap hstate_before_pred
    rw[hunwrap'] at he_req_mrs_le_pred_state_after
    rw[hunwrap'] at hpred_produces
    rw[hunwrap'] at hno_perms
    rw[EntryState.cache] at hno_perms
    simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms] at hno_perms
    match hpred_p, hpred_c with
    | some .wr, true =>
      -- simp[hstate_before_pred] at hno_perms
      simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
      match coh, cons with
      | true, .SC =>
        simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
      | false, .Weak =>
        simp[LT.lt] at hno_perms
      | false, .Acq =>
        simp[LT.lt] at hno_perms
    | some .r, true =>
      -- simp[hstate_before_pred] at hno_perms
      simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
      match coh, cons with
      | true, .SC =>
        simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
      | false, .Weak =>
        simp[LT.lt] at hno_perms
      | false, .Acq =>
        simp[LT.lt] at hno_perms
    | some .wr, false
    | some .r, false
    | none, true
    | none, false =>
      simp[Event.down] at hpred_not_down
      simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
      simp[hpred_not_down] at he_req_mrs_le_pred_state_after
      simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
      simp[hpred_req] at he_req_mrs_le_pred_state_after
      simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after
      simp[ReadWrite.toPerms] at he_req_mrs_le_pred_state_after
      simp[EntryState.cache] at he_req_mrs_le_pred_state_after
      simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after
      simp[Vd] at he_req_mrs_le_pred_state_after
      simp[he_req] at he_req_mrs_le_pred_state_after
      try simp at he_req_mrs_le_pred_state_after
      simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
      simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

      simp[ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
      match coh, cons with
      | true, .SC =>
        -- simp[ReadWrite.toRWPerms, LE.le, State.le, ReadWritePermissions.le, LT.lt, State.lt, ReadWritePermissions.lt] at hno_perms
        cases hreq_weak_or_rel with
        | inl hweak =>
          simp[hweak] at he_req_mrs_le_pred_state_after
          simp[Event.SucceedingState, CacheEvent.SucceedingState] at hpred_produces
          simp[hpred_not_down] at hpred_produces
          simp[ValidRequest.RequestState] at hpred_produces
          simp[hpred_req] at hpred_produces
          simp[ValidRequest.MRS] at hpred_produces
          -- simp[ReadWrite.toPerms] at hpred_produces
          cases hstate_before_req : (EntryState.cache n
            (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
          . case mk hreq_before_p hreq_before_c =>
            have hunwrap_req := b.unwrap_stateBefore_cache_state_to_entry_state'
              (e_pred := Event.cacheEvent ce) (state := { p := hreq_before_p, c := hreq_before_c }) n
              (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce) init (by simp[Event.isCacheEvent]))
            match hreq_before_p, hreq_before_c with
            | some .wr, true =>
              simp[hstate_before_req] at hreq_on_coherent_state
              simp[hstate_before_req] at hpred_produces
              simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
              simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
              simp[EntryState.cache] at hpred_produces
              simp[LE.le, ReadWritePermissions.le] at hpred_produces
              simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
            | some .r, true =>
              simp[hweak] at he_req
              have hreq_can't_be_nc_weak_write := (hno_weak_write_on_coherent_read b init (Event.cacheEvent ce)).mp (by simp[Event.isNcWeakWrite, CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite, he_req])
              have hunwrap_req' := hunwrap_req hstate_before_req
              rw[hunwrap_req'] at hreq_can't_be_nc_weak_write
              simp[MREntry] at hreq_can't_be_nc_weak_write
            | some .wr, false
            | some .r, false
            | none, true
            | none, false =>
              simp[hstate_before_req] at hreq_on_coherent_state
              try
                simp[hstate_before_req] at hreq_has_perms
                simp[Event.req, ValidRequest.MRS, he_req, hweak] at hreq_has_perms
                simp[Vc, LE.le, State.le, LT.lt, State.lt, Option.le] at hreq_has_perms
        | inr hrel =>
          simp[hrel] at he_req_mrs_le_pred_state_after
      | false, .Weak =>
        -- `e_pred` is a non-coherent weak read.
        simp[LE.le, Option.le, ReadWritePermissions.le, LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after
        -- simp[Event.down] at hpred_not_down
        simp[Event.SucceedingState, CacheEvent.SucceedingState] at hpred_produces
        simp[hpred_not_down] at hpred_produces
        simp[ValidRequest.RequestState] at hpred_produces
        simp[hpred_req] at hpred_produces
        simp[ValidRequest.MRS] at hpred_produces
        -- simp[ReadWrite.toPerms] at hpred_produces
        cases hstate_before_req : (EntryState.cache n
          (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
        . case mk hreq_before_p hreq_before_c =>
          match hreq_before_p, hreq_before_c with
          | some .wr, true =>
            simp[hstate_before_req] at hreq_on_coherent_state
            simp[hstate_before_req] at hpred_produces
            simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
            simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
            simp[EntryState.cache] at hpred_produces
            try
              simp[LE.le, ReadWritePermissions.le] at hpred_produces
              simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
          | some .r, true =>
            simp[hstate_before_req] at hreq_on_coherent_state
            simp[hstate_before_req] at hpred_produces
            simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
            simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
            simp[EntryState.cache] at hpred_produces
            try
              simp[LE.le, ReadWritePermissions.le] at hpred_produces
              simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
          | some .wr, false
          | some .r, false
          | none, true
          | none, false =>
            simp[hstate_before_req] at hreq_on_coherent_state
            try simp[hstate_before_req] at hpred_produces
            try simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
            try simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
            try simp[EntryState.cache] at hpred_produces
            try simp[LE.le, ReadWritePermissions.le] at hpred_produces
            try simp[LT.lt, ReadWritePermissions.lt] at hpred_produces

      | false, .Acq =>
        -- `e_pred` is a non-coherent weak read.
        simp[LE.le, Option.le, ReadWritePermissions.le, LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

        -- simp[Event.down] at hpred_not_down
        simp[Event.SucceedingState, CacheEvent.SucceedingState] at hpred_produces
        simp[hpred_not_down] at hpred_produces
        simp[ValidRequest.RequestState] at hpred_produces
        simp[hpred_req] at hpred_produces
        -- simp[ValidRequest.MRS] at hpred_produces
        -- simp[ReadWrite.toPerms] at hpred_produces
        cases hstate_before_req : (EntryState.cache n
          (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
        . case mk hreq_before_p hreq_before_c =>
          match hreq_before_p, hreq_before_c with
          | some .wr, true =>
            simp[hstate_before_req] at hreq_on_coherent_state
            simp[hstate_before_req] at hpred_produces
            simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
            -- simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
            simp[EntryState.cache] at hpred_produces
            -- simp[LE.le, ReadWritePermissions.le] at hpred_produces
            -- simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
          | some .r, true =>
            simp[hstate_before_req] at hreq_on_coherent_state
            simp[hstate_before_req] at hpred_produces
            simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
            -- simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
            simp[EntryState.cache] at hpred_produces
            -- simp[LE.le, ReadWritePermissions.le] at hpred_produces
            -- simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
          | some .wr, false
          | some .r, false
          | none, true
          | none, false =>
            simp[hstate_before_req] at hreq_on_coherent_state
            try
              simp[hstate_before_req] at hpred_produces
              simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
              -- simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
              simp[EntryState.cache] at hpred_produces
              -- simp[LE.le, ReadWritePermissions.le] at hpred_produces
              -- simp[LT.lt, ReadWritePermissions.lt] at hpred_produces


/-- Alternative version for NC requests: If a request produces a state with write permissions, the request must be a write (no coherence assumption). -/
lemma produces_state_with_write_perms_implies_is_write_no_coherence
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hwrite : e_req.isWrite)
  (hreq_has_perms : b.hasPerms n init e_req)
  (hreq_on_coherent_state : b.reqMadeOnCoherentState n init e_req)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  (hno_nc_weak_write_on_coherent_read : Behaviour.stateBefore.CoherentRead.ofWeakWrite.contradiction n)
  : e_pred.req.val.isWrite := by
  -- Strategy: Similar to the first version, but works for NC requests too
  -- Show that e_req needs write permissions, and predecessor produced them
  cases e_req with
  | cacheEvent ce =>
    simp [Event.isWrite] at hwrite
    cases e_pred with
    | cacheEvent ce_pred =>
      simp [Event.req, Request.isWrite]
      -- Need to show: ce_pred.req.val.rw = .w
      -- We know:
      -- 1. ce.req.val.isWrite (hwrite)
      -- 2. ce has permissions: ce.req.MRS ≤ stateBefore ce (hreq_has_perms)
      -- 3. predecessor produces: stateBefore ce ≤ stateAfter ce_pred (hpred_produces)
      -- For writes with write permissions, MRS.p = some .wr
      -- Therefore stateAfter ce_pred has p = some .wr
      -- Only writes can produce p = some .wr
      unfold Behaviour.hasPerms at hreq_has_perms
      unfold Behaviour.stateReqMadeOn Behaviour.reqLeavesStateAtLeast at hpred_produces
      simp [Event.req] at hreq_has_perms hpred_produces

      simp[Behaviour.reqMadeOnCoherentState] at hreq_on_coherent_state
      unfold Behaviour.stateReqMadeOn at hreq_on_coherent_state

      have he_req_mrs_le_pred_state_after : ce.req.MRS ≤ (b.stateAfter n (init.stateAt n (Event.cacheEvent ce_pred)) (Event.cacheEvent ce_pred)).cache :=
        State.le_trans hreq_has_perms hpred_produces

      -- Match on the request type
      match he_req : ce.req with
      | ⟨⟨.w,true,.SC⟩, _⟩
      | ⟨⟨.w,true,.Rel⟩, _⟩
      | ⟨⟨.w,true,.Weak⟩, _⟩ =>
        -- Coherent writes: MRS = ⟨some .wr, true⟩
        -- These need write permissions, so predecessor must be write
        match hpred_req : ce_pred.req with
        | ⟨⟨.w,_,_⟩,_⟩ =>
          -- Predecessor is write, done
          simp
        | ⟨⟨.r,coh,cons⟩,_⟩ =>
          -- Predecessor is read, derive contradiction
          -- Reads cannot produce write permissions
          cases hpred_missing_perms with
          | downgrade hd _ =>
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
            simp [Event.req] at hno_perms
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case noPermsForNonNcRelAcqWeakWrite.mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after
              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms] at hno_perms
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
                match coh, cons with
                | true, .SC =>
                  simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
                | false, .Weak =>
                  simp[LT.lt] at hno_perms
                | false, .Acq =>
                  simp[LT.lt] at hno_perms
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
                match coh, cons with
                | true, .SC =>
                  simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
                | false, .Weak =>
                  simp[LT.lt] at hno_perms
                | false, .Acq =>
                  simp[LT.lt] at hno_perms
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after
                simp[ReadWrite.toPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after
                simp[he_req] at he_req_mrs_le_pred_state_after
                try simp at he_req_mrs_le_pred_state_after
                simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                match coh, cons with
                | true, .SC =>
                  simp[] at he_req_mrs_le_pred_state_after
                | false, .Weak =>
                  simp[LE.le, Option.le, ReadWritePermissions.le, LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after
                | false, .Acq =>
                  simp[] at he_req_mrs_le_pred_state_after
          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_ack hno_perms_acq =>
            -- hnc_rel_ack : Event.isNcRelAcq = isNcRelease ∨ isAcquire
            -- Case on whether it's Acq or NC Rel
            cases hnc_rel_ack with
            | inl hacq =>
              -- Acquire is a read (.r), contradicts goal (we need to show predecessor is write .w)
              exfalso
              rw [Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
              simp [Event.down] at hpred_not_down
              simp [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
              simp [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down,
                ValidRequest.RequestState, ValidRequest.MRS, ReadWrite.toPerms,
                EntryState.cache, LE.le, State.le, LT.lt, State.lt, Option.le,
                ReadWritePermissions.le, ReadWritePermissions.lt, he_req, hacq]
                at he_req_mrs_le_pred_state_after
            | inr hncrel =>
              -- NC Release: this is a write, so done
              simp[Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease, hpred_req] at hncrel
      | ⟨⟨.w,false,.Rel⟩, _⟩ =>
        -- NC Rel write: MRS = Vd = ⟨some .wr, false⟩
        -- Needs write permissions, so predecessor must be write
        match hpred_req : ce_pred.req with
        | ⟨⟨.w,_,_⟩,_⟩ =>
          -- Predecessor is write, done
          simp
        | ⟨⟨.r,coh,cons⟩,_⟩ =>
          -- Predecessor is read, derive contradiction
          -- Reads cannot produce write permissions
          cases hpred_missing_perms with
          | downgrade hd _ =>
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite _ hnotrel hno_perms =>
            simp only [Behaviour.eventOnStateNoPerms, Behaviour.eventOnStateHasPerms] at hno_perms
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
            rw[Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at hpred_produces
            simp [Event.req] at hno_perms
            cases hstate_before_pred : (EntryState.cache n
              (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                (Event.cacheEvent ce_pred)))
            . case noPermsForNonNcRelAcqWeakWrite.mk hpred_p hpred_c =>
              have hunwrap := b.unwrap_stateBefore_cache_state_to_entry_state'
                (e_pred := Event.cacheEvent ce_pred) (state := { p := hpred_p, c := hpred_c }) n
                (by simp[Event.isCacheEvent]) (b.initCacheStateIsCache (Event.cacheEvent ce_pred) init (by simp[Event.isCacheEvent]))
              have hunwrap' := hunwrap hstate_before_pred
              rw[hunwrap'] at he_req_mrs_le_pred_state_after
              rw[hunwrap'] at hpred_produces
              simp[ValidRequest.MRS, hpred_req, ReadWrite.toPerms] at hno_perms
              match hpred_p, hpred_c with
              | some .wr, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
                match coh, cons with
                | true, .SC =>
                  simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
                | false, .Weak =>
                  simp[LT.lt] at hno_perms
                | false, .Acq =>
                  simp[LT.lt] at hno_perms
              | some .r, true =>
                simp[hstate_before_pred] at hno_perms
                simp[LE.le, State.le, LT.lt, Option.le] at hno_perms
                match coh, cons with
                | true, .SC =>
                  simp[ReadWrite.toRWPerms, LT.lt] at hno_perms
                | false, .Weak =>
                  simp[LT.lt] at hno_perms
                | false, .Acq =>
                  simp[LT.lt] at hno_perms
              | some .wr, false
              | some .r, false
              | none, true
              | none, false =>
                simp[Event.down] at hpred_not_down
                simp[Event.SucceedingState, CacheEvent.SucceedingState] at he_req_mrs_le_pred_state_after
                simp[hpred_not_down] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.RequestState] at he_req_mrs_le_pred_state_after
                simp[hpred_req] at he_req_mrs_le_pred_state_after
                simp[ValidRequest.MRS] at he_req_mrs_le_pred_state_after
                simp[ReadWrite.toPerms] at he_req_mrs_le_pred_state_after
                simp[EntryState.cache] at he_req_mrs_le_pred_state_after
                simp[LE.le, State.le, LT.lt, State.lt, Option.le] at he_req_mrs_le_pred_state_after
                simp[Vd] at he_req_mrs_le_pred_state_after
                simp[he_req] at he_req_mrs_le_pred_state_after
                try simp at he_req_mrs_le_pred_state_after
                simp[ReadWritePermissions.le] at he_req_mrs_le_pred_state_after
                simp[LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after

                simp[ReadWrite.toRWPerms] at he_req_mrs_le_pred_state_after
                match coh, cons with
                | true, .SC =>
                  simp[] at he_req_mrs_le_pred_state_after
                | false, .Weak =>
                  simp[LE.le, Option.le, ReadWritePermissions.le, LT.lt, ReadWritePermissions.lt] at he_req_mrs_le_pred_state_after
                  try

                    -- simp[Event.down] at hpred_not_down
                    simp[Event.SucceedingState, CacheEvent.SucceedingState] at hpred_produces
                    simp[hpred_not_down] at hpred_produces
                    simp[ValidRequest.RequestState] at hpred_produces
                    simp[hpred_req] at hpred_produces
                    simp[ValidRequest.MRS] at hpred_produces
                    -- simp[ReadWrite.toPerms] at hpred_produces
                    cases hstate_before_req : (EntryState.cache n
                      (Behaviour.stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)))
                    . case mk hreq_before_p hreq_before_c =>
                      match hreq_before_p, hreq_before_c with
                      | some .wr, true =>
                        simp[hstate_before_req] at hreq_on_coherent_state
                        simp[hstate_before_req] at hpred_produces
                        simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
                        simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
                        simp[EntryState.cache] at hpred_produces
                        simp[LE.le, ReadWritePermissions.le] at hpred_produces
                        simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
                      | some .r, true =>
                        simp[hstate_before_req] at hreq_on_coherent_state
                        simp[hstate_before_req] at hpred_produces
                        simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
                        simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
                        simp[EntryState.cache] at hpred_produces
                        simp[LE.le, ReadWritePermissions.le] at hpred_produces
                        simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
                      | some .wr, false
                      | some .r, false
                      | none, true
                      | none, false =>
                        simp[hstate_before_req] at hreq_on_coherent_state
                        try
                          simp[hstate_before_req] at hpred_produces
                          simp[LE.le, State.le, LT.lt, State.lt, Option.le] at hpred_produces
                          simp[ReadWrite.toPerms, ReadWrite.toRWPerms] at hpred_produces
                          simp[EntryState.cache] at hpred_produces
                          simp[LE.le, ReadWritePermissions.le] at hpred_produces
                          simp[LT.lt, ReadWritePermissions.lt] at hpred_produces
                | false, .Acq =>
                  simp[] at he_req_mrs_le_pred_state_after
          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_ack hno_perms_acq =>
            -- hnc_rel_ack : Event.isNcRelAcq = isNcRelease ∨ isAcquire
            -- Case on whether it's Acq or NC Rel
            cases hnc_rel_ack with
            | inl hacq =>
              -- Acquire is a read (.r), contradicts goal (we need to show predecessor is write .w)
              exfalso
              rw [Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at he_req_mrs_le_pred_state_after
              simp [Event.down] at hpred_not_down
              simp [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
              simp [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down,
                ValidRequest.RequestState, ValidRequest.MRS, ReadWrite.toPerms,
                EntryState.cache, LE.le, State.le, LT.lt, State.lt, Option.le,
                ReadWritePermissions.le, ReadWritePermissions.lt, he_req, hacq, Vd]
                at he_req_mrs_le_pred_state_after
            | inr hncrel =>
              -- NC Release: this is a write, so done
              simp[Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease, hpred_req] at hncrel
      | ⟨⟨.w,false,.Weak⟩, property_req⟩ =>
        match hpred_req : ce_pred.req with
        | ⟨⟨.w,_,_⟩,property_pred⟩ =>
          -- Predecessor is write, done
          simp
        | ⟨⟨.r,coh,cons⟩,_⟩ =>
          -- NC Weak write: MRS = Vc = ⟨some .r, false⟩
          -- Only needs read permissions - so we need different analysis
          -- For NC Weak write, if predecessor is read, the read might produce Vc
          -- But we can use hpred_missing_perms to constrain the predecessor
          cases hpred_missing_perms with
          | downgrade hd _ =>
            exfalso
            exact hpred_not_down hd
          | noPermsForNonNcRelAcqWeakWrite hpred_not_down hnotrel hno_perms =>
            . case noPermsForNonNcRelAcqWeakWrite =>
              rw[← hpred_req]
              apply pred_is_write_of_req_produces_write_perms_and_has_coherent_perms_before
              . case hreq_on_coherent_state => exact hreq_on_coherent_state
              . case hpred_not_down => exact hpred_not_down
              . case hreq_has_perms => exact hreq_has_perms
              . case hpred_produces => exact hpred_produces
              . case he_req_mrs_le_pred_state_after => exact he_req_mrs_le_pred_state_after
              . case he_req => exact he_req
              . case hreq_weak_or_rel => simp[]
              . case hno_perms => exact hno_perms
              . case hpred_req => exact hpred_req
              . case hno_weak_write_on_coherent_read => exact hno_nc_weak_write_on_coherent_read
                --exact property_pred
          | ncRelAcqWeakWriteNotOnCoherentState _ hnc_rel_acq _ =>
            -- Predecessor is NC Rel/Acq but not on coherent state
            cases hnc_rel_acq with
            | inl hacq =>
              exfalso
              -- From predecessor producing a state at least as high as a coherent state,
              -- coherence must satisfy true ≤ stateAfter.c.
              have hreq_coh_true : (b.stateReqMadeOn n init (Event.cacheEvent ce)).c = true := by
                simpa [Behaviour.reqMadeOnCoherentState] using hreq_on_coherent_state
              have hcoh_le_after :
                (b.stateReqMadeOn n init (Event.cacheEvent ce)).c ≤
                (b.stateAfter n (InitialSystemState.stateAt n init (Event.cacheEvent ce_pred))
                  (Event.cacheEvent ce_pred)).cache.c := by
                cases hpred_produces with
                | inl hlt => exact hlt.right.left
                | inr heq =>
                  unfold Behaviour.stateReqMadeOn
                  rw [heq]

              rw [Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce_pred)] at hcoh_le_after
              simp [Event.down] at hpred_not_down
              simp [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] at hacq
              simp [Event.SucceedingState, CacheEvent.SucceedingState, hpred_not_down,
                ValidRequest.RequestState, hacq, Vc] at hcoh_le_after
              rw [hreq_coh_true] at hcoh_le_after
              exact (by decide : ¬ (true ≤ false)) hcoh_le_after
            | inr hrel =>
              simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease] at hrel
              have hrw : ce_pred.req.val.rw = .w := by
                simp [hrel]
              simp []

              rw[hpred_req] at hrel
              simp at hrel
      | ⟨⟨.r,_,_⟩, _⟩ =>
        -- Read isn't a write, contradicts hwrite
        simp[Request.isWrite] at hwrite
        absurd hwrite
        have hreq_read : ce.req.val.rw = .r := by simp[he_req]
        simp[hreq_read]
    | directoryEvent de_pred =>
      simp[Event.isCacheEvent] at hpred_cache
  | directoryEvent _ =>
    simp [Event.isWrite] at hwrite