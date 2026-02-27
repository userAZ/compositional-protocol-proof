import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

lemma List.ordered_mem_impl_ordered_idx {α} [DecidableEq α] {l_head l_tail : List α} {n m : α}
  (l : List α) (hlist : l = l_head ++ l_tail)
  (hn_in_head : n ∈ l_head) (hm_in_tail : m ∈ l_tail) (hl_nodup : l.Nodup) : idxOf n l < idxOf m l  := by
  rw[hlist]
  rw[List.idxOf_append_of_mem]
  have hm_not_in_head : m ∉ l_head := by
    simp[List.Nodup] at hl_nodup
    intro hm_in_head
    rw[hlist] at hl_nodup
    have test := List.nodup_append'.mp hl_nodup
    have test1 := test.right.right
    simp[List.Disjoint] at test1
    apply (test1 hm_in_head)
    exact hm_in_tail
  . rw[List.idxOf_append_of_notMem hm_not_in_head]
    have hidx_n_lt_length := List.idxOf_lt_length_of_mem hn_in_head
    have hidx_n_lt_length_plus_idx_m := Nat.lt_add_left (idxOf m l_tail) hidx_n_lt_length
    rw[Nat.add_comm] at hidx_n_lt_length_plus_idx_m
    exact hidx_n_lt_length_plus_idx_m
  . exact hn_in_head

lemma Behaviour.contradiction_of_event_after_last_pred
  {l_head : List (Event n)} {last : (Event n)} (l : List (Event n)) (hsorted : l.Sorted (Event.OrderedBefore n))
  (hlist : l = l_head ++ [last]) (hl_nodup : l.Nodup) (e_between : Event n) (he_btn_in_l : e_between ∈ l) (hlast_lt_n : last.OrderedBefore n e_between)
  : False := by
  have hlast_in_l : last ∈ l := by simp [hlist]
  simp[List.Sorted] at hsorted
  -- simp[List.pairwise_iff Nat.lt l] at hsorted
  -- simp[List.pairwise_iff_forall_sublist] at hsorted
  simp[List.pairwise_iff_getElem] at hsorted

  have hspare_n_in_l := he_btn_in_l

  rw[hlist] at he_btn_in_l
  simp[List.mem_append] at he_btn_in_l
  have hn_ne_last : e_between ≠ last := by
    intro he_btn_eq_last
    simp[Event.OrderedBefore] at hlast_lt_n
    rw[he_btn_eq_last] at hlast_lt_n
    absurd hlast_lt_n
    simp[Nat.le_iff_lt_or_eq, last.oWellFormed]
  have hn_in_head := Or.resolve_right he_btn_in_l hn_ne_last

  have hlast_in_tail : last ∈ [last] := by simp

  have hlast_in_l : last ∈ l := by simp[hlast_in_tail, hlist]
  have hlast_lt_len : List.idxOf last l < l.length := List.idxOf_lt_length_iff.mpr hlast_in_l

  have hn_lt_len : List.idxOf e_between l < l.length := List.idxOf_lt_length_iff.mpr hspare_n_in_l

  have hidx_n_lt_last : List.idxOf e_between l < List.idxOf last l :=
    List.ordered_mem_impl_ordered_idx l hlist hn_in_head hlast_in_tail hl_nodup

  have hn_lt_last := hsorted (List.idxOf e_between l) (List.idxOf last l) hn_lt_len hlast_lt_len hidx_n_lt_last
  simp[List.getElem_idxOf] at hn_lt_last
  absurd hlast_lt_n
  simp[Event.OrderedBefore,] at hn_lt_last
  simp[Event.OrderedBefore, Nat.le_iff_lt_or_eq, ]
  apply Or.intro_left
  have h : e_between.oStart < last.oEnd := by
    calc e_between.oStart < e_between.oEnd := e_between.oWellFormed
      _ < last.oStart := hn_lt_last
      _ < last.oEnd := last.oWellFormed
  exact h

-- (hinit_i : init.stateAt n e_req = IEntry n)
lemma Event.init_state_at_entry_is_same (init : InitialSystemState n) (e₁ e₂ : Event n)
  (hsame_entry : e₁.sameEntry n e₂)
  : (init.stateAt n e₁) = (init.stateAt n e₂) := by
  simp[InitialSystemState.stateAt]
  match e₁ with
  | .cacheEvent ce₁ =>
    match e₂ with
    | .cacheEvent ce₂ =>
      simp[InitialSystemState.cacheStates]
      have hsame_cid := hsame_entry.sameStruct
      simp[Event.sameStructure, Event.struct] at hsame_cid
      simp[hsame_cid]
    | .directoryEvent _ =>
      have hsame_cid := hsame_entry.sameStruct
      simp[Event.sameStructure, Event.struct] at hsame_cid
  | .directoryEvent de₁ =>
    match e₂ with
    | .cacheEvent ce₂ =>
      simp[InitialSystemState.cacheStates]
      have hsame_cid := hsame_entry.sameStruct
      simp[Event.sameStructure, Event.struct] at hsame_cid
    | .directoryEvent de₂ =>
      simp[InitialSystemState.cacheStates]
      have hsame_pinst := hsame_entry.sameStruct
      simp[Event.sameStructure, Event.struct] at hsame_pinst
      simp[hsame_pinst]

lemma Behaviour.list_upToEvent_with_imm_bot_pred_eq_upToPred_append
  (b : Behaviour n) (e_pred e : Event n) (he_in_b : e ∈ b) (himm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : eventsUpToEvent n b e = eventsUpToEvent n b e_pred ++ [e_pred] := by
  have hpred_at_e_struct := himm_bot_pred.isImmPred.bPred.sameEntry.sameStruct
  simp[Event.sameStructure] at hpred_at_e_struct
  have hpred_at_e_addr := himm_bot_pred.isImmPred.bPred.sameEntry.sameAddr
  simp[Event.sameAddr] at hpred_at_e_addr

  have he_at_e_struct : e.struct = e.struct := by rfl
  have he_at_e_addr : e.addr = e.addr := by rfl

  have he_in_l_in_b := b.eventsAtEntryOfListBottomEvents_in_b n e.struct e.addr
  have he_in_l_bottom := b.eventsAtEntryOfListBottomEvents_are_bottom n e.struct e.addr

  have hentry_es_sorted := b.eventsAtEventEntry_ordered_before_sorted n e
  have hentry_es_nodup := b.eventsAtEventEntry_no_dups n e

  let e_pred_at : EventAtEntry n b e.struct e.addr := ⟨e_pred,⟨himm_bot_pred.isImmPred.predInB, hpred_at_e_struct, hpred_at_e_addr⟩⟩
  let e_at      : EventAtEntry n b e.struct e.addr := ⟨e,⟨he_in_b,he_at_e_struct,he_at_e_addr⟩⟩

  have he_pred : e_pred_at = ⟨e_pred,⟨himm_bot_pred.isImmPred.predInB, hpred_at_e_struct, hpred_at_e_addr⟩⟩ := by simp[e_pred_at]
  have he      : e_at      = ⟨e,⟨he_in_b, he_at_e_struct, he_at_e_addr⟩⟩ := by simp[e_at]

  have hpred_in_l := b.bottom_e_in_b_impl_in_eventsAtEventEntry n e_pred himm_bot_pred.isImmPred.predInB himm_bot_pred.isBottomPred
  have he_in_l := b.bottom_e_in_b_impl_in_eventsAtEventEntry n e he_in_b himm_bot_pred.isBottomSucc
  rw[b.eventsAtEventEntry_eq_same_entry n e_pred e himm_bot_pred.isImmPred.bPred.sameEntry] at hpred_in_l

  have hidxOf_pred_in_l := List.idxOf_lt_length_of_mem hpred_in_l
  have hidxOf_e_in_l := List.idxOf_lt_length_of_mem he_in_l

  have hpred_imm_list_pred_e := b.eventsAtEventEntry_imm_pred_equiv n e.struct e.addr
    himm_bot_pred.isImmPred.predInB he_in_b
    hpred_at_e_struct hpred_at_e_addr
    he_at_e_struct he_at_e_addr
    himm_bot_pred

  simp[eventsUpToEvent, List.upToEvent]
  apply Eq.symm

  have hidx_pred_one_eq_idx_e := hpred_imm_list_pred_e.noIntermediate
  rw[hidx_pred_one_eq_idx_e]

  have hn_lt_len : List.idxOf e_pred (eventsAtEventEntry n b e) < (eventsAtEventEntry n b e).length := List.idxOf_lt_length_of_mem hpred_in_l
  have hn : [(eventsAtEventEntry n b e)[List.idxOf e_pred (eventsAtEventEntry n b e)]] = [e_pred] := by
    simp[List.idxOf_getElem hentry_es_nodup (List.idxOf e_pred (eventsAtEventEntry n b e)) hn_lt_len]
  rw[← hn]

  rw[b.eventsAtEventEntry_eq_same_entry n e_pred e himm_bot_pred.isImmPred.bPred.sameEntry]
  apply List.take_append_getElem hidxOf_pred_in_l

lemma Behaviour.state_after_eventsUpToEvent_has_e_pred_last
  (b : Behaviour n) (init : InitialSystemState n) (e_pred e : Event n) (he_in_b : e ∈ b) (himm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : (List.stateAfter n (eventsUpToEvent n b e) (InitialSystemState.stateAt n init e)).cache n =
    (eventsUpToEvent n b e_pred ++ [e_pred] |>.stateAfter n (InitialSystemState.stateAt n init e)).cache n :=
  by
  rw [b.list_upToEvent_with_imm_bot_pred_eq_upToPred_append n e_pred e he_in_b himm_bot_pred]

lemma Behaviour.state_after_eventsUpToEvent_eq_state_after_imm_bot_pred
  (b : Behaviour n) (init : InitialSystemState n) (e_pred e : Event n) (he_in_b : e ∈ b) (himm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : (List.stateAfter n (eventsUpToEvent n b e) (InitialSystemState.stateAt n init e)).cache n =
    (stateAfter n b (InitialSystemState.stateAt n init e_pred) e_pred).cache n :=
  by
  have hsame_entry := himm_bot_pred.isImmPred.bPred.sameEntry
  have hsame_init : (InitialSystemState.stateAt n init e_pred) = (InitialSystemState.stateAt n init e) :=
    e_pred.init_state_at_entry_is_same n (init) e hsame_entry
  simp[hsame_init]

  simp[stateAfter, stateBefore]
  rw [Behaviour.state_after_eventsUpToEvent_has_e_pred_last n b init e_pred e he_in_b himm_bot_pred]

lemma Behaviour.state_before_is_state_after_pred (b : Behaviour n) (init : InitialSystemState n)
  (e_pred e : Event n) (he_in_b : e ∈ b) (himm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : (stateBefore n b (InitialSystemState.stateAt n init e) e).cache n =
    (stateAfter n b (InitialSystemState.stateAt n init e_pred) e_pred).cache n :=
  by
  simp[stateBefore]
  apply Behaviour.state_after_eventsUpToEvent_eq_state_after_imm_bot_pred
  . case he_in_b => exact he_in_b
  . case himm_bot_pred => exact himm_bot_pred

/- This got added to mathlib! -/
-- lemma List.take_mem_append_eq_take {α} [DecidableEq α] (n m : α) (l : List α) (hn_in_head : n ∈ l)
--   : List.take (List.idxOf n l) l = List.take (List.idxOf n (l ++ [m])) (l ++ [m]) := by
--   rw[List.idxOf_append_of_mem hn_in_head]
--   rw[List.take_append_eq_append_take]
--   have hidxn_lt_len : (List.idxOf n l) < l.length := List.idxOf_lt_length_of_mem hn_in_head
--   have hidxn_le_len := Nat.le_of_lt hidxn_lt_len
--   have hidxn_sub_len_eq_zero := Nat.sub_eq_zero_iff_le.mpr hidxn_le_len
--   rw[hidxn_sub_len_eq_zero]
--   simp

lemma List.take_idxOf_append_eq_list {α} [DecidableEq α] (n : α) (l : List α) (hnodup : (l ++ [n]).Nodup) : List.take (List.idxOf n (l ++ [n])) (l ++ [n]) = l := by
  have hn_not_in_l : n ∉ l := by
    simp[List.nodup_append'] at hnodup
    exact hnodup.right
  simp[List.idxOf_append_of_notMem hn_not_in_l]

/-
lemma Behaviour.no_pred_obtains_perms_impl_req_has_no_perms'
  (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  (l_preds : List (Event n))
  (hreq_coherent : e_req.isCoherent n)
  (hreq_in_b : e_req ∈ b)
  (hreq_is_bottom : b.IsBottomEvent n e_req)
  (hreq_is_ce : e_req.isCacheEvent n)
  (hax6 : Behaviour.axRequestAccessesDirectory n)
  (hno_pred : ∀ e_predecessor ∈ b, ¬immBottomPredHasNoPermsAndLeavesStateAtLeast n b init e_predecessor e_req)
  (init_state : EntryState n)
  (hinit_i : init_state = IEntry n)
  : ¬ (Event.req n e_req).MRS ≤ EntryState.cache n (List.stateAfter n (l_preds) (init_state)) := by
  induction l_preds generalizing init_state with -- using List.reverseRecOn with
  | nil =>
    match he : e_req with
    | .cacheEvent ce =>
      /- For any request, the state it was made on is greater or equal to it's MRS. -/
      match hreq : ce.req with
      | ⟨⟨.w,true,.SC⟩,_⟩
      | ⟨⟨.r,true,.SC⟩,_⟩
      | ⟨⟨.w,true,.Rel⟩,_⟩
      | ⟨⟨.w,true,.Weak⟩,_⟩
      | ⟨⟨.r,false,.Weak⟩,_⟩
      | ⟨⟨.w,false,.Weak⟩,_⟩
      | ⟨⟨.w,false,.Rel⟩,_⟩
      | ⟨⟨.r,false,.Acq⟩,_⟩ =>
        all_goals simp [hinit_i]
        all_goals simp [List.stateAfter, EntryState.cache];
        all_goals simp [ValidRequest.MRS, Event.req, hreq];
        all_goals simp [LE.le, State.le, Option.le,];
        all_goals simp [ReadWrite.toPerms, ReadWrite.toRWPerms, LT.lt, LE.le, Option.le]
    | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce
  | cons head l_tail ih =>
    match hreq : e_req with
    | .cacheEvent ce_req =>
      simp[List.stateAfter]
      apply ih
      . case hinit_i =>

        sorry
    | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce
-/

lemma List.drop_idxOf_append_eq_append {α} [DecidableEq α] {n : α} {l_head : List α} (hnodup : (l_head ++ [n]).Nodup)
  : List.drop (List.idxOf n (l_head ++ [n])) (l_head ++ [n]) = [n] := by
  have hn_not_in_l_head : n ∉ l_head := by
    simp[List.nodup_append'] at hnodup
    exact hnodup.right
  simp[List.idxOf_append_of_notMem hn_not_in_l_head]

lemma Behaviour.reqMissingPerms_accesses_dir {b : Behaviour n} {init : InitialSystemState n} {e_req : Event n}
  (hreq_in_b : e_req ∈ b) (hreq_at_cache : e_req.isCacheEvent n)
  (hmissing_perms : b.reqMissingPerms n init e_req) (hax_req_encap_dir : Behaviour.axRequestAccessesDirectory n)
  : ∃ e_dir ∈ b, b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir := by
  /- First, start with the cases of missing permissions (`hmissing_perms`). Consider, ∀ e_req.req that's missing permissions.
  Second, identify the relevant cases where a request encapsulating a directory event (`hax_req_encap_dir`). -/
  -- simp[axRequestAccessesDirectory] at hax_req_encap_dir
  have hreq_encap_dir := hax_req_encap_dir b init e_req hreq_in_b
  simp[requestAccessesDirectoryWrapper] at hreq_encap_dir
  match he_req : e_req with
  | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_at_cache
  | .cacheEvent ce =>
    cases hmissing_perms
    . case downgrade hreq_is_down hreq_on_mrs =>
      match hreq_encap_dir with
      | .evictVdWB hvd_wb =>
        use hvd_wb.encapWBDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hvd_wb.encapWBDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right => exact hvd_wb.encapWBDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
      | .evictSCPutM hput_m =>
        use hput_m.encapPutMDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hput_m.encapPutMDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right => exact hput_m.encapPutMDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
      | .evictSCPutS hput_s =>
        use hput_s.encapPutSDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hput_s.encapPutSDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right => exact hput_s.encapPutSDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
      | .coherentRequest hcoherent_req_no_perms => simp_all [hcoherent_req_no_perms.notDowngrade]
      | .nonCoherentRelease hnc_rel => simp_all [Event.down, hnc_rel.notDowngrade]
      | .acquire hacq => simp_all [Event.down, hacq.notDowngrade]
      | .weakWrite hww => simp_all [Event.down, hww.notDowngrade]
      | .weakRead hwr => simp_all [Event.down, hwr.notDowngrade]

    . case noPermsForNonNcRelAcqWeakWrite hreq_not_down hreq_not_nc_rel_acq_ww hno_perms =>
      cases hreq_encap_dir
      case coherentRequest hcoherent_req_no_perms =>
        use hcoherent_req_no_perms.reqEncapDir.reqEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hcoherent_req_no_perms.reqEncapDir.reqEncapCorrDir.choose_spec.left
        . case h.right => exact hcoherent_req_no_perms.reqEncapDir.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent
      case weakRead hwr =>
        use hwr.encapDirEvent.reqEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hwr.encapDirEvent.reqEncapCorrDir.choose_spec.left
        . case h.right => exact hwr.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent

      . case nonCoherentRelease hnc_rel =>
        have his_nc_rel := hnc_rel.existsDirWb.choose_spec.right.isRelease
        simp[CacheEvent.isNcRelease, ValidRequest.isNcRelease] at his_nc_rel
        simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_not_nc_rel_acq_ww
        simp[his_nc_rel] at hreq_not_nc_rel_acq_ww
      . case acquire hacq =>
        have his_acq := hacq.isAcquire
        simp[CacheEvent.isAcquire, ValidRequest.isAcquire] at his_acq
        simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_not_nc_rel_acq_ww
        simp[his_acq] at hreq_not_nc_rel_acq_ww
      . case weakWrite hww =>
        have his_ww := hww.isWrite
        simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at his_ww
        simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
          CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
          ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite] at hreq_not_nc_rel_acq_ww
        simp[his_ww] at hreq_not_nc_rel_acq_ww
      . case evictVdWB hvd_wb =>
        have his_down := hvd_wb.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down
      . case evictSCPutM hput_m =>
        have his_down := hput_m.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down
      . case evictSCPutS hput_s =>
        have his_down := hput_s.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down

    . case ncRelAcqWeakWriteNotOnCoherentState hreq_not_down hreq_nc_rel_acq hno_perms =>
      cases hreq_encap_dir
      case nonCoherentRelease hnc_rel =>
        use hnc_rel.existsDirWb.choose
        apply And.intro
        . case h.left => exact hnc_rel.existsDirWb.choose_spec.left
        . case h.right => exact hnc_rel.existsDirWb.choose_spec.right.encapsDirWB.reqEncapCorrespondingDirEvent
      case acquire hacq =>
        use hacq.encapDirEvent.reqEncapCorrDir.choose
        apply And.intro
        . case h.left => exact hacq.encapDirEvent.reqEncapCorrDir.choose_spec.left
        . case h.right => exact hacq.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent

      . case coherentRequest hcoherent_req_no_perms =>
        have his_coh := hcoherent_req_no_perms.isCoherent
        simp[Event.req,] at his_coh
        simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
        cases hreq_nc_rel_acq
        . case inl his_acq => simp[his_acq] at his_coh
        . case inr his_nc_rel => simp[his_nc_rel] at his_coh
      . case weakWrite hww =>
        have his_weak_write := hww.isWrite
        simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at his_weak_write
        simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
        simp[his_weak_write] at hreq_nc_rel_acq
      . case weakRead hwr =>
        have his_weak_read := hwr.isRead
        simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at his_weak_read
        simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
          ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
        simp[his_weak_read] at hreq_nc_rel_acq
      . case evictVdWB hvd_wb =>
        have his_down := hvd_wb.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down
      . case evictSCPutM hput_m =>
        have his_down := hput_m.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down
      . case evictSCPutS hput_s =>
        have his_down := hput_s.isDowngrade
        simp[Event.down] at his_down
        simp[Event.down, his_down] at hreq_not_down

/-
/-- `Helper Lemma 1` in Lemma 3's re-write -/
lemma Behaviour.exists_predecessor_setting_state''
  (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  (hreq_in_b : e_req ∈ b)
  (l_preds : List (Event n))
  (hl_preds : l_preds = b.eventsUpToEvent n e_req)
  (hpreds_at_same_entry : ∀ e ∈ l_preds, b.eventAtEntry n e e_req.struct e_req.addr)
  (hpreds_pred_to_req : ∀ e ∈ l_preds, b.Predecessor n e e_req)
  (hpreds_are_bottom : ∀ e' ∈ l_preds, e'.isBottomAtEntry n b e_req.struct e_req.addr)
  (hreq_not_downgrade : ¬ e_req.down)
  (hhave_perms : reqHasPerms n b init e_req)
  (hinit_i : init.stateAt n e_req = IEntry n)
  (hcoherent_perms : (b.stateBefore n (init.stateAt n e_req) e_req).cache ≠ Vd)
  (hax6 : Behaviour.axRequestAccessesDirectory n)
  (hreq_is_ce : e_req.isCacheEvent n)
  :
  ∃ e_dir ∈ b, e_dir.isDirectoryEvent ∧ b.dirAccessOfRequest n init e_req e_dir
  := by
  /- identify the predecessor event `e_pred` such that `e_pred` has a succeeding state of `s'` such that `s'` is greater than or equal
  to the state `e_req` is made on, and `e_pred` encapsulates an e_dir by Axiom 6.
  Perform `backwards induction` on the list `l_preds` of events before `e_req`.
  -/
  /-
  have hpreds_at_same_entry : ∀ e ∈ b.eventsUpToEvent n e_req, b.eventAtEntry n e e_req.struct e_req.addr := by
    -- subst l_preds
    apply Behaviour.eventsUpToEvent_are_at_entry
  -/
  /- First, state the state e_req is made on. With an empty pred list, it's I. -/
  let state_made_on := b.stateBefore n (init.stateAt n e_req) e_req |>.cache
  have h_made_on : state_made_on = (stateBefore n b (InitialSystemState.stateAt n init e_req) e_req).cache := by
    subst state_made_on; rfl
  rw[hinit_i] at h_made_on
  unfold stateBefore at h_made_on

  have hexists_e_pred : ∃ e_pred ∈ b, b.immBottomPredHasNoPermsAndLeavesStateAtLeast n init e_pred e_req :=
    by
    by_contra hno_pred
    simp at hno_pred
    /- if all events in `l_preds` are not imm bottom pred that get perms for `e_req`, then by def of state before `e_req`,
    then `e_req`'s state it's made on does not have sufficient permissions!
    -/
    /- First show, state made on is at least `e_req`'s request's MRS. -/

    /- show the state `s` that `e_req` is made on is greater than `e_req.req.MRS` (using `hhave_perms`).
    We can then state if all `l_preds` are `¬immBottomPredEncapDirAndHasNoPermsAndLeavesStateAtLeast`,
    the `s` is not greater than `e_req.req.MRS`.
     -/
    cases hhave_perms
    . case hasPerms h_is_coherent h_has_perms =>
      dsimp[hasPerms] at h_has_perms

      subst state_made_on
      rw[h_made_on] at h_has_perms

      rw[← hl_preds] at h_has_perms
      /- show that because of `hno_pred` (no predecessor gets permissions for `e_req`)
      all the predecessor events to `e_req` do not obtain permissions for `e_req` as per h_has_perms. -/
      have hno_perms : ¬ (Event.req n e_req).MRS ≤ EntryState.cache n (List.stateAfter n (l_preds) (IEntry n)) :=
        b.no_pred_obtains_perms_impl_req_has_no_perms n init e_req l_preds h_is_coherent hreq_in_b
          hreq_is_ce hpreds_at_same_entry hpreds_pred_to_req hpreds_are_bottom hax6 hno_pred
      absurd h_has_perms
      exact hno_perms
    . case ncRelAcqWeakWriteHasCoherentPerms => sorry
    . case ncWeakReadHasPermsNotVd => sorry

  /- Can use hexists_e_pred to show it encapsulates a directory event.
  have h := hexists_e_pred.choose_spec.right
  simp[immBottomPredHasNoPermsAndLeavesStateAtLeast] at h
  simp[ImmediateBottomPredSatisfyingProp] at h
  have t := h.satisfyP
  simp[Event.PropOnEvent] at t
  have z := t.missingPerms
  -/
  --[TODO]: write a helper lemma to state that a request without perms accesses the directory.
  -- Use the directory event to fill in the `_` below.
  -- [TODO] : July 5, 2025

  have hpred_no_perm_gets_perms := hexists_e_pred.choose_spec.right
  simp[immBottomPredHasNoPermsAndLeavesStateAtLeast, ImmediateBottomPredSatisfyingProp] at hpred_no_perm_gets_perms
  have hprop_pred_no_perms_get_perms := hpred_no_perm_gets_perms.satisfyP
  simp[Event.PropOnEvent] at hprop_pred_no_perms_get_perms
  have hpred_no_perms := hprop_pred_no_perms_get_perms.missingPerms
  simp[reqMissingPerms] at hpred_no_perms

  have hpred_at_cache : hexists_e_pred.choose.isCacheEvent n := by
    have hpred_same_struct_req := hpred_no_perm_gets_perms.isImmBottomPred.isImmPred.sameStructure
    simp[Event.sameStructure, Event.struct] at hpred_same_struct_req
    simp[Event.isCacheEvent] at hreq_is_ce
    simp[Event.isCacheEvent]
    match hreq : e_req with
    | .directoryEvent _ => simp_all
    | .cacheEvent ce_req =>
      simp[hreq] at hpred_same_struct_req
      match hpred : hexists_e_pred.choose with
      | .directoryEvent _ => simp_all
      | .cacheEvent ce_pred => simp_all

  have hpred_access_dir : ∃ e_dir ∈ b,
    cacheEncapsulatesCorrespondingDirEvent n b (InitialSystemState.stateAt n init hexists_e_pred.choose) true
    hexists_e_pred.choose e_dir :=
      b.reqMissingPerms_accesses_dir n init
        hexists_e_pred.choose hexists_e_pred.choose_spec.left hpred_at_cache hpred_no_perms hax6

  have hhas_pred_getting_perms : dirAccessOfRequest n b init e_req hpred_access_dir.choose := by
    apply dirAccessOfRequest.orderBeforeDir
    . case hreq_has_perms => exact hhave_perms
    . case hpred_accesses_dir => exact hpred_access_dir.choose_spec.right

  use hpred_access_dir.choose
  apply And.intro
  . case h.left => exact hpred_access_dir.choose_spec.left
  . case h.right =>
    apply And.intro
    . case left => exact hpred_access_dir.choose_spec.right.isDir
    . case right =>
      exact hhas_pred_getting_perms
          /- Show that there must be a predecessor that accesses the directory, and it is the immediate predecessor that accesses the directory.
          Use the contrapositive. -/
-/

structure Behaviour.exists_predecessor_setting_state (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) where
  hreq_has_perms : b.reqHasPerms n init e_req
  hexists_pred_getting_perms : b.reqHasPermsSoDirPred n init e_req
  hpred_accesses_dir : ∃ e_dir ∈ b, b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose e_dir
  -- hinter_leaves_state_at_least : b.stateBeforeAndAfterAtLeast n init hexists_pred_getting_perms.choose e_req
  hinter_leaves_state_at_least : ∀ e_inter ∈ b,
    e_inter.OrderedBetween n hexists_pred_getting_perms.choose e_req →
    b.stateBeforeAndAfterAtLeast n init e_inter e_req
  hinter_same_protocol : hexists_pred_getting_perms.choose.sameProtocol n e_req
  hreq_not_down : ¬ e_req.down

/-- Axiom 7 Redux. -/
structure Behaviour.exists_vd_successor_wb_or_get_sw (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) where
  hweak_read_on_vd : b.ncWeakReqOnVd n init e_req
  hsucc_encap_dir : ∃ e_dir ∈ b, b.immBottomSuccOnVdEncapCorrDir n init e_req e_dir
  /- All requests between the predecessor that
     gets permissions (`hsucc_encap_dir.choose`) and `e_req` have permissions (like `b.reqHasPerms`),
     and leave the cache state with at least as much permissions (`b.reqLeavesStateAtLeast`  n `e_inter` init e_req.req.MRS).
     -/
  -- hinter_leaves_state_at_least : b.stateBeforeAndAfterAtLeast n init hsucc_encap_dir.choose e_req
  hsucc_same_protocol : hsucc_encap_dir.choose_spec.right.choose.sameProtocol n e_req
  hreq_not_down : ¬ e_req.down

structure Behaviour.has_perms_or_vd_exists_e_dir_before_or_after where
  hasPermsDirBefore : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req : Event n, b.exists_predecessor_setting_state n init e_req
  vdDirAfter : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req : Event n, b.exists_vd_successor_wb_or_get_sw n init e_req

lemma Behaviour.contradiction_of_dir_state_from_state_after_from_cache_events
  {dir_state} (e_req : Event n) {l : List (Event n)} (hce : e_req.isCacheEvent n)
  (hall_ : ∀ e ∈ l, e.isCacheEvent)
  (entry_s : EntryState n)
  (hentry_s : entry_s.isCacheState)
  (heq : (List.stateAfter n l entry_s) = Sum.inr dir_state)
  : False := by
  induction l generalizing entry_s with
  | nil =>
    simp[List.stateAfter, InitialSystemState.stateAt] at heq
    match hreq : e_req with
    | .directoryEvent _ => simp[Event.isCacheEvent, hreq] at hce
    | .cacheEvent ce => match entry_s with
      | .inl cs => simp[hreq] at heq
      | .inr _ => simp[EntryState.isCacheState] at hentry_s
  | cons h t ih =>
    simp[List.stateAfter, InitialSystemState.stateAt] at heq
    match hreq : e_req with
    | .directoryEvent _ => simp[Event.isCacheEvent, hreq] at hce
    | .cacheEvent ce =>
      apply ih
      . case hall_ =>
        intro event he_in_t
        apply hall_ event (by simp[he_in_t])
      . case hentry_s =>
        have hsucc_is_cache_s : (Event.SucceedingState n h entry_s).isCacheState := by
          simp[Event.SucceedingState]
          match hh : h with
          | .cacheEvent ce => simp[EntryState.isCacheState]
          | .directoryEvent _ =>
            have hcache_h := hall_ h (by simp[hh])
            simp[Event.isCacheEvent, hh] at hcache_h
        apply hsucc_is_cache_s
      . case heq =>
        apply heq

lemma Behaviour.stateBefore_cache_event_is_cache (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) (hce : e_req.isCacheEvent n)
  : (stateBefore n b (InitialSystemState.stateAt n init e_req) e_req).isCacheState := by
  simp[EntryState.isCacheState, ]
  -- simp[listBottomEventsAtEntry', bottomEventsAtEntry', Set.finSetEvents']
  split
  . case h_1 entry_state cache_state heq =>
    match (eventsUpToEvent n b e_req) with
    | .nil => simp
    | .cons h t =>
      simp
  . case h_2 entry_state dir_state heq =>
    simp [stateBefore] at heq
    apply Behaviour.contradiction_of_dir_state_from_state_after_from_cache_events
    . case hce => exact hce
    . case hall_ =>
      apply eventsUpToEvent_at_cache_all_cache
      . case b => exact b
      . case he_cache => exact hce
    . case hentry_s =>
      have hinit_entry : (InitialSystemState.stateAt n init e_req).isCacheState := by
        simp[InitialSystemState.stateAt]
        match e_req with
        | .cacheEvent _ => simp[EntryState.isCacheState]
        | .directoryEvent _ => simp[Event.isCacheEvent] at hce
      exact hinit_entry
    . case heq => exact heq

-- Helper lemmas for the three cases of dirAccessOfRequest

/-- Helper: Find directory event for request with permissions (orderBeforeDir case) -/
private lemma Behaviour.exists_e_dir_orderBeforeDir {n : ℕ} (b : Behaviour n) (init : InitialSystemState n)
  (e_req : Event n) (he_req_in_b : e_req ∈ b)
  (hhas_perms : b.reqHasPerms n init e_req)
  (hdir_before_after : Behaviour.has_perms_or_vd_exists_e_dir_before_or_after n)
  : ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir := by
  have hexists_pred_dir := hdir_before_after.hasPermsDirBefore b init e_req
  use hexists_pred_dir.hpred_accesses_dir.choose
  apply And.intro
  . case h.left => exact hexists_pred_dir.hpred_accesses_dir.choose_spec.left
  . case h.right =>
    apply Behaviour.dirAccessOfRequest.orderBeforeDir
    . case hreq_has_perms => exact hhas_perms
    . case hpred_accesses_dir => exact hexists_pred_dir.hpred_accesses_dir.choose_spec.right
    . case hinter_leaves_state_at_least => exact hexists_pred_dir.hinter_leaves_state_at_least
    . case hpred_same_protocol => exact hexists_pred_dir.hinter_same_protocol
    . case hnot_down => exact hexists_pred_dir.hreq_not_down

/-- Helper: Find directory event for request without permissions (encapDir case) -/
private lemma Behaviour.exists_e_dir_encapDir {n : ℕ} (b : Behaviour n) (init : InitialSystemState n)
  (e_req : Event n) (he_req_in_b : e_req ∈ b)
  (hreq_cache : e_req.isCacheEvent)
  (hno_perms : b.reqMissingPerms n init e_req)
  (hreq_encap_dir : Behaviour.axRequestAccessesDirectory n)
  : ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir := by
  have hencap_dir := Behaviour.reqMissingPerms_accesses_dir n he_req_in_b hreq_cache hno_perms hreq_encap_dir
  use hencap_dir.choose
  apply And.intro
  . case h.left => simp[hencap_dir.choose_spec.left]
  . case h.right =>
    apply Behaviour.dirAccessOfRequest.encapDir
    . case hreq_missing_perms => exact hno_perms
    . case hencap_dir => exact hencap_dir.choose_spec.right

/-- Helper: Find directory event for weak request on Vd (orderAfterDir case) -/
private lemma Behaviour.exists_e_dir_orderAfterDir {n : ℕ} (b : Behaviour n) (init : InitialSystemState n)
  (e_req : Event n) (he_req_in_b : e_req ∈ b)
  (hreq_on_vd : b.ncWeakReqOnVd n init e_req)
  (hdir_before_after : Behaviour.has_perms_or_vd_exists_e_dir_before_or_after n)
  : ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir := by
  have hexists_dir_after := hdir_before_after.vdDirAfter b init e_req
  use hexists_dir_after.hsucc_encap_dir.choose
  apply And.intro
  . case h.left => exact hexists_dir_after.hsucc_encap_dir.choose_spec.left
  . case h.right =>
    apply Behaviour.dirAccessOfRequest.orderAfterDir
    . case hweak_read_on_vd => exact hreq_on_vd
    . case hsucc_same_protocol => exact hexists_dir_after.hsucc_same_protocol
    . case hnot_down => exact hexists_dir_after.hreq_not_down

/-- Helper: Find directory event for evict request (encapDir via downgrade) -/
private lemma Behaviour.exists_e_dir_evict {n : ℕ} (b : Behaviour n) (init : InitialSystemState n)
  (e_req : Event n)
  (hdown : e_req.down)
  (hmrs : b.evictOnMRSState n init e_req)
  (hencap : b.evictEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req)
  : ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir := by
  use hencap.evictEncapCorrDir.choose
  apply And.intro
  . case h.left => exact hencap.evictEncapCorrDir.choose_spec.left
  . case h.right =>
    apply dirAccessOfRequest.encapDir
    apply reqMissingPerms.downgrade
    . case hreq_missing_perms.hreq_is_down => exact hdown
    . case hreq_missing_perms.hreq_on_mrs_state => exact hmrs
    . case hencap_dir => exact hencap.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent

-- [TODO] constrain goal to say not just `e_req` relates `e_dir`, but either encapsulates if lacking permissions, or a previous one if have perms,
-- of a future one if Weak Non-Coherent on Vd
/-- `Lemma 3.` For each Cache Request Event `e_req`, there exists a unique event `e_dir` relating `e_req` to the total order of events at
`e_req`'s corresonponding Directory entry. -/
lemma Behaviour.exists_e_dir_access_of_e_req (b : Behaviour n) (init : InitialSystemState n)
(e_req : Event n) (he_req_in_b : e_req ∈ b)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n)
-- (hvd_wb_later : Behaviour.vdCacheEntryWriteBackLater n b e_req init)
-- (hreq_not_down : ¬ e_req.down)
(hdir_before_after : Behaviour.has_perms_or_vd_exists_e_dir_before_or_after n)
  :
  ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir
  := by
  have ax6 := hreq_encap_dir b init e_req he_req_in_b
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases hce : e_req
  . case cacheEvent ce =>
    match hdown : ce.down with
    | false =>
      match hreq : ce.req with
      | ⟨⟨rw,true,consistency⟩, hvalid_req⟩ =>
        have hnot_down : ¬ (Event.cacheEvent ce).down := by simp[Event.down, hdown]
        have hreq_coh : (Event.cacheEvent ce).isCoherent := by simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq]
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          have hhas_perms := reqHasPerms.hasPerms hreq_coh hreq_has_perms
          exact b.exists_e_dir_orderBeforeDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hhas_perms hdir_before_after
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          have hreq_not_rel_acq_ww : (Event.cacheEvent ce).notNcRelAcqWeakWrite := by
            simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hreq_no_perms : eventOnStateNoPerms n b init (Event.cacheEvent ce) := by
            subst state_req_made_on event_req
            simp[eventOnStateNoPerms, eventOnStateHasPerms, Event.req, hreq_has_perms]
          -- have hhas_perms := Behaviour.reqHasPerms.hasPerms hreq_coh hreq_has_perms
          have hno_perms := reqMissingPerms.noPermsForNonNcRelAcqWeakWrite hnot_down hreq_not_rel_acq_ww hreq_no_perms
          -- (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req)
          have hce_in_b : Event.cacheEvent ce ∈ b := by
            simp[hce,] at he_req_in_b
            simp[he_req_in_b]
          have hreq_cache : (Event.cacheEvent ce).isCacheEvent := by simp[Event.isCacheEvent]
          exact b.exists_e_dir_encapDir init (Event.cacheEvent ce) hce_in_b hreq_cache hno_perms hreq_encap_dir
      | ⟨⟨.r,false,.Weak⟩, _⟩ =>
        have hnot_down : ¬ (Event.cacheEvent ce).down := by simp[Event.down, hdown]
        have hreq_wr : (Event.cacheEvent ce).isNcWeakRead := by
          simp[Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, hreq]
        -- have hreq_coh : (Event.cacheEvent ce).isCoherent := by simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq]
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          by_cases hnot_on_vd : state_req_made_on ≠ Vd
          . case pos =>
            have hwr_perms : Behaviour.reqHasPermsNotVd n b init (Event.cacheEvent ce) := by
              constructor
              . case hasPerms =>
                subst state_req_made_on event_req
                simp[hasPerms, Event.req, hreq_has_perms]
              . case notOnVd =>
                subst state_req_made_on event_req
                simp[stateReqMadeOn, hnot_on_vd]
            have hreq_wr : (Event.cacheEvent ce).isNcWeakRead := by
              simp[Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead, hreq]
            have hhas_perms := reqHasPerms.ncWeakReadHasPermsNotVd hreq_wr hwr_perms
            exact b.exists_e_dir_orderBeforeDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hhas_perms hdir_before_after
          . case neg =>
            simp at hnot_on_vd
            /- [NOTE] Use Behaviour.hasPermsNotVd .ncWeakReadHasPermsNotVd
            in Behaviour.dirAccessOfRequest from the Goal to show this case isn't true. -/
            have hreq_on_vd : b.ncWeakReqOnVd n init (Event.cacheEvent ce) := by
              constructor
              . case notDown => simp[hnot_down]
              . case weakReq =>
                simp[Event.isNcWeak]
                simp[Event.isNonCoherent, Event.isWeak]
                apply And.intro
                . case left => simp[hreq]
                . case right => simp[hreq]
              . case reqOnOrAfterVd =>
                subst state_req_made_on event_req
                apply Or.intro_left
                simp[hnot_on_vd]
              . case reqCache => simp[Event.isCacheEvent]
            exact b.exists_e_dir_orderAfterDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hreq_on_vd hdir_before_after
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          have hreq_not_rel_acq_ww : (Event.cacheEvent ce).notNcRelAcqWeakWrite := by
            simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hreq_no_perms : eventOnStateNoPerms n b init (Event.cacheEvent ce) := by
            subst state_req_made_on event_req
            simp[eventOnStateNoPerms, eventOnStateHasPerms, Event.req, hreq_has_perms]
          -- have hhas_perms := Behaviour.reqHasPerms.hasPerms hreq_coh hreq_has_perms
          have hno_perms := reqMissingPerms.noPermsForNonNcRelAcqWeakWrite (b:=b) (init:=init) hnot_down hreq_not_rel_acq_ww hreq_no_perms
          -- (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req)
          have hce_in_b : Event.cacheEvent ce ∈ b := by
            simp[hce,] at he_req_in_b
            simp[he_req_in_b]
          have hreq_cache : (Event.cacheEvent ce).isCacheEvent := by simp[Event.isCacheEvent]
          exact b.exists_e_dir_encapDir init (Event.cacheEvent ce) hce_in_b hreq_cache hno_perms hreq_encap_dir
      | ⟨⟨.r,false,.Acq⟩, _⟩ =>
        have hnot_down : ¬ (Event.cacheEvent ce).down := by simp[Event.down, hdown]
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on.c ∧ ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          have hreq_rel_acq_ww : (Event.cacheEvent ce).isNcRelAcqWeakWrite := by
            simp[Event.isNcRelAcqWeakWrite,
              Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hwr_perms : b.reqHasPermsOnCoherentState n init (Event.cacheEvent ce) := by
            constructor
            . case hasPerms =>
              subst state_req_made_on event_req
              simp[hasPerms, Event.req, hreq_has_perms]
            . case onCoherentState =>
              simp[reqMadeOnCoherentState]
              exact hreq_has_perms.left
          have hhas_perms := reqHasPerms.ncRelAcqWeakWriteHasCoherentPerms hreq_rel_acq_ww hwr_perms
          exact b.exists_e_dir_orderBeforeDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hhas_perms hdir_before_after
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          have hreq_not_rel_acq_ww : (Event.cacheEvent ce).isNcRelAcq := by
            simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hreq_no_perms : acqRelWeakWriteNoPerms n b init (Event.cacheEvent ce) := by
            simp only [acqRelWeakWriteNoPerms]
            simp only [eventOnCoherentState, eventOnStateHasPerms, Event.req]
            subst state_req_made_on event_req
            simp [hreq_has_perms]
          -- have hhas_perms := Behaviour.reqHasPerms.hasPerms hreq_coh hreq_has_perms
          have hno_perms := reqMissingPerms.ncRelAcqWeakWriteNotOnCoherentState (b:=b) (init:=init) hnot_down hreq_not_rel_acq_ww hreq_no_perms
          -- (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req)
          have hce_in_b : Event.cacheEvent ce ∈ b := by
            simp[hce,] at he_req_in_b
            simp[he_req_in_b]
          have hreq_cache : (Event.cacheEvent ce).isCacheEvent := by simp[Event.isCacheEvent]
          exact b.exists_e_dir_encapDir init (Event.cacheEvent ce) hce_in_b hreq_cache hno_perms hreq_encap_dir
      | ⟨⟨.w,false,.Weak⟩, _⟩ =>
        have hnot_down : ¬ (Event.cacheEvent ce).down := by simp[Event.down, hdown]
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on.c ∧ ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          have hreq_rel_acq_ww : (Event.cacheEvent ce).isNcRelAcqWeakWrite := by
            simp[Event.isNcRelAcqWeakWrite,
              Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hwr_perms : b.reqHasPermsOnCoherentState n init (Event.cacheEvent ce) := by
            constructor
            . case hasPerms =>
              subst state_req_made_on event_req
              simp[hasPerms, Event.req, hreq_has_perms]
            . case onCoherentState =>
              simp[reqMadeOnCoherentState]
              exact hreq_has_perms.left
          have hhas_perms := reqHasPerms.ncRelAcqWeakWriteHasCoherentPerms hreq_rel_acq_ww hwr_perms
          exact b.exists_e_dir_orderBeforeDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hhas_perms hdir_before_after
        . case neg =>
          /- Show a future event writes back. -/
            have hreq_on_vd : b.ncWeakReqOnVd n init (Event.cacheEvent ce) := by
              constructor
              . case notDown => simp[hnot_down]
              . case weakReq =>
                simp[Event.isNcWeak]
                simp[Event.isNonCoherent, Event.isWeak]
                apply And.intro
                . case left => simp[hreq]
                . case right => simp[hreq]
              . case reqOnOrAfterVd =>
                subst state_req_made_on event_req
                apply Or.intro_right
                . case h =>
                  simp only [not_and_or] at hreq_has_perms
                  apply Or.elim
                  apply hreq_has_perms
                  . case left =>
                    intro hno_perms
                    rw[state_after_eq_succeeding_state_before]
                    have hstate_before_cache : (stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)).isCacheState := by
                      apply stateBefore_cache_event_is_cache
                      . case hce => simp[Event.isCacheEvent]
                    match he_state : (stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)) with
                    | .inl state =>
                      match hs : state with
                      | ⟨some .wr, true⟩
                      | ⟨some .r, true⟩
                      | ⟨none, true⟩ =>
                        rw[he_state] at hno_perms
                        simp[EntryState.cache, State.c] at hno_perms
                      | ⟨some .wr, false⟩
                      | ⟨some .r, false⟩
                      | ⟨none, false⟩ =>
                        rw[he_state] at hno_perms
                        simp[Event.SucceedingState]
                        simp[CacheEvent.SucceedingState]
                        simp[hdown]
                        simp[ValidRequest.RequestState, hreq]
                        simp[EntryState.cache]
                    | .inr _ => simp [he_state, EntryState.isCacheState] at hstate_before_cache
                  . case right =>
                    intro hno_perms
                    rw[state_after_eq_succeeding_state_before]
                    have hstate_before_cache : (stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)).isCacheState := by
                      apply stateBefore_cache_event_is_cache
                      . case hce => simp[Event.isCacheEvent]
                    match he_state : (stateBefore n b (InitialSystemState.stateAt n init (Event.cacheEvent ce)) (Event.cacheEvent ce)) with
                    | .inl state =>
                      match hs : state with
                      | ⟨some .wr, true⟩ =>
                        rw[he_state] at hno_perms
                        simp[EntryState.cache, State.c, hreq,] at hno_perms
                        simp [ValidRequest.MRS, LE.le, State.le, LT.lt, Option.le] at hno_perms
                      | ⟨some .r, true⟩
                      | ⟨none, true⟩
                      | ⟨some .wr, false⟩
                      | ⟨some .r, false⟩
                      | ⟨none, false⟩ =>
                        rw[he_state] at hno_perms
                        simp[Event.SucceedingState]
                        simp[CacheEvent.SucceedingState]
                        simp[hdown]
                        simp[ValidRequest.RequestState, hreq]
                        simp[EntryState.cache]
                    | .inr _ => simp [he_state, EntryState.isCacheState] at hstate_before_cache
              . case reqCache => simp[Event.isCacheEvent]

            exact b.exists_e_dir_orderAfterDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hreq_on_vd hdir_before_after
      | ⟨⟨.w,false,.Rel⟩, _⟩ =>
        have hnot_down : ¬ (Event.cacheEvent ce).down := by simp[Event.down, hdown]
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on.c ∧ ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          have hreq_rel_acq_ww : (Event.cacheEvent ce).isNcRelAcqWeakWrite := by
            simp[Event.isNcRelAcqWeakWrite,
              Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hwr_perms : b.reqHasPermsOnCoherentState n init (Event.cacheEvent ce) := by
            constructor
            . case hasPerms =>
              subst state_req_made_on event_req
              simp[hasPerms, Event.req, hreq_has_perms]
            . case onCoherentState =>
              simp[reqMadeOnCoherentState]
              exact hreq_has_perms.left
          have hhas_perms := reqHasPerms.ncRelAcqWeakWriteHasCoherentPerms hreq_rel_acq_ww hwr_perms
          exact b.exists_e_dir_orderBeforeDir init (Event.cacheEvent ce) (by simp[hce] at he_req_in_b; exact he_req_in_b) hhas_perms hdir_before_after
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          have hreq_not_rel_acq_ww : (Event.cacheEvent ce).isNcRelAcq := by
            simp[Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease, Event.isNcWeakWrite,
              CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
              ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
              hreq]
          have hreq_no_perms : acqRelWeakWriteNoPerms n b init (Event.cacheEvent ce) := by
            simp only [acqRelWeakWriteNoPerms]
            simp only [eventOnCoherentState, eventOnStateHasPerms, Event.req]
            subst state_req_made_on event_req
            simp [hreq_has_perms]
          -- have hhas_perms := Behaviour.reqHasPerms.hasPerms hreq_coh hreq_has_perms
          have hno_perms := reqMissingPerms.ncRelAcqWeakWriteNotOnCoherentState (b:=b) (init:=init) hnot_down hreq_not_rel_acq_ww hreq_no_perms
          -- (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req)
          have hce_in_b : Event.cacheEvent ce ∈ b := by
            simp[hce,] at he_req_in_b
            simp[he_req_in_b]
          have hreq_cache : (Event.cacheEvent ce).isCacheEvent := by simp[Event.isCacheEvent]
          exact b.exists_e_dir_encapDir init (Event.cacheEvent ce) hce_in_b hreq_cache hno_perms hreq_encap_dir
    | true =>
      simp[hce] at ax6
      match ax6 with
      | .evictVdWB he_vd =>
        exact b.exists_e_dir_evict init (Event.cacheEvent ce) he_vd.isDowngrade he_vd.madeOnMrs he_vd.encapWBDirEvent
      | .evictSCPutM hputm =>
        exact b.exists_e_dir_evict init (Event.cacheEvent ce) hputm.isDowngrade hputm.madeOnMrs hputm.encapPutMDirEvent
      | .evictSCPutS hputs =>
        exact b.exists_e_dir_evict init (Event.cacheEvent ce) hputs.isDowngrade hputs.madeOnMrs hputs.encapPutSDirEvent
      | .nonCoherentRelease hnc_rel =>
        absurd hnc_rel.notDowngrade
        simp[hdown]
      | .weakWrite hweak_w =>
        absurd hweak_w.ncWeakReq.notDowngrade
        simp[hdown]
      | .coherentRequest hcoh_req =>
        absurd hcoh_req.notDowngrade
        simp[Event.down, hdown]
      | .acquire hacq =>
        absurd hacq.notDowngrade
        simp[Event.down, hdown]
      | .weakRead hweak_r =>
        absurd hweak_r.ncWeakReq.notDowngrade
        simp[hdown]
  . case directoryEvent _ => simp [hce] at ax6

/- Helper lemma: orderAfterDir succ is cache event -/
lemma orderAfterDir_succ_is_cache_event
  (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop)
  (hsucc_spec : Behaviour.ImmediateBottomSuccSatisfyingProp n b e_pred e_succ p)
  (he_pred_is_cache : e_pred.isCacheEvent)
  : e_succ.isCacheEvent := by
  match hsucc_ev : e_succ with
  | Event.cacheEvent _ => simp [Event.isCacheEvent]
  | Event.directoryEvent de_succ =>
    exfalso
    -- e_pred and e_succ have same struct from sameEntry property
    have hsame_struct : Event.sameStructure n e_pred (Event.directoryEvent de_succ) :=
      hsucc_spec.isImmBottomSucc.sameEntry.sameStruct
    -- e_pred is a cache event, so match on it to show struct contradiction
    match e_pred with
    | Event.cacheEvent ce_pred =>
      -- Struct.cache ≠ Struct.directory, so we get a contradiction
      simp only [Event.sameStructure, Event.struct] at hsame_struct
      -- hsame_struct should now be something like: Struct.cache ce_pred.cid = Struct.directory de_succ.pInst
      -- This is false, so we can derive a contradiction
      cases hsame_struct
    | Event.directoryEvent _ =>
      -- e_pred is a directory event, contradicting he_pred_is_cache
      simp [Event.isCacheEvent] at he_pred_is_cache

/- Helper lemma: orderBeforeDir pred is cache event -/
lemma orderBeforeDir_pred_is_cache_event
  (b : Behaviour n)
  (init : InitialSystemState n)
  (e_req : Event n)
  (hexists_pred_r : b.reqHasPermsSoDirPred n init e_req)
  (he_req_is_cache : e_req.isCacheEvent)
  : hexists_pred_r.choose.isCacheEvent := by
  -- First, case split on e_req while we still have the clean state
  match e_req with
  | Event.directoryEvent _ =>
    -- e_req is a directory event, which contradicts he_req_is_cache
    simp [Event.isCacheEvent] at he_req_is_cache
  | Event.cacheEvent ce_req =>
    -- e_req is a cache event, so we can proceed
    -- Get the predecessor specification from existential
    have hpred_spec := hexists_pred_r.choose_spec.right
    -- Unfold the immBottomPredHasNoPermsAndLeavesStateAtLeast definition
    simp [Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at hpred_spec
    -- Access the ImmediateBottomPredSatisfyingProp
    simp [Behaviour.ImmediateBottomPredSatisfyingProp] at hpred_spec
    -- Extract the predecessor relationships
    have hpred_imm_pred := hpred_spec.isImmPred
    have hpred_bpred := hpred_imm_pred.bPred
    have hpred_same_entry := hpred_bpred.sameEntry
    -- sameStruct extracts the struct equality
    have hpred_same_struct := hpred_same_entry.sameStruct
    simp [Event.sameStructure] at hpred_same_struct
    -- hpred_same_struct : Event.sameStructure n hexists_pred_r.choose (Event.cacheEvent ce_req)

    -- Now show hexists_pred_r.choose must be a cache event
    match hpred : hexists_pred_r.choose with
    | Event.cacheEvent _ =>
      simp [Event.isCacheEvent]
    | Event.directoryEvent de_pred =>
      -- Contradiction: a directory event cannot have same structure as cache event
      simp [Event.struct,] at hpred_same_struct
      -- rw[hpred] at hpred_same_struct
      split at hpred_same_struct
      . case h_1 e_pred e_pred_dir hpred_dir =>
        simp at hpred_same_struct
      . case h_2 e_pred e_pred_cache hpred_cache =>
        simp at hpred_same_struct
        grind
      -- exfalso
      -- Unfold sameStructure to get struct equality
      -- Use hpred to substitute hexists_pred_r.choose with Event.directoryEvent de_pred
      -- This will simplify the match in hpred_same_struct to Struct.directory de_pred.pInst
      -- rw[] at hpred_same_struct

/-- Def. Prop constraints for Def 2.37 case where the request has coherent permissions and is then defined as it's own linearization event. -/
structure Behaviour.requestWithCoherentPermsLinearizes (b : Behaviour n) (init : InitialSystemState n) (e_req e_lin : Event n) : Prop where
  reqHasPerms : b.reqHasPerms n init e_req
  -- reqHasCoherentPerms : b.eventOnCoherentStateAtLeastMRS n e_req init
  reqIsLin : e_lin = e_req

/-
/-- Def. Wrapper structure : Prop. for Def 2.37-/
structure Behaviour.requestWithCoherentPermLin : Prop where
  linearizingRequest : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∃ e_lin : Event n,
    b.requestWithCoherentPermsLinearizes n init e_req e_lin
-/

structure Behaviour.requestLinearizesAtDirectory (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir e_lin : Event n) where
  isDir : e_dir.isDirectoryEvent
  reqCorrespondsToDir : b.dirAccessOfRequest n init e_req e_dir
  dirIsLin : e_lin = e_dir

/-- Def. Prop constraints for Def 2.37 case where the request has doesn't have coherent permissions and there exists a corresponding Directory
Event, defined by Lemma 3. -/
structure Behaviour.requestWithoutCoherentPermsLinearizesAtDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_lin : Event n)
  -- (hreq_in_b : e_req ∈ b) (hreq_encap_dir : axRequestAccessesDirectory n) (hdir_before_after : has_perms_or_vd_exists_e_dir_before_or_after n)
  : Prop where
  reqHasNoPerms : b.reqMissingPerms n init e_req -- rule out cases that don't make sense
  -- reqOnNonCoherentOrNoPerms : b.eventOnNonCoherentState n init e_req ∨ b.eventOnStateNoPerms n init e_req
  reqLinearizeAtDir : ∃ e_dir ∈ b, b.requestLinearizesAtDirectory n init e_req e_dir e_lin

/-
/-- Def. Wrapper structure : Prop. for Def 2.37-/
structure Behaviour.requestWithoutCoherentPermLin (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  linearizingRequest : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∃ e_lin : Event n,
    b.requestWithoutCoherentPermsLinearizesAtDir n init e_req e_lin
-/

/-- Def. 2.37. Linearization Event Corresponding to a Request Event. If a Request Event `e_req` is made on a `Coherent` state with sufficient
permissions, the linearization event `e_lin` of `e_req` is `e_req`. Otherwise, `e_lin` is the Directory Event `e_dir` stated by Lemma 3. -/
inductive Behaviour.linearizationEventOfRequest (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
| requestLin : (∃ e_lin ∈ b, b.requestWithCoherentPermsLinearizes n init e_req e_lin) → Behaviour.linearizationEventOfRequest b init e_req
| dirLin : (∃ e_lin ∈ b, b.requestWithoutCoherentPermsLinearizesAtDir n init e_req e_lin) → Behaviour.linearizationEventOfRequest b init e_req

def Behaviour.linearizationEventOfRequestWrapper := ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req : Event n,
  b.linearizationEventOfRequest n init e_req
