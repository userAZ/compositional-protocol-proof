import CompositionalProtocolProof.Behaviours
import Mathlib

variable (n : Nat)

lemma Behaviour.state_after_eq_succeeding_state_before' {n l} {init : EntryState n} {e_req : Event n}
  : List.stateAfter n (l ++ [e_req]) init =
    Event.SucceedingState n e_req (List.stateAfter n l init) := by
  induction l generalizing init with
  | nil =>
    simp[List.stateAfter]
  | cons head tail ih =>
    rw[List.stateAfter.eq_def]
    rw[List.stateAfter.eq_def]
    simp
    apply ih

lemma Behaviour.state_after_eq_succeeding_state_before (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  : (stateAfter n b (InitialSystemState.stateAt n init e_req) e_req) = e_req.SucceedingState n (stateBefore n b (InitialSystemState.stateAt n init e_req) e_req)
  := by
  apply state_after_eq_succeeding_state_before'

/-- A coherent write downgrade at a cache will have a resulting state of I. -/
lemma Behaviour.stateAfter_fwd_sw_downgrade_eq_i {b init_entry_state}
  {e_gdown : Event n} (hcache : e_gdown.isCacheEvent) (hdown : e_gdown.down) (hsc_write : e_gdown.isSCWrite)
  : (Behaviour.stateAfter n b init_entry_state e_gdown) = Sum.inl I := by
  simp[Behaviour.stateAfter]
  /- Induct on the list, events up to event, unfold List.stateAfter.
  Show that the state after an `e_gdown` (fwded sc write downwgrade) is always I.  -/
  induction eventsUpToEvent n b e_gdown generalizing init_entry_state with
  | nil =>
    simp[List.stateAfter]
    simp[Event.SucceedingState]
    match e_gdown with
    | .cacheEvent ce =>
      simp[Event.down] at hdown
      simp[CacheEvent.SucceedingState, hdown]
      /- Show the result of the global downgrade `e_gdown` is `I`. -/
      simp[ValidRequest.DowngradeState]

      simp[Event.isSCWrite, Event.req, ValidRequest.isSCWrite] at hsc_write
      simp only [hsc_write, ]
      simp only [ValidRequest.MRS, ReadWrite.toPerms, ReadWrite.toRWPerms]
      /- No matter what the previous state is, this fwd SC get SW `e_gdown` invalidates this cache. -/

      match EntryState.cache n init_entry_state with
      | ⟨some .wr, true⟩ | ⟨some .r, true⟩ | ⟨some .wr, false⟩ | ⟨some .r, false⟩ | ⟨none, false⟩ | ⟨none, true⟩ =>
        all_goals simp [LE.le, State.le, LT.lt, Option.le]
    | .directoryEvent _ => simp[Event.isCacheEvent] at hcache
  | cons h tail ih => simp [List.stateAfter, ih]

lemma Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore {b e init_state}
  : (List.stateAfter n (eventsUpToEvent n b e ++ [e]) init_state) = ([e].stateAfter n (stateBefore n b init_state e))
  := by
  simp [stateBefore]
  induction eventsUpToEvent n b e generalizing init_state with
  | nil => simp[List.stateAfter]
  | cons head l_tail ih =>
    rw[List.cons_append]
    nth_rw 3 [List.stateAfter]
    nth_rw 1 [List.stateAfter]
    apply ih

lemma Behaviour.stateAfter_directory_event_is_directory_state {b init_state e_dir_coh_read} {es : List (Event n)} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  (hall_dir : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e_dir_coh_read) (Event.addr n e_dir_coh_read))
  : (List.stateAfter n es init_state).isDirectoryState := by
  simp[EntryState.isDirectoryState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isDirectoryState.eq_def]
    exact hinit_dir
  | cons head tail ih =>
    apply ih
    . case cons.hinit_dir =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_dir head (by simp) |>.eAtStruct
      match head with
      | .directoryEvent de => simp[EntryState.isDirectoryState]
      | .cacheEvent _ =>
        match e_dir_coh_read with
        | .directoryEvent _ => simp [Event.struct] at hhead_of_dir
        | .cacheEvent _ => simp[Event.isDirectoryEvent] at hdir_is_dir
    . case cons.hall_dir =>
      intro e' he'_in_tail
      apply hall_dir
      . case a => simp[he'_in_tail]

lemma Behaviour.stateBefore_dir_event_is_dir_state {b init_state e_dir_coh_read} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  : (stateBefore n b init_state e_dir_coh_read).isDirectoryState := by
  simp[stateBefore]
  have hall_dir := Behaviour.eventsUpToEntry_at_e_entry n b e_dir_coh_read
  apply Behaviour.stateAfter_directory_event_is_directory_state
  . case hdir_is_dir => exact hdir_is_dir
  . case hinit_dir => exact hinit_dir
  . case hall_dir => exact hall_dir

/-- The initial state of a CacheEvent will be a CacheState. -/
lemma InitialSystemState.stateAt_event_isCacheEvent_EntryState_is_cache_state
  {e : Event n} (he_cache : e.isCacheEvent)
  : (InitialSystemState.stateAt n init e).isCacheState := by
  simp[InitialSystemState.stateAt]
  match e with
  | .cacheEvent ce => simp[EntryState.isCacheState]
  | .directoryEvent _ => simp[Event.isCacheEvent] at he_cache

lemma Behaviour.stateAfter_cache_event_is_cache_state {b init_state e} {es : List (Event n)} (he_is_cache : e.isCacheEvent) (hinit_cache : init_state.isCacheState)
  (hall_at_entry : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e) (Event.addr n e))
  : (List.stateAfter n es init_state).isCacheState := by
  simp[EntryState.isCacheState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isCacheState.eq_def]
    exact hinit_cache
  | cons head tail ih =>
    apply ih
    . case cons.hinit_cache =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_at_entry head (by simp) |>.eAtStruct
      match head with
      | .cacheEvent _ => simp[EntryState.isCacheState]
      | .directoryEvent _ =>
        match e with
        | .directoryEvent _ => simp[Event.isCacheEvent] at he_is_cache
        | .cacheEvent _ => simp [Event.struct] at hhead_of_dir
    . case cons.hall_at_entry =>
      intro e' he'_in_tail
      apply hall_at_entry
      . case a => simp[he'_in_tail]

lemma Behaviour.stateBefore_cache_event_is_cache_state {b init_state e} (he_is_cache : e.isCacheEvent) (hinit_cache : init_state.isCacheState)
  : (stateBefore n b init_state e).isCacheState := by
  simp[stateBefore]
  have hall_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e
  apply Behaviour.stateAfter_cache_event_is_cache_state
  . case he_is_cache => exact he_is_cache
  . case hinit_cache => exact hinit_cache
  . case hall_at_entry => exact hall_at_entry

lemma Behaviour.stateAfter_eventsUpToEvent_append_eq_stateAfter_stateBefore' {b e es init_state}
  : (List.stateAfter n (eventsUpToEvent n b e ++ es) init_state) = (es.stateAfter n (stateBefore n b init_state e))
  := by
  simp [stateBefore]
  induction eventsUpToEvent n b e generalizing init_state with
  | nil => simp[List.stateAfter]
  | cons head l_tail ih =>
    rw[List.cons_append]
    nth_rw 2 [List.stateAfter]
    nth_rw 1 [List.stateAfter]
    apply ih

/-- Helper Lemma: If an Event `e_pred` Finishes Before `e_gdown`,
and it's ordered after `e_cdir` that's encapsulated by `e_gdown`,
then `e_gdown.Encapsulates e_pred`-/
lemma Behaviour.gdown_encap_finish_before_cdir
  (hdpred : e_pred = Event.directoryEvent de_pred)
  (hdcdir : e_cdir = Event.directoryEvent de_cdir)
  (hpred_finish_before_gdown : Event.finishesBefore n e_pred e_gdown)
  (hcdir_ob_pred : DirectoryEvent.OrderedBefore n de_cdir de_pred)
  (hgdown_encap_cdir : e_gdown.Encapsulates n e_cdir)
  : e_gdown.Encapsulates n e_pred := by
  simp[DirectoryEvent.OrderedBefore] at hcdir_ob_pred
  simp[Event.Encapsulates]
  apply And.intro
  . case left =>
    calc e_gdown.oStart < e_cdir.oStart := hgdown_encap_cdir.left
      _ < e_cdir.oEnd := e_cdir.oWellFormed
      _ < e_pred.oStart := by simp[hdcdir,hdpred,Event.oEnd,Event.oStart,hcdir_ob_pred]
  . case right =>
    simp[Event.finishesBefore] at hpred_finish_before_gdown
    exact hpred_finish_before_gdown

lemma Behaviour.directory_acq_from_sw_state_eq_stateAfter_vd_append_rest
  {es : List (Event n)} {e_dir_shim_acq : Event n}
  (hacq_is_dir : e_dir_shim_acq.isDirectoryEvent)
  (hacq_not_down : ¬ e_dir_shim_acq.down)
  (hacq_is_acq_or_weak_write : e_dir_shim_acq.req.isAcquire ∨ e_dir_shim_acq.req.isNcWeakWrite)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  :
  List.stateAfter n ([e_dir_shim_acq] ++ es) (Sum.inr (DirectoryState.SW ⟨SW, by simp⟩ owner)) = List.stateAfter n es (Sum.inr (DirectoryState.Vd ⟨Vd, by simp⟩))
  -- (List.stateAfter n ([e_dir_shim_vd_down] ++ [e_dir_shim_vc_down]) (Sum.inr (DirectoryState.Vd a✝)))
  := by
  rw[List.stateAfter.eq_def]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_acq with
  | .directoryEvent de_shim_acq =>
    simp [DirectoryEvent.SucceedingState]
    simp[Event.down] at hacq_not_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hacq_not_down]

    simp[Event.req, ValidRequest.isAcquire, ValidRequest.isNcWeakWrite] at hacq_is_acq_or_weak_write
    cases hacq_is_acq_or_weak_write
    . case inl hacq_is_acq =>
      -- After NC read on SW fix: Acquire on SW → Vc, not Vd.
      -- This lemma needs splitting: Acquire → Vc, NC weak write → Vd.
      -- TODO: refactor this lemma and its call sites in Lemma 6.
      simp[hacq_is_acq]
      sorry -- Acquire on SW now produces Vc, not Vd
    . case inr hacq_is_nc_weak_write =>
      -- resolve to case where we apply a Vd downgrade at the directory
      simp[hacq_is_nc_weak_write]
  | .cacheEvent _ =>
    simp[Event.isDirectoryEvent] at hacq_is_dir

/- Something like this is probably the best way to break down the 3 lemmas -/
lemma Behaviour.directory_vd_downgrade_from_vd_state_eq_stateAfter_vc_append_rest
  {es : List (Event n)} {e_dir_shim_vd_down : Event n}
  (hvd_is_dir : e_dir_shim_vd_down.isDirectoryEvent)
  (hvd_is_down : e_dir_shim_vd_down.down)
  (hvd_is_nc_weak_write : e_dir_shim_vd_down.req.isNcWeakWrite)
  -- (hfwd_sw_down_translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down)
  :
  List.stateAfter n ([e_dir_shim_vd_down] ++ es) (Sum.inr (DirectoryState.Vd ⟨Vd, by simp⟩)) = List.stateAfter n es (Sum.inr (DirectoryState.Vc ⟨Vc, by simp⟩))
  -- (List.stateAfter n ([e_dir_shim_vd_down] ++ [e_dir_shim_vc_down]) (Sum.inr (DirectoryState.Vd a✝)))
  := by
  rw[List.stateAfter.eq_def]
  simp[Event.SucceedingState]
  -- e_dir_shim_vd_down is a directory event
  match e_dir_shim_vd_down with
  | .directoryEvent de_shim_vd_down =>
    simp [DirectoryEvent.SucceedingState]
    simp[Event.down] at hvd_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hvd_is_down]

    simp[Event.req, ValidRequest.isNcWeakWrite] at hvd_is_nc_weak_write
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hvd_is_nc_weak_write]
    simp[EntryState.directory]
  | .cacheEvent _ =>
    simp[Event.isDirectoryEvent] at hvd_is_dir

lemma Behaviour.directory_vc_downgrade_from_vc_state_eq_stateAfter_i_append_rest
  {es : List (Event n)} {e_dir_shim_vc_down : Event n}
  (hvc_is_dir : e_dir_shim_vc_down.isDirectoryEvent)
  (hvc_is_down : e_dir_shim_vc_down.down)
  (hvc_is_nc_weak_read : e_dir_shim_vc_down.req.isNcWeakRead)
  :
  List.stateAfter n ([e_dir_shim_vc_down] ++ es) (Sum.inr (DirectoryState.Vc ⟨Vc, by simp⟩)) = List.stateAfter n es (Sum.inr (DirectoryState.I ⟨I, by simp⟩))
  := by
  -- Now resolve Shim Vc downgrade
  simp[List.stateAfter]
  simp[Event.SucceedingState]
  match e_dir_shim_vc_down with
  | .directoryEvent de_shim_vc_down =>
    simp[DirectoryEvent.SucceedingState]
    have hshim_vc_down_is_down := hvc_is_down
    simp[Event.down] at hshim_vc_down_is_down
    -- resolve to the case that `e_vd_down` is indeed a downgrade
    simp[hshim_vc_down_is_down]

    have hshim_vc_down_is_vc_req := hvc_is_nc_weak_read
    simp[Event.req, ValidRequest.isNcWeakRead] at hshim_vc_down_is_vc_req
    -- resolve to case where we apply a Vd downgrade at the directory
    simp[hshim_vc_down_is_vc_req]
    simp[EntryState.directory]
  | .cacheEvent _ =>
    simp[Event.isDirectoryEvent] at hvc_is_dir

lemma Behaviour.stateAfter_directory_event_is_directory_state' {b init_state e_dir_coh_read} {es : List (Event n)} (hdir_is_dir : e_dir_coh_read.isDirectoryEvent) (hinit_dir : init_state.isDirectoryState)
  (hall_dir : ∀ e' ∈ es, eventAtEntry n b e' (Event.struct n e_dir_coh_read) (Event.addr n e_dir_coh_read))
  : (List.stateAfter n es init_state).isDirectoryState := by
  simp[EntryState.isDirectoryState]
  induction es generalizing init_state with
  | nil =>
    simp[List.stateAfter]
    simp[← EntryState.isDirectoryState.eq_def]
    exact hinit_dir
  | cons head tail ih =>
    apply ih
    . case cons.hinit_dir =>
      simp[Event.SucceedingState]
      have hhead_of_dir := hall_dir head (by simp) |>.eAtStruct
      match head with
      | .directoryEvent de => simp[EntryState.isDirectoryState]
      | .cacheEvent _ =>
        match e_dir_coh_read with
        | .directoryEvent _ => simp [Event.struct] at hhead_of_dir
        | .cacheEvent _ => simp[Event.isDirectoryEvent] at hdir_is_dir
    . case cons.hall_dir =>
      intro e' he'_in_tail
      apply hall_dir
      . case a => simp[he'_in_tail]

lemma Behaviour.unwrap_cache_state_to_entry_state
  (he_is_cache : e_evict.isCacheEvent)
  (hevict_init_is_cache_state : (InitialSystemState.stateAt n init e_evict).isCacheState)
  : (EntryState.cache n
      (List.stateAfter n (Behaviour.eventsUpToEvent n b e_evict) (InitialSystemState.stateAt n init e_evict)) =
       Event.MRS n e_evict) →
    (List.stateAfter n (Behaviour.eventsUpToEvent n b e_evict) (InitialSystemState.stateAt n init e_evict)) =
      Sum.inl (Event.MRS n e_evict)
  := by
  intro hstate_before_e_eq_mrs_e
  rw[← hstate_before_e_eq_mrs_e]
  -- TODO: show applying EntryState.cache and then Sum.inl gives you the original cache EntryState back.
  -- Need hypothesis that the resulting state from stateAfter is a cache state.
  have hall_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e_evict
  have hstate_after_is_cache_state := Behaviour.stateAfter_cache_event_is_cache_state n he_is_cache hevict_init_is_cache_state hall_at_entry

  cases hstate_after : List.stateAfter n (eventsUpToEvent n b e_evict) (InitialSystemState.stateAt n init e_evict)
  . case inl state => simp[EntryState.cache]
  . case inr dir_state =>
    simp[EntryState.isCacheState] at hstate_after_is_cache_state
    simp[hstate_after] at hstate_after_is_cache_state

lemma Behaviour.unwrap_stateBefore_cache_state_to_entry_state' {b init e_pred}
  (he_is_cache : e_pred.isCacheEvent)
  (hpred_init_is_cache_state : (InitialSystemState.stateAt n init e_pred).isCacheState)
  : (EntryState.cache n
    (Behaviour.stateBefore n b (InitialSystemState.stateAt n init e_pred)
      e_pred)) = state
      →
      (Behaviour.stateBefore n b (InitialSystemState.stateAt n init e_pred)
        e_pred) = Sum.inl state
  := by
  -- apply Behaviour.unwrap_cache_state_to_entry_state n he_is_cache hevict_init_is_cache_state
  intro hcache_state_before_eq_state
  rw[← hcache_state_before_eq_state]

  have hall_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e_pred
  have hstate_before_is_cache_state := b.stateBefore_cache_event_is_cache_state n he_is_cache hpred_init_is_cache_state

  cases hstate_after : (stateBefore n b (InitialSystemState.stateAt n init e_pred) e_pred)
  . case inl state =>
    simp[EntryState.cache]
  . case inr dir_state =>
    simp[EntryState.isCacheState] at hstate_before_is_cache_state
    simp[hstate_after] at hstate_before_is_cache_state
