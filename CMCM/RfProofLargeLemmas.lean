import CMCM.RfProofDefs

variable {n : ℕ}

/-- Helper: I state is not MR state. -/
lemma i_state_ne_mr : (I : State) ≠ MR := by
  simp only [I, MR]
  norm_num

/-- Helper: If events list equals eventsUpToEvent n e and splits as front ++ [last],
    then front equals eventsUpToEvent n last. -/
lemma eventsUpToEvent_split
  {b : Behaviour n} {e : Event n}
  {front : List (Event n)} {last : Event n}
  (h_split : b.eventsUpToEvent n e = front ++ [last])
  : front = b.eventsUpToEvent n last := by
  -- Unfold definitions
  simp only [Behaviour.eventsUpToEvent] at h_split ⊢
  simp only [List.upToEvent] at h_split ⊢

  -- h_split: List.take (List.idxOf e (eventsAtEventEntry n b e)) (eventsAtEventEntry n b e) = front ++ [last]
  -- Goal: List.take (List.idxOf last (eventsAtEventEntry n b last)) (eventsAtEventEntry n b last) = front

  --last must be in eventsUpToEvent, so it's at the same entry as e
  have h_last_at_same_entry : b.eventAtEntry n last e.struct e.addr := by
    apply Behaviour.eventsUpToEntry_at_e_entry
    simp only [Behaviour.eventsUpToEvent, List.upToEvent]
    rw [h_split]
    exact List.mem_append_right front (List.mem_singleton_self last)

  -- Events at same entry are equal
  have h_same_events : b.eventsAtEventEntry n last = b.eventsAtEventEntry n e := by
    apply Behaviour.eventsAtEventEntry_eq_same_entry
    constructor
    · simp only [Event.sameStructure]
      exact h_last_at_same_entry.eAtStruct
    · simp only [Event.sameAddr]
      exact h_last_at_same_entry.eAtAddr

  -- Substitute: events at last = events at e
  rw [h_same_events]

  -- Get nodup for front ++ [last]
  have h_nodup : (front ++ [last]).Nodup := by
    have := b.eventsUpToEvent_no_dups n e
    simp only [Behaviour.eventsUpToEvent, List.upToEvent] at this
    rw [h_split] at this
    exact this

  -- last ∉ front (from nodup)
  have hlast_not_in_front : last ∉ front := by
    simp [List.nodup_append'] at h_nodup
    exact h_nodup.right

  -- Since take (idxOf e list) list = front ++ [last], and list starts with at least that much,
  -- we can reconstruct: list = front ++ [last] ++ (drop (idxOf e list) list)
  have h_list_decomp : b.eventsAtEventEntry n e =
      List.take (List.idxOf e (b.eventsAtEventEntry n e)) (b.eventsAtEventEntry n e) ++
      List.drop (List.idxOf e (b.eventsAtEventEntry n e)) (b.eventsAtEventEntry n e) := by
    exact (List.take_append_drop _ _).symm

  rw [h_split] at h_list_decomp

  -- Now idxOf last in (front ++ [last] ++ rest) = idxOf last (front ++ [last])
  have h_idx_last : List.idxOf last (b.eventsAtEventEntry n e) = List.idxOf last (front ++ [last]) := by
    rw [h_list_decomp]
    apply List.idxOf_append_of_mem
    simp

  -- And idxOf last (front ++ [last]) = front.length
  have h_idx_in_prefix : List.idxOf last (front ++ [last]) = front.length := by
    rw [List.idxOf_append_of_notMem hlast_not_in_front]
    simp

  -- Therefore take (idxOf last list) list = take front.length list = front
  rw [h_idx_last, h_idx_in_prefix]
  -- Goal: front = take front.length (eventsAtEventEntry)
  -- Substitute list decomposition
  rw [h_list_decomp]
  -- Now: front = take front.length (front ++ [last] ++ rest)
  simp

/-- Key lemma: If an event list produces MR state from I, then some event must be coherent.
    Uses backward induction with reverseRecOn to process last event first.
-/
lemma event_list_to_mr_requires_coherent
  {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
  (he_is_cache : e.isCacheEvent)
  (hlist : List (Event n))
  (h_list_eq : hlist = b.eventsUpToEvent n e)
  (h_state_after : List.stateAfter n hlist (init.stateAt n e) = MREntry n)
  : ∃ e_coh ∈ hlist, e_coh.req.val.coherent = true := by
  -- Use reverse recursion to work backwards through the event list
  -- This gives us front ++ [last] structure, where we can apply the lemma recursively
  revert e he_is_cache h_list_eq h_state_after

  induction hlist using List.reverseRecOn with
  | nil =>
    -- Base case: empty list
    intros e he_is_cache h_eq h_state
    simp only [List.stateAfter] at h_state
    -- h_state: init.stateAt n e = MREntry n
    -- This contradicts that initial state is I for cache events
    exfalso
    cases e with
    | cacheEvent ce =>
      simp only [InitialSystemState.stateAt, MREntry] at h_state
      simp only [Sum.inl.injEq] at h_state
      -- h_state: init.cacheStates ce.cid = MR
      have h_ce_is_cache : Event.isCacheEvent n (.cacheEvent ce) := rfl
      have h_init_is_i : InitialSystemState.stateAt n init (.cacheEvent ce) = IEntry n :=
        b.initCacheStateIsI (.cacheEvent ce) init h_ce_is_cache
      simp only [InitialSystemState.stateAt, IEntry] at h_init_is_i
      simp only [Sum.inl.injEq] at h_init_is_i
      -- h_init_is_i: init.cacheStates ce.cid = I
      have : (I : State) ≠ MR := i_state_ne_mr
      exact this (Eq.trans h_init_is_i.symm h_state)
    | directoryEvent de =>
      simp only [InitialSystemState.stateAt, MREntry] at h_state
      -- Sum.inr ≠ Sum.inl
      cases h_state
  | append_singleton front last ih =>
    -- Recursive case: list is front ++ [last]
    intros e he_is_cache h_eq h_state

    -- We know: front ++ [last] = b.eventsUpToEvent n e
    -- By helper lemma: front = b.eventsUpToEvent n last
    have h_front_eq : front = b.eventsUpToEvent n last := by
      exact eventsUpToEvent_split h_eq.symm

    -- Compute state after applying all events
    rw [Behaviour.state_after_eq_succeeding_state_before'] at h_state

    -- h_state: Event.SucceedingState n last (front.stateAfter n (init.stateAt n e)) = MREntry n

    -- Check if last is coherent
    by_cases h_last_coh : last.req.val.coherent = true
    · -- Case: last is coherent
      -- last is coherent, we're done
      use last
      constructor
      · exact List.mem_append_right front (List.mem_singleton_self last)
      · exact h_last_coh
    · -- Case: last is not coherent
      -- Define sB_last (state before last = state after front)
      let sB_last := front.stateAfter n (init.stateAt n e)
      
      -- h_state: SucceedingState(last, sB_last) = MREntry n
      
      -- Case analysis on the cache state before last
      match sB_cache : sB_last.cache with
      | ⟨some .r, true⟩ =>
        -- Case B: sB_last.cache = MR = ⟨some .r, true⟩
        -- Apply IH: if front produces MR, it contains a coherent event
        
        -- The match gives us: sB_cache : sB_last.cache = ⟨some .r, true⟩ = MR
        -- sB_last = front.stateAfter n (init.stateAt n e) and sB_last.cache = MR
        -- Therefore, (front ++ [last]).stateAfter with initial state produces MR means front produces MR
        
        -- For IH, we need to show front.stateAfter n (init.stateAt n last) = MREntry n
        -- But sB_last = front.stateAfter n (init.stateAt n e)
        -- We have sB_last.cache = MR, which means sB_last = MREntry n (as shown below)
        
        have h_sB_last_is_MR : sB_last = MREntry n := by
          cases h : sB_last with
          | inl s =>
            -- sB_last = Sum.inl s
            -- sB_cache : sB_last.cache = MR
            -- Since EntryState.cache (Sum.inl s) = s, we have s = MR
            have h_s_eq_mr : s = MR := by
              have hsb_cache_eval := sB_cache
              rw [h] at hsb_cache_eval
              simp [EntryState.cache] at hsb_cache_eval
              exact hsb_cache_eval
            -- Show Sum.inl s = MREntry n = Sum.inl MR
            unfold MREntry
            rw [h_s_eq_mr]
          | inr ds =>
            -- This case is impossible: sB_last must be a cache state
            exfalso
            -- last is in eventsUpToEvent n e, so it's at the same entry as e
            have h_last_at_same_entry : b.eventAtEntry n last e.struct e.addr := by
              have h_last_in : last ∈ b.eventsUpToEvent n e := by
                rw [← h_eq]
                exact List.mem_append_right front (List.mem_singleton_self last)
              exact Behaviour.eventsUpToEntry_at_e_entry n b e last h_last_in
            
            -- Since e is a cache event (by hypothesis), last is also a cache event
            have h_last_is_cache : last.isCacheEvent := by
              cases e with
              | cacheEvent ce =>
                cases last with
                | cacheEvent ce_last => rfl
                | directoryEvent de_last =>
                  -- Can't have directory event at cache entry
                  -- h_last_at_same_entry says last.struct = e.struct and last.addr = e.addr
                  -- But last is directory and e is cache, so structs can't match
                  exfalso
                  have h_struct_eq := h_last_at_same_entry.eAtStruct
                  simp [Event.struct] at h_struct_eq
              | directoryEvent de =>
                -- e is a cache event by hypothesis he_is_cache
                simp [Event.isCacheEvent] at he_is_cache
            
            -- Initial state at last is a cache state
            have h_init_last_is_cache : (init.stateAt n last).isCacheState := by
              cases last with
              | cacheEvent ce => simp [InitialSystemState.stateAt, EntryState.isCacheState]
              | directoryEvent de => simp [Event.isCacheEvent] at h_last_is_cache
            
            -- The state before last (which equals sB_last) must also be a cache state
            -- by stateAfter_cache_event_is_cache_state
            -- But sB_last = Sum.inr ds is a directory state, contradiction
            have h_sB_last_is_cache : sB_last.isCacheState := by
              -- sB_last = front.stateAfter n (init.stateAt n e)
              -- All events in front are at same entry as e (cache entry)
              have hall_at_entry : ∀ e' ∈ front, b.eventAtEntry n e' e.struct e.addr := by
                intro e' he'_in_front
                have he'_in_list : e' ∈ front ++ [last] := List.mem_append_left [last] he'_in_front
                rw [h_eq] at he'_in_list
                exact Behaviour.eventsUpToEntry_at_e_entry n b e e' he'_in_list
              -- Initial state is cache state
              have h_init_cache : (init.stateAt n e).isCacheState := by
                cases e with
                | cacheEvent ce => simp [InitialSystemState.stateAt, EntryState.isCacheState]
                | directoryEvent de => simp [Event.isCacheEvent] at he_is_cache
              -- Apply stateAfter_cache_event_is_cache_state
              exact Behaviour.stateAfter_cache_event_is_cache_state n he_is_cache h_init_cache hall_at_entry
            -- But we have sB_last = Sum.inr ds, which contradicts h_sB_last_is_cache
            rw [h] at h_sB_last_is_cache
            simp [EntryState.isCacheState] at h_sB_last_is_cache
        
        -- Now we use IH with event = last
        -- Need: front = b.eventsUpToEvent n last (we have this as h_front_eq)
        -- Need: front.stateAfter n (init.stateAt n last) = MREntry n
        -- We have: sB_last = front.stateAfter n (init.stateAt n e) = MREntry n
        
        have h_front_produces_mr : front.stateAfter n (init.stateAt n last) = MREntry n := by
          -- Show init.stateAt n last = init.stateAt n e
          have h_same_entry : last.sameEntry n e := by
            have h_last_in : last ∈ b.eventsUpToEvent n e := by
              rw [← h_eq]
              exact List.mem_append_right front (List.mem_singleton_self last)
            have h_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e last h_last_in
            -- h_at_entry : b.eventAtEntry n last e.struct e.addr
            -- Need to construct Event.sameEntry n last e
            exact ⟨h_at_entry.eAtStruct, h_at_entry.eAtAddr⟩
          
          have h_init_eq : init.stateAt n last = init.stateAt n e :=
            Event.init_state_at_entry_is_same n init last e h_same_entry
          
          -- Now substitute and use h_sB_last_is_MR
          rw [h_init_eq]
          exact h_sB_last_is_MR
        
        -- Apply the inductive hypothesis
        -- Need to show last.isCacheEvent (proven above)
        have h_last_is_cache : last.isCacheEvent := by
          have h_last_in : last ∈ b.eventsUpToEvent n e := by
            rw [← h_eq]
            exact List.mem_append_right front (List.mem_singleton_self last)
          have h_at_entry := Behaviour.eventsUpToEntry_at_e_entry n b e last h_last_in
          cases e with
          | cacheEvent ce =>
            cases last with
            | cacheEvent ce_last => rfl
            | directoryEvent de_last =>
              exfalso
              have h_struct_eq := h_at_entry.eAtStruct
              simp [Event.struct] at h_struct_eq
          | directoryEvent de => simp [Event.isCacheEvent] at he_is_cache
        
        obtain ⟨e_coh, he_coh_mem, he_coh_coh⟩ := ih h_last_is_cache h_front_eq h_front_produces_mr
        
        -- Return the coherent event from front (which is in front ++ [last])
        use e_coh
        exact ⟨List.mem_append_left [last] he_coh_mem, he_coh_coh⟩
      
      | ⟨some .wr, true⟩ =>
        -- Case A: sB_last.cache = SW = ⟨some .wr, true⟩
        -- Non-coherent events can't produce MR from SW
        exfalso
        -- Proof: last is non-coherent, sB_last.cache = SW, but SucceedingState = MREntry
        -- For a non-coherent event from SW to produce MR:
        -- - Requires changing permission from .wr to .r and keeping coherent = true
        -- - But non-coherent events don't upgrade cache states to produce read permissions with coherency
        -- TODO: Complete using protocol transition constraints
        sorry
      
      | ⟨some .r, false⟩ =>
        -- Case C: sB_last.cache = Vc = ⟨some .r, false⟩
        -- Non-coherent events can't produce MR from Vc
        exfalso
        -- Proof: last is non-coherent, sB_last.cache = Vc, but SucceedingState = MREntry
        -- For a non-coherent event from Vc to produce MR:
        -- - Requires changing coherent flag from false to true while keeping .r permission
        -- - But non-coherent events (coherent = false) don't produce coherent cache states
        -- - By protocol constraints: non-coherent requests don't upgrade coherency
        -- TODO: Complete using protocol coherency constraints (e.g., non-coherent can't produce coherent state)
        sorry
      
      | ⟨some .wr, false⟩ =>
        -- Case C: sB_last.cache = Vd = ⟨some .wr, false⟩
        -- Non-coherent events can't produce MR from Vd
        exfalso
        -- Proof: last is non-coherent, sB_last.cache = Vd, but SucceedingState = MREntry
        -- For a non-coherent event from Vd to produce MR:
        -- - Requires changing from .wr to .r permission and setting coherent = true
        -- - But non-coherent events don't produce coherent states with read permissions
        -- - By protocol constraints: Vd → MR requires coherent transition
        -- TODO: Complete using protocol transition constraints
        sorry
      
      | ⟨none, _⟩ =>
        -- Case C: sB_last.cache = I or ⟨none, true⟩
        -- Non-coherent events can't produce MR from I
        exfalso
        -- Proof: last is non-coherent, sB_last.cache has no permissions, but SucceedingState = MREntry
        -- For a non-coherent event from I (⟨none, false⟩) to produce MR:
        -- - Requires acquiring read permissions and coherency: none → some .r with coherent = true
        -- - But non-coherent events don't produce coherent states
        -- - By protocol constraints: I → MR requires coherent acquisition
        -- TODO: Complete using protocol acquisition constraints (non-coherent can't acquire to MR)
        sorry
/-- Helper: NC weak write cannot be produced given MR state before it. -/
lemma mr_state_implies_sc_read_exists
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
  (he_is_cache : e.isCacheEvent)
  (hstate_before : b.stateBefore n (init.stateAt n e) e = MREntry n)
  (hncweakwrite : e.req.val = ⟨.w, false, .Weak⟩)
  : False := by
  -- Unfold stateBefore to get the events up to e
  unfold Behaviour.stateBefore at hstate_before

  -- hstate_before: List.stateAfter n (b.eventsUpToEvent n e) (init.stateAt n e) = Sum.inl MR
  -- This means the entry state is the left case (cache state), and it's MR (some .r, true)

  -- Case on whether events list is empty
  cases heq : (b.eventsUpToEvent n e) with
  | nil =>
    -- The list of events before e is empty
    rw [heq] at hstate_before
    simp only [List.stateAfter] at hstate_before
    -- So hstate_before: init.stateAt n e = Sum.inl MR

    -- This means the initial state itself is Sum.inl MR
    -- But the initial cache state is I = (none, false), not MR = (some .r, true)
    cases e with
    | cacheEvent ce =>
      -- For cache events: init.stateAt = Sum.inl (init.cacheStates ce.cid)
      simp only [InitialSystemState.stateAt] at hstate_before
      simp only [Sum.inl.injEq] at hstate_before
      -- Now hstate_before: init.cacheStates ce.cid = MR

      -- By b.initCacheStateIsI, for a cache event ce, init.stateAt n (.cacheEvent ce) = IEntry n
      have h_ce_is_cache : Event.isCacheEvent n (.cacheEvent ce) := rfl
      have hce_initial : InitialSystemState.stateAt n init (.cacheEvent ce) = IEntry n :=
        b.initCacheStateIsI (.cacheEvent ce) init h_ce_is_cache

      -- Simplify: init.stateAt n (.cacheEvent ce) = Sum.inl I
      simp only [InitialSystemState.stateAt, IEntry] at hce_initial
      simp only [Sum.inl.injEq] at hce_initial
      -- hce_initial: init.cacheStates ce.cid = I

      -- But we have hstate_before: init.cacheStates ce.cid = MR
      -- And I ≠ MR
      have h_i_ne_mr : (I : State) ≠ MR := i_state_ne_mr
      exact h_i_ne_mr (Eq.trans hce_initial.symm hstate_before)
    | directoryEvent de =>
      -- For directory events, init.stateAt should be Sum.inr
      simp only [InitialSystemState.stateAt] at hstate_before
      -- hstate_before: Sum.inr (init.directoryStates de.pInst) = Sum.inl MR
      simp only [MREntry] at hstate_before
      -- hstate_before: Sum.inr (init.directoryStates de.pInst) = Sum.inl MR
      -- This is a contradiction: left and right Sum constructors don't unify
      cases hstate_before
  | cons head tail =>
    -- Non-empty event list - multiple events before e
    -- Key insight: All events before e have been applied to reach MREntry n
    --
    -- Strategy (strong induction on event sequence):
    -- 1. To reach state with coherence=true from coherence=false (I state),
    --    at least one event must have coherence=true in its request
    -- 2. Only SC (coherent) reads set coherence to true
    -- 3. So some event e_sc in (head :: tail) is an SC read
    -- 4. Event e is a NC weak write, so by protocol separation (nc_no_sc):
    --    if NC weak write in protocol, then SC read not in protocol
    -- 5. But e_sc is in behavior b, which follows the protocol
    -- 6. So both NC write and SC read are in the protocol, contradiction

    -- Extract the key facts needed
    have hncw_noncoherent : e.req.NonCoherent := by
      simp only [ValidRequest.NonCoherent, Request.nonCoherent]
      rw [hncweakwrite]
      decide

    -- Now use the event sequence structure
    rw [heq] at hstate_before
    simp only [List.stateAfter] at hstate_before

    -- Apply the helper lemma to find a coherent event in the sequence
    have h_exists_coherent : ∃ e_coh ∈ (head :: tail), e_coh.req.val.coherent = true := by
      exact event_list_to_mr_requires_coherent he_is_cache (head :: tail) heq.symm hstate_before

    obtain ⟨e_coh, he_coh_in_list, he_coh_is_coherent⟩ := h_exists_coherent

    -- Now derive the contradiction using protocol constraints
    have : False := by
      -- e_coh is in b.eventsUpToEvent n e (from he_coh_in_list), so it's in behavior b
      -- Therefore e_coh.req follows the protocol
      --
      -- e is NC weak write, so e.req is noncoherent
      have hncw_noncoherent : e.req.NonCoherent := by
        simp only [ValidRequest.NonCoherent, Request.nonCoherent]
        simp only [hncweakwrite]
        simp

      -- e_coh is coherent (he_coh_is_coherent), so it can produce MR state
      -- By nc_no_sc: if NC request is in protocol, coherent requests are not
      -- Both e and e_coh are in the behavior which follows the protocol
      -- So both requests are in the protocol, contradicting nc_no_sc

      -- The formal completion requires:
      -- 1. That events in b.eventsUpToEvent n e are in behavior b
      -- 2. That b follows the compound protocol
      -- 3. Application of nc_no_sc to both e.req and e_coh.req
      
      -- The contradiction should follow from:
      -- - We found e_coh with coherent=true in the event list before e
      -- - e is NC weak write (state before e = MR)
      -- - By protocol constraint nc_no_sc: if NC is in protocol, coherent (SC) is not
      -- - But both are in the behavior, which follows the protocol
      -- This creates a protocol violation
      
      sorry  -- TODO: Complete using nc_no_sc protocol constraint

    exact this

/-- Helper lemma: NC weak write cannot be made on MR (maximum read) state.
MR state ⟨some .r, true⟩ can only be produced by coherent SC reads,
but SC reads and NC weak writes cannot coexist in the same protocol. -/
lemma nc_weak_write_not_on_mr_state
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_ww : Event n}
    (he_ww_is_cache : e_ww.isCacheEvent)
  (_he_ww_in_b : e_ww ∈ b)
  (hncweakwrite : e_ww.req.val = ⟨.w, false, .Weak⟩)
  (hmr_state : b.stateBefore n (init.stateAt n e_ww) e_ww = MREntry n)
  : False := by
  exact mr_state_implies_sc_read_exists (cmp := cmp) he_ww_is_cache hmr_state hncweakwrite

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
{cmp : CompoundProtocol n}
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
(he_ce_in_b : Event.cacheEvent ce ∈ b)
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
              -- State before ce is MR (⟨some .r, true⟩)
              -- If ce is NC weak write, this contradicts protocol constraints
              simp[hweak] at he_req
              exfalso
              have hunwrap_req' := hunwrap_req hstate_before_req
              have hval_eq : (Event.cacheEvent ce).req.val = ⟨.w, false, .Weak⟩ := by simp [Event.req, he_req]
              exact nc_weak_write_not_on_mr_state (cmp := cmp) (b := b) (init := init)
                (e_ww := Event.cacheEvent ce) rfl he_ce_in_b hval_eq hunwrap_req'
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
  {cmp : CompoundProtocol n}
  {b : Behaviour n} {init : InitialSystemState n} {e_pred e_req : Event n}
  (hwrite : e_req.isWrite)
  (hreq_has_perms : b.hasPerms n init e_req)
  (hreq_on_coherent_state : b.reqMadeOnCoherentState n init e_req)
  (hpred_produces : b.reqLeavesStateAtLeast n e_pred init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ e_pred.down)
  (hpred_missing_perms : Behaviour.reqMissingPerms n b init e_pred)
  (hpred_cache : e_pred.isCacheEvent)
  (he_req_in_b : e_req ∈ b)
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
              . case cmp => exact cmp
              . case hreq_on_coherent_state => exact hreq_on_coherent_state
              . case hpred_not_down => exact hpred_not_down
              . case hreq_has_perms => exact hreq_has_perms
              . case hpred_produces => exact hpred_produces
              . case he_req_mrs_le_pred_state_after => exact he_req_mrs_le_pred_state_after
              . case he_req => exact he_req
              . case hreq_weak_or_rel => simp[]
              . case hno_perms => exact hno_perms
              . case hpred_req => exact hpred_req
              . case he_ce_in_b => exact he_req_in_b
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
