import CompositionalProtocolProof.Behaviours

variable (n : Nat)

/-
structure Request.IsValid (r : Request) where
  non_coherent : r.NoSCNonCoherent := by simp
  no_write_acq : r.NoWriteAcquire := by simp
  no_read_rel : r.NoReadRelease := by simp
  no_cacq : r.NoCoherentAcquire := by simp
  no_cwr : r.NoCoherentWeakRead := by simp
-/

noncomputable def Behaviour.reqToDirOfRequestEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : ValidRequest :=
  let state_before := b.stateBefore n e_req init
  match e_req.req.val, state_before.cache with
  | ⟨.w, false, _⟩, I => ⟨⟨.r, false, .Weak⟩, {non_coherent := by simp, no_write_acq := by simp, no_read_rel := by simp, no_cacq := by simp, no_cwr := by simp}⟩
  | ⟨.r, false, .Acq⟩, Vd => ⟨⟨.w, false, .Weak⟩, {non_coherent := by simp, no_write_acq := by simp, no_read_rel := by simp, no_cacq := by simp, no_cwr := by simp}⟩
  | _, _ => e_req.req

/-- Axiom 3. The Request field of a Directory Event corresponding to a Request Event (Cache Event). -/
structure Behaviour.requestDirectoryEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEvent : e_dir.isDirEventOfReqEvent n e_req
  sameAddr : e_req.addr = e_dir.addr
  dirReq :  e_dir.req = b.reqToDirOfRequestEvent n e_req init -- from analysis on e_req and the state it's made on
  dirState : e_dir.isDirEventOfDirState n (b.stateAfter n e_dir init).directory

structure Behaviour.reqEncapsulatesDirEvent' (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapDir : e_req.Encapsulates n e_dir
  dirCorresponds : b.requestDirectoryEvent n e_req e_dir init
  dirInB : e_dir ∈ b.es
  reqInB : e_req ∈ b.es

structure Behaviour.reqEncapCorrespondingDirEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : Prop where
  reqEncapCorrDir : ∃ e_dir ∈ b.es, b.reqEncapsulatesDirEvent' n e_req e_dir init

/--Axiom 4. Acquire invalidates other Vc cache entries after it's directory access. -/
structure Behaviour.acquireInvalidates (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isAcquire : e_req.isAcquire
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n e_req init
  invalOther : ∀ addr ≠ e_req.addr, ∃ e_inval ∈ b.es, e_dir.OrderedBefore n e_inval ∧ e_inval.isVcInval

  isRelease : e_req.isNCRelease
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent e_req init
  writeBackOther : ∀ addr ≠ e_req.addr, ∃ e_wb ∈ b.es, e_wb.OrderedBefore n e_dir ∧ e_wb.isVdWriteBack
