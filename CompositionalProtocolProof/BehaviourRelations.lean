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

def Event.reqToDirOfRequestEvent (e_req : Event n) (state_before : State) : ValidRequest :=
  match e_req.req, state_before, e_req.down with
  | ⟨⟨.w, false, _⟩, _⟩, I, false => ⟨⟨.r, false, .Weak⟩, {}⟩
  | ⟨⟨.r, false, .Acq⟩, {}⟩, Vd, _ => ⟨⟨.w, false, .Weak⟩, {}⟩
  | _, _, _ => e_req.req

noncomputable def Behaviour.reqToDirOfRequestEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : ValidRequest :=
  let state_before := b.stateBefore n e_req init
  e_req.reqToDirOfRequestEvent n state_before.cache

/-- Axiom 3. The Request field of a Directory Event corresponding to a Request Event (Cache Event). -/
structure Behaviour.requestDirectoryEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEvent : e_dir.isDirEventOfReqEvent n e_req
  sameAddr : e_req.addr = e_dir.addr
  dirReq :  e_dir.req = b.reqToDirOfRequestEvent n e_req init -- from analysis on e_req and the state it's made on
  dirState : e_dir.isDirEventOfDirState n (b.stateAfter n e_dir init).directory

structure Behaviour.cacheEncapsulatesCorrespondingDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapDir : e_req.Encapsulates n e_dir
  dirCorresponds : b.requestDirectoryEvent n e_req e_dir init
  dirInB : e_dir ∈ b.es
  reqInB : e_req ∈ b.es

structure Behaviour.reqEncapsulatesDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n e_req e_dir init
  notDowngrade : ¬ e_dir.down

structure Behaviour.reqEncapCorrespondingDirEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : Prop where
  reqEncapCorrDir : ∃ e_dir ∈ b.es, b.reqEncapsulatesDirEvent n e_req e_dir init

structure Behaviour.evictEncapsulatesCorrespondingDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n e_req e_dir init
  isDowngrade : e_dir.down

structure Behaviour.evictEncapCorrespondingDirEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : Prop where
  evictEncapCorrDir : ∃ e_dir ∈ b.es, b.evictEncapsulatesCorrespondingDirEvent n e_req e_dir init

/--Axiom 4. Acquire invalidates other Vc cache entries after it's directory access. -/
structure Behaviour.acquireInvalidates (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isAcquire : e_req.isAcquire
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n e_req init
  invalOther : ∀ addr ≠ e_req.addr, ∃ e_inval ∈ b.es, e_dir.OrderedBefore n e_inval ∧ e_inval.isVcInval

/-- Axiom 5. Non Coherent Release writes back other Vd cache entries before it's directory access. -/
structure Behaviour.ncReleaseWritesBack (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isRelease : e_req.isNCRelease
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n e_req init
  writeBackOther : ∀ addr ≠ e_req.addr, ∃ e_wb ∈ b.es, e_wb.OrderedBefore n e_dir ∧ e_wb.isVdWriteBack

/-- Def: Props for Coherent Request encapsulating a Directory Event -/
structure Behaviour.requestCoherentNoPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  isCoherent : e_req.req.val.coherent
  noPerms : (b.stateBefore n e_req (init.stateAt n e_req)).cache < e_req.req.MRS
  notDowngrade : ¬ e_req.down
  reqEncapDir : b.reqEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)

/- Defs: Props on when a non-coherent Release accesses the Directory -/
structure Behaviour.dirReleaseGetVBeforeWBEncapInRequest (b : Behaviour n) (e_req e_dir_getv e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  getVBeforeWB : e_dir_getv.OrderedBefore n e_dir_wb
  reqEncapGetV : b.reqEncapsulatesDirEvent n e_req e_dir_wb (init.stateAt n e_req)

structure Behaviour.ncReleaseOnI (b : Behaviour n) (e_req e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  madeOnI : b.stateBefore n e_req (init.stateAt n e_req) = Sum.inl I
  encapDirGetV : ∃ e_dir_getv ∈ b.es, b.dirReleaseGetVBeforeWBEncapInRequest n e_req e_dir_getv e_dir_wb init

/-- Def: Props for a non-coherent Release encapsulating one (or two) Directory Events (if on I state) -/
structure Behaviour.nonCoherentReleaseEncapDirEvents (b : Behaviour n) (e_req : CacheEvent n) (e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  notCoherent : ¬ e_req.Coherent
  isRelease : e_req.req.val.consistency = .Rel
  encapsDirWB : b.reqEncapsulatesDirEvent n (Event.cacheEvent e_req) e_dir_wb (Sum.inl Vd)
  encapGetVFromI : b.ncReleaseOnI n (Event.cacheEvent e_req) e_dir_wb init

def Behaviour.nonCoherentRelease (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop :=
  ∃ e_dir_wb ∈ b.es, b.nonCoherentReleaseEncapDirEvents n e_req e_dir_wb init

/- Def: Props for a non-coherent Acquire encapsulating a Directory Event. -/
structure Behaviour.acquireEncapDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isAcquire : e_req.req.val.consistency = .Acq
  madeOnNCStates : let made_on_state := b.stateBefore n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))
    made_on_state = VdEntry n ∨ made_on_state = VcEntry n ∨ made_on_state = IEntry n
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))

/-- Def: Props stating when a non-coherent weak operation (read/write) encapsulates a Directory Event -/
structure Behaviour.ncWeakRequestEncapDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  notCoherent : ¬ e_req.Coherent
  isWeak : e_req.req.val.consistency = .Weak
  madeOnIState : b.stateBefore n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req)) = IEntry n
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))

/-- Def Props stating when an Evicting Weak Non-Coherent Write accesses the Directory -/
structure Behaviour.evictVdWBEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isVdWriteBack : e_req.req.val = ⟨.w, false, .Weak⟩
  madeOnVdState : b.stateBefore n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req)) = VdEntry n
  encapWBDirEvent : b.evictEncapCorrespondingDirEvent n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))

structure Behaviour.evictSCPutMEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isPutM : e_req.req.val = ⟨.w, true, .SC⟩
  madeOnSW : b.stateBefore n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req)) = SWEntry n
  encapPutMDirEvent : b.evictEncapCorrespondingDirEvent n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))

structure Behaviour.evictSCPutSEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isPutS : e_req.req.val = ⟨.r, true, .SC⟩
  madeOnMR : b.stateBefore n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req)) = MREntry n
  encapPutSDirEvent : b.evictEncapCorrespondingDirEvent n (Event.cacheEvent e_req) (init.stateAt n (Event.cacheEvent e_req))

/-- Axiom 6: When a Request Event encapsulates Directory Events to access/request from the Directory. -/
inductive Behaviour.requestCoherentAccessesDirectory (b : Behaviour n) (ce : CacheEvent n) (init : InitialSystemState n) : Prop
| coherentRequest : b.requestCoherentNoPerms n (Event.cacheEvent ce) init → Behaviour.requestCoherentAccessesDirectory b ce init
| nonCoherentRelease : b.nonCoherentRelease n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: have a struct and fields for OnI and OnV
| acquire : b.acquireEncapDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: struct field : Not on MR
| weakWrite : b.ncWeakRequestEncapDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: struct field : On I
| weakRead : b.ncWeakRequestEncapDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: struct field : On I
| evictVdWB : b.evictVdWBEncapsulatesDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutM : b.evictSCPutMEncapsulatesDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutS : b.evictSCPutSEncapsulatesDirEvent n ce init → Behaviour.requestCoherentAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}

/-- Axiom 7, a Cache Entry in Vd State may writeback -/
structure Behaviour.vdCacheEntryWriteBackLater (b : Behaviour n) (ce : CacheEvent n) (vd_wb_e : Event n) (init : InitialSystemState n) : Prop where
  vdStateAfterEvent : b.stateAfter n (Event.cacheEvent ce) (init.stateAt n (Event.cacheEvent ce)) = VdEntry n
  wbImmPred : ∃ vd_wb_e ∈ b.es, b.ImmediateBottomPredecessor n (Event.cacheEvent ce) vd_wb_e

/-- Axiom 8, messages from the directory are ordered by Cache Event `deid?` field. -/
structure Behaviour.deidOrdered : Prop where
  orderedDeid : ∀ e₁ e₂ : Event n, e₁.deidOrderBefore n e₂
  orderedEvents : ∀ e₁ e₂ : Event n, e₁.OrderedBefore n e₂
  inB : ∀ e : Event n, ∀ b : Behaviour n, e ∈ b.es

-- inductive Behaviour.coherentWriteAtDirectoryEncapDowngrades (b : Behaviour n) (e_dir : Event n)

structure Behaviour.coherentWriteDowngradeOthers (b : Behaviour n) (e_dir : Event n) : Prop where
  isDirEvent : e_dir.isDirectoryEvent
  coherentWrite : e_dir.req.isCoherentWrite
  -- TODO: Write an inductive: based on the state of the directory that e_dir occurs in, exists downgrades at other caches

/-- Axiom 9, Coherent-Write request to Directory results in Downgrade at other caches axiom. -/
structure Behaviour.coherentWriteDirDowngradeOthers : Prop where
  encapDowngrades : ∀ b : Behaviour n, ∃ e ∈ b.es, b.coherentWriteDowngradeOthers n e
