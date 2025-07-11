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

/-- Key definition: (Not Acq, Rel, Weak Write). A request cache event has permissions if it's MRS is less than or equal the state it's made on. -/
def Behaviour.eventOnStateHasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  e_req.req.MRS ≤ (b.stateBefore n (init.stateAt n e_req) e_req).cache

/-- Key Definition: A request does not have permissions if the negation of it's MRS is less than the state it's made on is true. -/
def Behaviour.eventOnStateNoPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  ¬ b.eventOnStateHasPerms n init e_req

def Behaviour.eventOnCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache.c
def Behaviour.eventOnNonCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  ¬ (b.stateBefore n (init.stateAt n e_req) e_req).cache.c

def Behaviour.acqRelWeakWriteNoPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  ¬ (b.eventOnCoherentState n init e_req ∧ b.eventOnStateHasPerms n init e_req)

noncomputable def Event.reqToDirOfRequestEvent (e_req : Event n) (state_before : State) : ValidRequest :=
  match e_req.req, state_before, e_req.down with
  | ⟨⟨.w, false, _⟩, _⟩, I, false => ⟨⟨.r, false, .Weak⟩, {}⟩
  | ⟨⟨.r, false, .Acq⟩, {}⟩, Vd, _ => ⟨⟨.w, false, .Weak⟩, {}⟩
  | _, _, _ => e_req.req

noncomputable def Behaviour.reqToDirOfRequestEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req : Event n) : ValidRequest :=
  if e_req.req.val = ⟨.w, false, .Rel⟩ ∧ rel_wb then
    e_req.reqToDirOfRequestEvent n Vd
  else
    let state_before := b.stateBefore n init e_req
    e_req.reqToDirOfRequestEvent n state_before.cache

/-- Axiom 3. The Request field of a Directory Event corresponding to a Request Event (Cache Event). -/
structure Behaviour.requestDirectoryEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req e_dir : Event n) : Prop where
  reqEvent : e_dir.isDirEventOfReqEvent n e_req
  sameAddr : e_req.addr = e_dir.addr
  dirReq :  e_dir.req = b.reqToDirOfRequestEvent n init rel_wb e_req -- from analysis on e_req and the state it's made on
  dirState : e_dir.isDirEventOfDirState n (b.stateAfter n init e_dir).directory

structure DirectoryEvent.matchesCacheEvent (de : DirectoryEvent n) (ce : CacheEvent n) : Prop where
  correspondingCE : de.eReq = ce
  sameDown : de.down = ce.down

def Event.dirEventOfReqEvent (e_dir e_req : Event n) : Prop := match e_dir, e_req with
| .directoryEvent de, .cacheEvent ce => de.matchesCacheEvent n ce
| _, _ => false

structure Behaviour.cacheEncapsulatesCorrespondingDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req e_dir : Event n) : Prop where
  isDir : e_dir.isDirectoryEvent n
  reqEncapDir : e_req.Encapsulates n e_dir
  dirCorresponds : b.requestDirectoryEvent n init rel_wb e_req e_dir
  dirOfReq : e_dir.dirEventOfReqEvent n e_req
  dirInB : e_dir ∈ b.es
  reqInB : e_req ∈ b.es

structure Behaviour.cacheEncapCorrespondingDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req : Event n) : Prop where
  cacheDirEvent : ∃ e_dir ∈ b.es, b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e_req e_dir

structure Behaviour.reqEncapsulatesDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req e_dir : Event n) : Prop where
  reqEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e_req e_dir
  notDowngrade : ¬ e_dir.down

structure Behaviour.reqEncapCorrespondingDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req : Event n) : Prop where
  reqEncapCorrDir : ∃ e_dir ∈ b.es, b.reqEncapsulatesDirEvent n init rel_wb e_req e_dir

structure Behaviour.evictEncapsulatesCorrespondingDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req e_dir : Event n) : Prop where
  evictEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n init rel_wb e_req e_dir
  isDowngrade : e_dir.down

structure Behaviour.evictEncapCorrespondingDirEvent (b : Behaviour n) (init : EntryState n) (rel_wb : Bool) (e_req : Event n) : Prop where
  evictEncapCorrDir : ∃ e_dir ∈ b.es, b.evictEncapsulatesCorrespondingDirEvent n init rel_wb e_req e_dir

/--Axiom 4. Acquire invalidates other Vc cache entries after it's directory access. -/
structure Behaviour.acquireInvalidates (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isAcquire : e_req.isAcquire
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n init true e_req
  invalOther : ∀ addr ≠ e_req.addr, ∃ e_inval ∈ b.es, e_dir.OrderedBefore n e_inval ∧ e_inval.isVcInval

/-- Axiom 5. Non Coherent Release writes back other Vd cache entries before it's directory access. -/
structure Behaviour.ncReleaseWritesBack (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isRelease : e_req.isNCRelease
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n init true e_req
  writeBackOther : ∀ addr ≠ e_req.addr, ∃ e_wb ∈ b.es, e_wb.OrderedBefore n e_dir ∧ e_wb.isVdWriteBack

/-- Def: Props for Coherent Request encapsulating a Directory Event -/
structure Behaviour.requestCoherentNoPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  isCoherent : e_req.req.val.coherent
  noPerms : b.eventOnStateNoPerms n init e_req
  notDowngrade : ¬ e_req.down
  reqEncapDir : b.reqEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

/- Defs: Props on when a non-coherent Release accesses the Directory -/
structure Behaviour.dirReleaseGetVBeforeWBEncapInRequest (b : Behaviour n) (e_req e_dir_getv e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  getVBeforeWB : e_dir_getv.OrderedBefore n e_dir_wb
  reqEncapGetV : b.reqEncapsulatesDirEvent n (init.stateAt n e_req) false e_req e_dir_wb -- [NOTE] this is one of two places where `rel_wb` is false

structure Behaviour.ncReleaseOnI (b : Behaviour n) (e_req e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  madeOnI : b.stateBefore n (init.stateAt n e_req) e_req = Sum.inl I
  encapDirGetV : ∃ e_dir_getv ∈ b.es, b.dirReleaseGetVBeforeWBEncapInRequest n e_req e_dir_getv e_dir_wb init

/-- Def: Props for a non-coherent Release encapsulating one (or two) Directory Events (if on I state) -/
structure Behaviour.nonCoherentReleaseEncapDirEvents (b : Behaviour n) (e_req : CacheEvent n) (e_dir_wb : Event n) (init : InitialSystemState n) : Prop where
  isRelease : e_req.isNcRelease
  encapsDirWB : b.reqEncapsulatesDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req) e_dir_wb
  encapGetVFromI : b.ncReleaseOnI n (Event.cacheEvent e_req) e_dir_wb init

structure Behaviour.nonCoherentRelease (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  notDowngrade : ¬ e_req.down
  noCoherentPerms : b.acqRelWeakWriteNoPerms n init (Event.cacheEvent e_req)
  existsDirWb : ∃ e_dir_wb ∈ b.es, b.nonCoherentReleaseEncapDirEvents n e_req e_dir_wb init

/- Def: Props for a non-coherent Acquire encapsulating a Directory Event. -/
structure Behaviour.acquireEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  notDowngrade : ¬ e_req.down
  isAcquire : e_req.isAcquire -- e_req.req.val.consistency = .Acq
  madeOnNCStates : b.acqRelWeakWriteNoPerms n init (Event.cacheEvent e_req)
    -- let made_on_state := b.stateBefore n (init.stateAt n (Event.cacheEvent e_req)) (Event.cacheEvent e_req)
    -- made_on_state = VdEntry n ∨ made_on_state = VcEntry n ∨ made_on_state = IEntry n
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

/-- Def: Props stating when a non-coherent weak operation (read/write) encapsulates a Directory Event -/
structure Behaviour.ncWeakRequestEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  -- isNcWeak : e_req.isNcWeak
  madeOnIState : b.eventOnStateNoPerms n init (Event.cacheEvent e_req) -- b.stateBefore n (init.stateAt n (Event.cacheEvent e_req)) (Event.cacheEvent e_req) = IEntry n
  notDowngrade : ¬ e_req.down

/-- Prop: NC Weak Read encaps a dir event -/
structure Behaviour.ncWeakReadEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  ncWeakReq : b.ncWeakRequestEncapDirEvent n init e_req
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)
  isRead : e_req.isNcWeakRead
  notDowngrade : ¬ e_req.down

/-- Prop: NC Weak Read encaps a dir event -/
structure Behaviour.ncWeakWriteEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  ncWeakReq : b.ncWeakRequestEncapDirEvent n init e_req
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) false (Event.cacheEvent e_req) -- [NOTE] One of two places where `rel_wb` is false
  isWrite : e_req.isNcWeakWrite
  notDowngrade : ¬ e_req.down

def Behaviour.evictOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop :=
  (b.stateBefore n (init.stateAt n (Event.cacheEvent e_req)) (Event.cacheEvent e_req)).cache = e_req.MRS

def Behaviour.eventOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache = e_req.req.MRS

/-- Def Props stating when an Evicting Weak Non-Coherent Write accesses the Directory -/
structure Behaviour.evictVdWBEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  isDowngrade : e_req.down
  isVdWriteBack : e_req.req.val = ⟨.w, false, .Weak⟩
  mrsVdState : e_req.MRS = Vd
  madeOnMrs : b.evictOnMRSState n init e_req
  encapWBDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

structure Behaviour.evictSCPutMEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  isDowngrade : e_req.down
  isPutM : e_req.req.val = ⟨.w, true, .SC⟩
  mrsSWState : e_req.MRS = SW
  madeOnMrs : b.evictOnMRSState n init e_req
  encapPutMDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

structure Behaviour.evictSCPutSEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  isDowngrade : e_req.down
  isPutS : e_req.req.val = ⟨.r, true, .SC⟩
  mrsMRState : e_req.MRS = MR
  madeOnMrs : b.evictOnMRSState n init e_req
  encapPutSDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

/-- Axiom 6: When a Request Event encapsulates Directory Events to access/request from the Directory. -/
inductive Behaviour.requestAccessesDirectory (b : Behaviour n) (ce : CacheEvent n) (init : InitialSystemState n) : Prop
| coherentRequest (hcohrent_req_of_no_perms : b.requestCoherentNoPerms n init (Event.cacheEvent ce)) : Behaviour.requestAccessesDirectory b ce init
| nonCoherentRelease (hnc_rel : b.nonCoherentRelease n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: have a struct and fields for OnI and OnV
| acquire (hacq_encap_dir : b.acquireEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : Not on MR
| weakWrite (hncww_encap_dir : b.ncWeakWriteEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| weakRead (hncwr_encap_dir : b.ncWeakReadEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| evictVdWB (hevict_vd_wb_encap_dir : b.evictVdWBEncapsulatesDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutM (hevict_put_m_encap_dir : b.evictSCPutMEncapsulatesDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutS (hevict_put_s_encap_dir : b.evictSCPutSEncapsulatesDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}

/-- Axiom 6 Event → CacheEvent Wrapper. -/
def Behaviour.requestAccessesDirectoryWrapper (b : Behaviour n) (e : Event n) (init : InitialSystemState n) : Prop := match e with
  | .cacheEvent ce => b.requestAccessesDirectory n ce init
  | .directoryEvent _ => false

/-- Axiom 6 Structure Wrapper for use in Lemmas. -/
structure Behaviour.axRequestAccessesDirectory : Prop where
  reqAccessDir : ∀ b : Behaviour n, ∀ e ∈ b.es, ∀ init : InitialSystemState n, b.requestAccessesDirectoryWrapper n e init

/-- Axiom 7, a Cache Entry in Vd State may writeback -/
structure Behaviour.vdCacheEntryWriteBackLater (b : Behaviour n) (e : Event n) /-(vd_wb_e : Event n)-/ (init : InitialSystemState n) : Prop where
  vdStateAfterEvent : b.stateAfter n (init.stateAt n e) e = VdEntry n
  wbImmPred : ∃ vd_wb_e ∈ b.es, b.ImmediateBottomPredecessor n e vd_wb_e

/-- Def. state that two events `e₁` `e₂` are orderedBefore if their Deid fields are orderedBefore. -/
structure Behaviour.orderedDeidEvents (b : Behaviour n) (e₁ e₂ : Event n) : Prop where
  orderedDeid : e₁.deidOrderBefore n e₂
  orderedEvents : e₁.OrderedBefore n e₂
  e₁InB : e₁ ∈ b.es
  e₂InB : e₂ ∈ b.es

/-- Axiom 8, messages from the directory are ordered by Cache Event `deid?` field. -/
structure Behaviour.deidOrdered : Prop where
  orderedDeidEvents : ∀ b : Behaviour n, ∀ e₁ e₂ : Event n, b.orderedDeidEvents n e₁ e₂

/-- Def. Constraints on fields of Forwarded Downgrade. -/
structure Behaviour.requestDowngradePrevOwner (b : Behaviour n) (e_req e_dir e_fwd_down : Event n) (init : InitialSystemState n) : Prop where
  atPrevOwner : e_fwd_down.downgradeAtPrevOwner n (b.stateBefore n (init.stateAt n e_dir) e_dir).directory
  fwdFromRequester : e_req.downgradeCorrespondingToRequest n e_fwd_down
  idCorrespondDir : e_fwd_down.fromDirectory n e_dir
  dirEncapDowngrade : e_dir.Encapsulates n e_fwd_down -- already have from Request Encaps Directory Event
  reqEncapDir : e_req.Encapsulates n e_dir

/- Def. Constraints on fields of Forwarded Downgrade events, and Grant Events. -/
structure Behaviour.downgradeAtPrevOwner (b : Behaviour n) (e_req e_dir e_fwd_down e_grant : Event n) (init : InitialSystemState n) : Prop where
  downgradePrevOwner : b.requestDowngradePrevOwner n e_req e_dir e_fwd_down init
  grantRels : e_req.encapGrantAfterDirEvent n e_dir e_grant

/- Def. When a Coherent Request causes a Forwarded Downgrade to the previous owner at the Directory. (and a Grant Event) -/
structure Behaviour.fwdCoherentRequestToOwner (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqDirOnSW   : b.stateBefore n (init.stateAt n e_dir) e_dir = SWEntry n
  fwdPrevOwner : ∃ e_down ∈ b.es, ∃ e_grant ∈ b.es, b.downgradeAtPrevOwner n e_req e_dir e_down e_grant init
/-- Def. Downgrade to sharers -/
def Behaviour.downgradeAtSharers (b : Behaviour n) (dir_state : DirectoryState n) (e_req e_dir : Event n) : Prop := match dir_state with
  | .MR _ sharers => ∃ e_grant ∈ b.es, ∀ s ∈ sharers, ∃ e_down ∈ b.es, match e_req, e_down with
    | .cacheEvent request, .cacheEvent downgrade =>
      request.downgradeOfReqToCache n downgrade s ∧ e_req.fwdMRDowngradeEventOrdering n e_dir e_down e_grant
    | _, _ => false
  | _ => false

/-- Def. fwd coherent request to other Sharer caches -/
structure Behaviour.fwdCoherentRequestToSharers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  cWriteOnMR : b.stateBefore n (init.stateAt n e_dir) e_dir = MREntry n
  fwdSharers : b.downgradeAtSharers n (b.stateBefore n (init.stateAt n e_dir) e_dir).directory e_req e_dir

/- Def. Which directory states will a Coherent Write Request cause downgrades at other caches. Includes Props on Downgrade Events to
other caches. -/
inductive Behaviour.coherentWriteAtDirectoryEncapDowngrades (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| cWriteOnSW : b.fwdCoherentRequestToOwner n e_req e_dir init → Behaviour.coherentWriteAtDirectoryEncapDowngrades b e_req e_dir init
| cWriteOnMR : b.fwdCoherentRequestToSharers n e_req e_dir init → Behaviour.coherentWriteAtDirectoryEncapDowngrades b e_req e_dir init

/-- Def. When a coherent write to the Directory downgrades other caches. -/
structure Behaviour.coherentWriteDowngradeOthers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  isDirEvent : e_dir.isDirectoryEvent
  dirCoherentWrite : e_dir.req.isCoherentWrite
  isCacheEvent : e_req.isCacheEvent
  reqCoherentWrite : e_req.req.isCoherentWrite
  downgradeOtherCaches : b.coherentWriteAtDirectoryEncapDowngrades n e_req e_dir init

/-- Axiom 9, Coherent-Write request to Directory results in Downgrade at other caches axiom. -/
structure Behaviour.coherentWriteDirDowngradeOthers : Prop where
  encapDowngrades : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∀ e_dir ∈ b.es, b.coherentWriteDowngradeOthers n e_req e_dir init

/- Def. Which directory states will a Coherent Read Request cause downgrades at other caches. Includes Props on Downgrade Events to
other caches. -/
inductive Behaviour.coherentRequestAtDirectoryEncapDowngrades (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| cReadOnSW : b.fwdCoherentRequestToOwner n e_req e_dir init → Behaviour.coherentRequestAtDirectoryEncapDowngrades b e_req e_dir init

/-- Def. Props on Coherent Read Request event accessing the directory -/
structure Behaviour.coherentReadDowngradeOthers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  isDirEvent : e_dir.isDirectoryEvent
  dirCoherentRead : e_dir.req.isCoherentRead
  isCacheEvent : e_req.isCacheEvent
  reqCoherentRead : e_req.req.isCoherentRead
  downgradeOtherCaches : b.coherentRequestAtDirectoryEncapDowngrades n e_req e_dir init

/-- Axiom 10. Coherent-Read request to Directory results in Downgrade at other caches axiom. -/
structure Behaviour.coherentReadDirDowngradeOthers : Prop where
  encapDowngrade : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∀ e_dir ∈ b.es, b.coherentReadDowngradeOthers n e_req e_dir init

/-- Prop Structure Helper for Axiom 11. Coherent Evict at Directory encapsulates a Grant OrderedAfter the Directory Event. -/
structure Behaviour.coherentEvictDirGrantOrdering (b : Behaviour n) (e_req e_dir e_grant : Event n) : Prop where
  isEvict : e_req.isEvict
  reqEncapDir : e_req.Encapsulates n e_dir
  reqDirGrantOrderings : e_req.encapGrantAfterDirEvent n e_dir e_grant

/-- Axiom 11. Coherent Evict at Directory encapsulates a Grant OrderedAfter the Directory Event. -/
structure Behaviour.coherentEvictGetsGrant : Prop where
  evictGetsGrant : ∀ b : Behaviour n, ∀ e_req ∈ b.es, ∀ e_dir ∈ b.es, ∃ e_grant ∈ b.es, b.coherentEvictDirGrantOrdering n e_req e_dir e_grant

structure Behaviour.nonCoherentReqOnSWDowngradeOthers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  dirNCReq : e_dir.req.NonCoherent
  isDir : e_dir.isDirectoryEvent
  isCache : e_req.isCacheEvent
  reqDirOnSW : b.stateBefore n (init.stateAt n e_dir) e_dir = SWEntry n
  fwdPrevOwner : ∃ e_down ∈ b.es, b.requestDowngradePrevOwner n e_req e_dir e_down init

/-- Axiom 12. Non-Coherent Write/Read on SW Directory State results in Downgrades. -/
structure Behaviour.nonCoherentRequestDowngradeOthers : Prop where
  ncReqDowngradeSWOwner : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∀ e_dir ∈ b.es,
    b.nonCoherentReqOnSWDowngradeOthers n e_req e_dir init

/-- Def.a (broadcast before e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEventBefore (b : Behaviour n) (addr : Addr) (e_base e_original e_dir: Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b.es, e_base.baseEncapBroadcastBefore n addr' e_original e_cast_copy e_dir

/-- Def.b (broadcast after e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEventAfter (b : Behaviour n) (addr : Addr) (e_base e_original e_dir : Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b.es, e_base.baseEncapBroadcastAfter n addr' e_original e_cast_copy e_dir

/-- Def.c (broadcast after e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEvent (b : Behaviour n) (addr : Addr) (e_base e_original : Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b.es, e_base.baseEncapBroadcast n addr' e_original e_cast_copy

/-- Def 2.36.a Broadcast Event `e` to Other Cache Entries, Ordered Before an encapsulated Directory Event. -/
structure Behaviour.broadcastToOtherEntriesBeforeDir (b : Behaviour n) (e_base e_original e_dir : Event n) : Prop where
  broadcast : b.broadcastEventBefore n e_base.addr e_base e_original e_dir

/-- Def 2.36.b Broadcast Event `e` to Other Cache Entries, Ordered After an encapsulated Directory Event. -/
structure Behaviour.broadcastToOtherEntriesAfterDir (b : Behaviour n) (e_base e_original e_dir : Event n) : Prop where
  broadcast : b.broadcastEventAfter n e_base.addr e_base e_original e_dir

/-- Def 2.36.c Broadcast Event `e` to Other Cache Entries. -/
structure Behaviour.broadcastToOtherEntries (b : Behaviour n) (e_base e_original : Event n) : Prop where
  broadcast : b.broadcastEvent n e_base.addr e_base e_original

/-- Def. Acquire Invalidates Other Entries in Vc after accessing the Directory -/
structure Behaviour.acqInvalOtherEntries (b : Behaviour n) (e_req e_inval e_dir : Event n) (init : InitialSystemState n) : Prop where
  isAcq : e_req.isAcquire
  isDir : e_dir.isDirectoryEvent
  dirCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_dir e_req
  isVcInval : e_inval.isVcInval
  acqEncapDir : e_req.Encapsulates n e_dir
  broadcastInval : b.broadcastToOtherEntriesAfterDir n e_req e_inval e_dir

/-- Def. Non-Coherent Release WritesBack Other Entries in Vd before accessing the Directory -/
structure Behaviour.relWriteBackOtherEntries (b : Behaviour n) (e_req e_wb e_dir : Event n) (init : InitialSystemState n) : Prop where
  isNCRel : e_req.isNCRelease
  isDir : e_dir.isDirectoryEvent
  dirCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_dir e_req
  isVdWriteBack : e_wb.isVdWriteBack
  relEncapDir : e_req.Encapsulates n e_dir
  broadcastWB : b.broadcastToOtherEntriesBeforeDir n e_req e_wb e_dir

/-- Def. (Lazy) Coherent Release WritesBack Other Entries in Vd when receiving a downgrade.
We assume it to be Lazy if it's Protocol Interface contains a Non-Coherent Weak Write. -/
structure Behaviour.coherentRelDowngradeWriteBackOthers (b : Behaviour n) (e_down e_wb : Event n) (p_i : Protocol.interface) : Prop where
  isVdWriteBack : e_wb.isVdWriteBack
  broadcastWB : b.broadcastToOtherEntries n e_down e_wb
  gotDowngrade : e_down.down -- Assume it arrives on SW state.
  -- Coherent Release is Lazy, because we have a Non-Coherent WeakWrite in the Protocol Interface
  cRelInPI : CoherentRelease ∈ (e_down.interfaceMatchingProtocol n p_i).val
  ncWeakWriteInPI : NonCoherentWeakWrite ∈ (e_down.interfaceMatchingProtocol n p_i).val

/-- Axiom 13. Release and Acquire Broadcast WriteBacks and Invalidations to other cache entries Axiom. -/
structure Behaviour.relAcqBroadcast : Prop where
  acquireInvals : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∀ e_inval ∈ b.es, ∀ e_dir ∈ b.es, b.acqInvalOtherEntries n e_req e_inval e_dir init
  ncReleaseWBs : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∀ e_wb ∈ b.es, ∀ e_dir ∈ b.es, b.relWriteBackOtherEntries n e_req e_wb e_dir init
  downgradeWB : ∀ b : Behaviour n, ∀ e_down ∈ b.es, ∀ e_wb ∈ b.es, ∀ p_i : Protocol.interface, b.coherentRelDowngradeWriteBackOthers n e_down e_wb p_i

/- ------------- Work in progress for Lemma 3. May or may not need. ------------- -/
/-
def CacheEvent.isRequest (e : CacheEvent n) : Prop := e.cid = e.rid
def Event.isRequest (e : Event n) : Prop := match e with
| .cacheEvent ce => ce.cid = ce.rid
| .directoryEvent _ => false
structure Event.isReqNotDown (e : Event n) : Prop where
  isReq : e.isRequest
  notDowngrade : ¬e.down
def RequestEvent := {e : Event n // e.isReqNotDown n}
def DirEvent := {e : Event n // e.isDirectoryEvent n}
-/
def Behaviour.reqEncapCorrespondingDir (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

def Behaviour.reqLeavesStateAtLeast (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (state : State) : Prop :=
  state ≤ (b.stateAfter n (init.stateAt n e_req) e_req).cache

structure Behaviour.reqWithCorrespondDirLeavesStateAtLeast (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (state : State) : Prop where
  encapCorresponding : b.reqEncapCorrespondingDir n e_req init
  stateAfterAtLeast : b.reqLeavesStateAtLeast n e_req init state

def Behaviour.eventOnCoherentStateAtLeastMRS (b : Behaviour n) (e : Event n) (init : InitialSystemState n) : Prop := match e with
| .cacheEvent ce => let state_made_on := init.stateAt n e |>.cache n;
  state_made_on.c ∧ ce.req.MRS ≤ (b.stateBefore n (init.stateAt n e) e).cache n
| .directoryEvent _ => false

/-- (Old. Don't use.) A Transitive Relation from a Request Event to a Directory Event. For Lemma 3. -/
def Event.relates (e₁ e₂ : Event n) : Prop := e₁.Encapsulates n e₂ ∨ e₁.Ordered n e₂

/- Defs describing where a Coherent Request's Directory Event that links the Request's data to the total order of Directory Entry Events. -/

def Event.isNcRelAcqWeakWrite : Event n → Prop
| e => e.isAcquire ∨ e.isNCRelease ∨ e.isNcWeakWrite
def Event.notNcRelAcqWeakWrite : Event n → Prop
| e => ¬ e.isNcRelAcqWeakWrite

def Event.isNcRelAcqWeakWriteRead : Event n → Prop
| e => e.isAcquire ∨ e.isNCRelease ∨ e.isNcWeakWrite ∨ e.isNcWeakRead
def Event.notNcRelAcqWeakWriteRead : Event n → Prop
| e => ¬ e.isNcRelAcqWeakWriteRead

def Event.isNcRelAcq : Event n → Prop
| e => e.isAcquire ∨ e.isNCRelease
/-
def Behaviour.eventOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache = e_req.req.MRS
-/

/-- Def. Prop on a Request Event `e_req`.
The state `e_req` is made on is not sufficient to be able to complete the request in cache.
For Acq, Non-Coherent Rel, and Weak Writes, this means the state it's made on is lower than it's `Minimum Required State (MRS)` AND is not coherent.
For other requests, SC, Coherent, and Weak Reads, this means it's state it's made on is lower that it's `MRS`.
In the case of Weak Reads, the state it's made on excludes `Vd`. -/
inductive Behaviour.reqMissingPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop
| downgrade (hreq_is_down : e_req.down) (hreq_on_mrs_state : b.eventOnMRSState n init e_req) : Behaviour.reqMissingPerms b init e_req
| noPermsForNonNcRelAcqWeakWrite (hreq_not_down : ¬ e_req.down) (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req) : Behaviour.reqMissingPerms b init e_req
| ncRelAcqWeakWriteNotOnCoherentState (hreq_not_down : ¬ e_req.down) (hreq_nc_rel_acq : e_req.isNcRelAcq) (hno_perms : b.acqRelWeakWriteNoPerms n init e_req) : Behaviour.reqMissingPerms b init e_req

structure Behaviour.reqHasNoPermsLeavesStateAtLeast (b : Behaviour n) (init : InitialSystemState n) (state : State) (e_req : Event n) : Prop where
  missingPerms : b.reqMissingPerms n init e_req
  stateAfterAtLeast : b.reqLeavesStateAtLeast n e_req init state
  -- encapDir : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

/-
/-- Wrapper structure Def. Prop on a Request Event `e_req`. `e_req` is made on a state where it doesn't have it's `MRS`.-/
structure Behaviour.inreqHasPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  noPerms : b.reqMissingPerms n init e_req
-/

/-- Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
def Behaviour.hasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  e_req.req.MRS ≤ (b.stateBefore n (init.stateAt n e_req) e_req).cache

noncomputable def Behaviour.stateReqMadeOn (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : State :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache

noncomputable def Behaviour.isReqMadeOnCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateReqMadeOn n init e_req).c

structure Behaviour.isReqHasPermsOnCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  hasPerms : b.hasPerms n init e_req
  onCoherentState : b.isReqMadeOnCoherentState n init e_req

structure Behaviour.isReqHasCoherentPermsNotVd (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  hasPerms : b.hasPerms n init e_req
  notOnVd : b.stateReqMadeOn n init e_req ≠ Vd
  coherentState : b.isReqMadeOnCoherentState n init e_req

/-- Wrapper structure Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
inductive Behaviour.reqHasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop
| hasPerms : e_req.isCoherent → b.hasPerms n init e_req → Behaviour.reqHasPerms b init e_req
| ncRelAcqWeakWriteHasCoherentPerms : e_req.isNcRelAcqWeakWrite → b.isReqHasPermsOnCoherentState n init e_req → Behaviour.reqHasPerms b init e_req
| ncWeakReadHasPermsNotVd : e_req.isNcWeakRead → b.isReqHasCoherentPermsNotVd n init e_req → Behaviour.reqHasPerms b init e_req

/-- Def. Structure stating a request event `e_req` has insufficient permissions, so it encapsulates directory event. -/
structure Behaviour.isReqHasNoPermsSoEncapDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  noPerms : b.reqMissingPerms n init e_req
  reqEncapDir : e_req.Encapsulates n e_dir

def Behaviour.predWithCorrespondingDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  (b.reqWithCorrespondDirLeavesStateAtLeast n e_pred init (b.stateBefore n (init.stateAt n e_req) e_req |>.cache))

def Behaviour.immBottomPredEncapCorrDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predWithCorrespondingDirLeavesStateAtLeastReq n · e_req init)

def Behaviour.predHasNoPermsAndLeavesStateAtLeastReq (b : Behaviour n) (init : InitialSystemState n) (e_pred e_req : Event n) : Prop :=
  b.reqHasNoPermsLeavesStateAtLeast n init (b.stateBefore n (init.stateAt n e_req) e_req |>.cache) e_pred

def Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast (b : Behaviour n) (init : InitialSystemState n) (e_pred e_req : Event n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predHasNoPermsAndLeavesStateAtLeastReq n init · e_req)

def Behaviour.reqHasPermsSoDirPred (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  ∃ e_pred ∈ b.es, b.immBottomPredHasNoPermsAndLeavesStateAtLeast n init e_pred e_req

/-
/- Not used ? remove? -/
/-- Inductive Prop. State where is the directory event that obtains permissions for a Coherent Request. -/
inductive Behaviour.dirEventOfCoherentReq (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop
| encapDir : b.isReqHasNoPermsSoEncapDir n init e_req e_dir → Behaviour.dirEventOfCoherentReq b init e_req e_dir
| orderBeforeDir : b.reqHasPermsSoDirPred n init e_req → Behaviour.dirEventOfCoherentReq b init e_req e_dir -- [NOTE]: not technically necessary
-/

structure Behaviour.ncWeakReqOnVd (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  weakReq : e_req.isNcWeak
  reqOnOrAfterVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n ∨ b.stateAfter n (init.stateAt n e_req) e_req = VdEntry n

/-- Succeeding Request Event on Vd that accesses the Directory -/
structure Behaviour.reqOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  stateBeforeAsVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n
  -- [NOTE]: Remebmer to use Axiom 6 to solve this.
  encapCorresponding : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir

def Behaviour.succOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_succ e_dir : Event n) : Prop :=
  b.reqOnVdWithCorrespondingDir n init e_succ e_dir

/-- Def. Prop. there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
def Behaviour.immBottomSuccOnVdEncapCorrDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop :=
  ∃ e_succ ∈ b.es, b.ImmediateBottomSuccSatisfyingProp n e_req e_succ (b.succOnVdWithCorrespondingDir n init · e_dir)

/-- Trying something new: separately state the cases of where -/
inductive Behaviour.dirAccessOfRequest (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop
| encapDir (hreq_missing_perms : b.reqMissingPerms n init e_req)
  (hencap_dir : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir)
  : Behaviour.dirAccessOfRequest b init e_req e_dir
| orderBeforeDir
  (hreq_has_perms : b.reqHasPerms n init e_req)
  (hexists_pred_getting_perms : b.reqHasPermsSoDirPred n init e_req)
  (hpred_accesses_dir : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose e_dir)
  : Behaviour.dirAccessOfRequest b init e_req e_dir
| orderAfterDir (hweak_read_on_vd : b.ncWeakReqOnVd n init e_req) (hsucc_encap_dir : b.immBottomSuccOnVdEncapCorrDir n init e_req e_dir)
  : Behaviour.dirAccessOfRequest b init e_req e_dir


/-- Top Level Def. Prop on a Coherent Request `e_coh_req`, and where will the directory event that gave it cache permissions for `e_coh_req`'s access is. -/
structure Behaviour.coherentReqDirEventNoPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  coherentReq : e_req.isCoherent
  notDowngrade : ¬e_req.down
  noPerms : b.reqMissingPerms n init e_req

/-- Top Level Def. Prop on a Coherent Request `e_coh_req`, and where will the directory event that gave it cache permissions for `e_coh_req`'s access is. -/
structure Behaviour.coherentReqDirEventHasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  coherentReq : e_req.isCoherent
  notDowngrade : ¬e_req.down
  -- noPerms : b.reqMissingPerms n e_req init
  hasPerms : b.reqHasPerms n init e_req
  immPredEncapDir : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/- Defs describing where a Non-Coherent Weak Read's Directory Event that links the Read's data to the total order of Directory Entry Events. -/

/-- Def. Prop Non-Coherent Weak Read on Vc or SW must have had an immediate bottom predecessor request event that brought the entry state to Vc or SW. -/
structure Behaviour.ncWeakReadVcOrSWDirBefore (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  reqOnVcOrSw : b.stateBefore n (init.stateAt n e_req) e_req = VcEntry n ∨ b.stateBefore n (init.stateAt n e_req) e_req = SWEntry n
  immPredEncapDir : b.reqHasPermsSoDirPred n init e_req


/-- Wrapper Def there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
structure Behaviour.weakReqOnVdSoDirSucc (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  immSuccEncapDir : b.immBottomSuccOnVdEncapCorrDir n init e_req e_dir

/-- Def. Prop Non-Coherent Weak Read on Vd must have an immediate bottom successor request event that will write back the entry to directory or get SW permissions. -/
structure Behaviour.ncWeakReadOrWriteVdDirBefore (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  reqOnVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n
  immSuccEncapDir : b.weakReqOnVdSoDirSucc n init e_req e_dir


/-- Def. Inductive Prop on Non-Coherent Weak Read and where is it's directory event that ties it to the directory entry's total order. -/
inductive Behaviour.dirEventOfNCWeakRead (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| encapDir : b.isReqHasNoPermsSoEncapDir n init e_req e_dir → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderBeforeDir : b.ncWeakReadVcOrSWDirBefore n init e_req e_dir → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderAfterDir : b.ncWeakReadOrWriteVdDirBefore n init e_req e_dir → Behaviour.dirEventOfNCWeakRead b e_req e_dir init


/-- Top level def for a Non-Coherent Weak Read's Directory Event relation. -/
structure Behaviour.ncWeakRead (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqNcWeakRead : e_req.isNcWeakRead
  dirOfNCWR : b.dirEventOfNCWeakRead n e_req e_dir init
  notDowngrade : ¬e_req.down

/-- Def. a Request is made on a state that has coherent permissions, so the directory event linking it to the total order of events at the dir entry is predecessor the request. -/
structure Behaviour.reqHasCoherentPermsSoDirPred (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  hasPerms : b.reqHasPerms n init e_req
  isCoherent : (b.stateBefore n (init.stateAt n e_req) e_req).cache.c
  immPredEncapDir : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/- Defs describing where a Non-Coherent Weak Write's Directory Event that links the Write's data to the total order of Directory Entry Events. -/
inductive Behaviour.dirEventOfNCWeakWrite (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| orderBeforeDir : b.reqHasCoherentPermsSoDirPred n init e_req e_dir  → Behaviour.dirEventOfNCWeakWrite b e_req e_dir init -- [NOTE]: not technically necessary
| orderAfterDir : b.ncWeakReadOrWriteVdDirBefore n init e_req e_dir → Behaviour.dirEventOfNCWeakWrite b e_req e_dir init


/-- Top level def for a Non-Coherent Weak Write's Directory Event relation. -/
structure Behaviour.ncWeakWrite (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqNcWeakWrite : e_req.isNcWeakWrite
  dirOfNCWWOrderAfter : b.dirEventOfNCWeakWrite n e_req e_dir init
  notDowngrade : ¬e_req.down

/-- Top level def for a Non-Coherent Acquire's Directory Event relation. An Acquire always encapsulates a directory event. -/
structure Behaviour.ncAcquire (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  reqNcAcquire : e_req.isAcquire
  -- reqEncapDir : e_req.Encapsulates n e_dir
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
  notDowngrade : ¬e_req.down

/-- Top level def for a Non-Coherent Release's Directory Event relation. -/
structure Behaviour.ncRelease (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  reqNcRelease : e_req.isNCRelease
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
  notDowngrade : ¬e_req.down
  /-
  dirWrite : e_dir.isWrite
  reqEncapDir : e_req.Encapsulates n e_dir-/

-- [NOTE] use `Behaviour.vdCacheEntryWriteBackLater` in the Vd succeeding Dir Events case

lemma List.ordered_mem_impl_ordered_idx {α} [DecidableEq α] {l_head l_tail : List α} {n m : α}
  (l : List α) (hlist : l = l_head ++ l_tail)
  (hn_in_head : n ∈ l_head) (hm_in_tail : m ∈ l_tail) (hl_nodup : l.Nodup) : idxOf n l < idxOf m l  := by
  rw[hlist]
  rw[List.idxOf_append_of_mem]
  have hm_not_in_head : m ∉ l_head := by
    simp[List.Nodup] at hl_nodup
    intro hm_in_head
    rw[hlist] at hl_nodup
    have test := List.nodup_append.mp hl_nodup
    have test1 := test.right.right
    simp[List.Disjoint] at test1
    apply (test1 hm_in_head)
    exact hm_in_tail
  . rw[List.idxOf_append_of_notMem hm_not_in_head]
    have hidx_n_lt_length := List.idxOf_lt_length hn_in_head
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

  have hidxOf_pred_in_l := List.idxOf_lt_length hpred_in_l
  have hidxOf_e_in_l := List.idxOf_lt_length he_in_l

  have hpred_imm_list_pred_e := b.eventsAtEventEntry_imm_pred_equiv n e.struct e.addr
    e_pred e himm_bot_pred.isImmPred.predInB he_in_b
    hpred_at_e_struct hpred_at_e_addr
    he_at_e_struct he_at_e_addr
    himm_bot_pred

  simp[eventsUpToEvent, List.upToEvent]
  apply Eq.symm

  have hidx_pred_one_eq_idx_e := hpred_imm_list_pred_e.noIntermediate
  rw[hidx_pred_one_eq_idx_e]

  have hn_lt_len : List.idxOf e_pred (eventsAtEventEntry n b e) < (eventsAtEventEntry n b e).length := List.idxOf_lt_length hpred_in_l
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

lemma List.take_mem_append_eq_take {α} [DecidableEq α] (n m : α) (l : List α) (hn_in_head : n ∈ l)
  : List.take (List.idxOf n l) l = List.take (List.idxOf n (l ++ [m])) (l ++ [m]) := by
  rw[List.idxOf_append_of_mem hn_in_head]
  rw[List.take_append_eq_append_take]
  have hidxn_lt_len : (List.idxOf n l) < l.length := List.idxOf_lt_length hn_in_head
  have hidxn_le_len := Nat.le_of_lt hidxn_lt_len
  have hidxn_sub_len_eq_zero := Nat.sub_eq_zero_iff_le.mpr hidxn_le_len
  rw[hidxn_sub_len_eq_zero]
  simp

lemma List.take_idxOf_append_eq_list {α} [DecidableEq α] (n : α) (l : List α) (hnodup : (l ++ [n]).Nodup) : List.take (List.idxOf n (l ++ [n])) (l ++ [n]) = l := by
  have hn_not_in_l : n ∉ l := by
    simp[List.nodup_append] at hnodup
    exact hnodup.right
  simp[List.idxOf_append_of_notMem hn_not_in_l]

lemma Behaviour.no_pred_obtains_perms_impl_req_has_no_perms
  (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  (l_preds : List (Event n))
  -- (l_preds : EventPreds n b e_req)
  (hreq_coherent : e_req.isCoherent n)
  -- (hreq_has_perms : b.reqHasPerms n init e_req)
  -- (hl_preds_up_to_req :  l_preds = b.eventsUpToEvent n e_req)
  (hreq_in_b : e_req ∈ b)
  (hreq_is_bottom : b.IsBottomEvent n e_req)
  (hreq_is_ce : e_req.isCacheEvent n)
  (hpreds_at_same_entry : ∀ e ∈ l_preds, b.eventAtEntry n e e_req.struct e_req.addr)
  (hpreds_pred_to_req : ∀ e ∈ l_preds, b.Predecessor n e e_req)
  (hpreds_are_bottom : ∀ e' ∈ l_preds, e'.isBottomAtEntry n b e_req.struct e_req.addr)
  (hentry_preds_in_l_preds : ∀ e ∈ b, b.bottomSameEntry n e e_req → e.OrderedBefore n e_req → e ∈ l_preds)
  (hl_preds_nodup : l_preds.Nodup)
  (hl_preds_ob_sorted : l_preds.Sorted (Event.OrderedBefore n))
  (hax6 : Behaviour.axRequestAccessesDirectory n)
  (hno_pred : ∀ e_predecessor ∈ b, ¬immBottomPredHasNoPermsAndLeavesStateAtLeast n b init e_predecessor e_req)
  : ¬ (Event.req n e_req).MRS ≤ EntryState.cache n (List.stateAfter n (l_preds) (IEntry n)) := by
  induction l_preds using List.reverseRecOn with
  | nil =>
    match he : e_req with
    | .cacheEvent ce =>
      /- For any request, the state it was made on is greater or equal to it's MRS. -/
      match hreq : ce.req with
      | ⟨⟨rw,true,_⟩,_⟩
      | ⟨⟨.r,false,.Weak⟩,{}⟩
      | ⟨⟨.w,false,.Weak⟩,{}⟩
      | ⟨⟨.w,false,.Rel⟩,{}⟩
      | ⟨⟨.r,false,.Acq⟩,{}⟩ =>
        all_goals simp[List.stateAfter, EntryState.cache]; simp[ValidRequest.MRS, Event.req, hreq]; simp[LE.le, State.le, Option.le,]; simp[LT.lt]
    | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce
  | append_singleton l_head e_pred ih =>
    match hreq : e_req with
    | .cacheEvent ce_req =>
      have ih_same_entry_precond : (∀ e ∈ l_head, eventAtEntry n b e (Event.struct n (Event.cacheEvent ce_req)) (Event.addr n (Event.cacheEvent ce_req))) := by
        intro e he_in_l_head
        apply hpreds_at_same_entry
        . case a => simp[he_in_l_head]

      have ih_pred_req_precond : (∀ e ∈ l_head, Predecessor n b e (Event.cacheEvent ce_req)) := by
        intro e he_in_l_head
        apply hpreds_pred_to_req
        . case a => simp[he_in_l_head]

      have ih_pred_bottom_precond : (∀ e' ∈ l_head, Event.isBottomAtEntry n b (Event.struct n (Event.cacheEvent ce_req)) (Event.addr n (Event.cacheEvent ce_req)) e') := by
        intro e he_in_l_head
        apply hpreds_are_bottom
        . case a => simp[he_in_l_head]

      have ih_bottom_same_entry : (∀ e ∈ b,
        bottomSameEntry n b e (Event.cacheEvent ce_req) → Event.OrderedBefore n e (Event.cacheEvent ce_req) → e ∈ l_head) :=
        by
        intro e he_in_b hbottom_same_entry hordered_before
        have h := hentry_preds_in_l_preds e he_in_b hbottom_same_entry hordered_before
        simp[List.mem_append] at h
        cases h
        . case inl hin_head => exact hin_head
        . case inr his_pred => sorry

      have ih_nodup : l_head.Nodup := by sorry

      have ih_sorted : List.Sorted (Event.OrderedBefore n) l_head := by sorry

      have ih_post := ih ih_same_entry_precond ih_pred_req_precond ih_pred_bottom_precond

      /- `ih_post`: the state after `l_head` (the state before `e_pred`) is less than the state required of `e_req` -/

      have h_e_pred_at_e_req := hpreds_at_same_entry e_pred (by simp)

      have h_pred_cannot_get_perms_for_req := hno_pred e_pred h_e_pred_at_e_req.eInB

      have hno_imm_bott_pred_of_p := b.IsImmediateBottomPredSatisfyingProp_neg n h_pred_cannot_get_perms_for_req

      /- use contra; if `e_req` got permissions, then we have a contradiction -/
      by_contra hreq_mrs_le_state_after_pred

      apply h_pred_cannot_get_perms_for_req

      have hpred_imm_bot_pred_to_req : IsImmediateBottomPred n b e_pred (Event.cacheEvent ce_req) := by
        constructor
        . case isImmPred =>
          constructor
          . case bPred =>
            constructor
            . case sameEntry =>
              constructor
              . case sameStruct => simp[Event.sameStructure, h_e_pred_at_e_req.eAtStruct]
              . case sameAddr => simp[Event.sameAddr, h_e_pred_at_e_req.eAtAddr]
            . case isPred => exact (hpreds_pred_to_req e_pred (by simp)).isPred
            . case predInB => simp[h_e_pred_at_e_req.eInB]
            . case succInB => exact hreq_in_b
          . case noIntermediate =>
            simp[NoIntermediatePredecessor]
            intro an_event he_in_b he_is_bottom_same_entry he_btn_pred_and_req
            have hpred_before_event := he_btn_pred_and_req.pred
            have hevent_in_l_preds := hentry_preds_in_l_preds an_event he_in_b he_is_bottom_same_entry he_btn_pred_and_req.succ
            apply Behaviour.contradiction_of_event_after_last_pred
            . case hsorted => exact hl_preds_ob_sorted
            . case hlist => rfl
            . case hl_nodup => exact hl_preds_nodup
            . case he_btn_in_l => exact hevent_in_l_preds
            . case hlast_lt_n => exact hpred_before_event
        . case isBottom => exact hpreds_are_bottom e_pred (by simp) |>.isBottom
        . case isBottomSucc => exact hreq_is_bottom

      constructor
      . case isImmBottomPred => exact hpred_imm_bot_pred_to_req
      . case satisfyP =>
        simp[Event.PropOnEvent]
        -- have hno_imm_bott_pred_of_p := b.IsImmediateBottomPredSatisfyingProp_neg n (hno_pred e_pred h_e_pred_at_e_req.eInB)
        -- simp only [not_and] at hno_imm_bott_pred_of_p
        constructor
        . case missingPerms =>
          -- 3 cases on `e_pred`: in the downgrade case, show contradiction.
          -- apply reqMissingPerms.noPermsForNonNcRelAcqWeakWrite
          sorry
        . case stateAfterAtLeast =>
          simp[reqLeavesStateAtLeast]
          simp[LE.le, State.le]
          apply Or.intro_right
          /- The state after the predecessor `e_pred` is the state before the request `e_req`-/
          apply Behaviour.state_before_is_state_after_pred
          . case h.he_in_b => exact hreq_in_b
          . case h.himm_bot_pred => exact hpred_imm_bot_pred_to_req
    | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce

lemma Behaviour.reqMissingPerms_accesses_dir (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  (hreq_in_b : e_req ∈ b) (hreq_at_cache : e_req.isCacheEvent n)
  (hmissing_perms : b.reqMissingPerms n init e_req) (hax_req_encap_dir : Behaviour.axRequestAccessesDirectory n)
  : ∃ e_dir ∈ b, b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir := by
  /- First, start with the cases of missing permissions (`hmissing_perms`). Consider, ∀ e_req.req that's missing permissions.
  Second, identify the relevant cases where a request encapsulating a directory event (`hax_req_encap_dir`). -/
  cases hax_req_encap_dir
  . case mk hreq_access_dir =>
    have hreq_encap_dir := hreq_access_dir b e_req hreq_in_b init
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
          simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNCRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
            ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_not_nc_rel_acq_ww
          simp[his_nc_rel] at hreq_not_nc_rel_acq_ww
        . case acquire hacq =>
          have his_acq := hacq.isAcquire
          simp[CacheEvent.isAcquire, ValidRequest.isAcquire] at his_acq
          simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNCRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
            ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_not_nc_rel_acq_ww
          simp[his_acq] at hreq_not_nc_rel_acq_ww
        . case weakWrite hww =>
          have his_ww := hww.isWrite
          simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at his_ww
          simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire, Event.isNCRelease, Event.isNcWeakWrite,
            CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
            ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite] at hreq_not_nc_rel_acq_ww
          simp[his_ww] at hreq_not_nc_rel_acq_ww
        . case evictVdWB hvd_wb => simp[Event.down, hvd_wb.isDowngrade] at hreq_not_down
        . case evictSCPutM hput_m => simp[Event.down, hput_m.isDowngrade] at hreq_not_down
        . case evictSCPutS hput_s => simp[Event.down, hput_s.isDowngrade] at hreq_not_down

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
          simp[Event.isNcRelAcq, Event.isAcquire, Event.isNCRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
            ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
          cases hreq_nc_rel_acq
          . case inl his_acq => simp[his_acq] at his_coh
          . case inr his_nc_rel => simp[his_nc_rel] at his_coh
        . case weakWrite hww =>
          have his_weak_write := hww.isWrite
          simp[CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at his_weak_write
          simp[Event.isNcRelAcq, Event.isAcquire, Event.isNCRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
            ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
          simp[his_weak_write] at hreq_nc_rel_acq
        . case weakRead hwr =>
          have his_weak_read := hwr.isRead
          simp[CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at his_weak_read
          simp[Event.isNcRelAcq, Event.isAcquire, Event.isNCRelease, CacheEvent.isAcquire, CacheEvent.isNcRelease,
            ValidRequest.isAcquire, ValidRequest.isNcRelease] at hreq_nc_rel_acq
          simp[his_weak_read] at hreq_nc_rel_acq
        . case evictVdWB hvd_wb => simp[Event.down, hvd_wb.isDowngrade] at hreq_not_down
        . case evictSCPutM hput_m => simp[Event.down, hput_m.isDowngrade] at hreq_not_down
        . case evictSCPutS hput_s => simp[Event.down, hput_s.isDowngrade] at hreq_not_down

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

-- [TODO] constrain goal to say not just `e_req` relates `e_dir`, but either encapsulates if lacking permissions, or a previous one if have perms,
-- of a future one if Weak Non-Coherent on Vd
/-- `Lemma 3.` For each Cache Request Event `e_req`, there exists a unique event `e_dir` relating `e_req` to the total order of events at
`e_req`'s corresonponding Directory entry. -/
lemma Behaviour.exists_e_dir_access_of_e_req (b : Behaviour n) (init : InitialSystemState n)
(e_req : Event n) (he_req_in_b : e_req ∈ b.es) (hreq_not_down : ¬ e_req.down)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n)
(hvd_wb_later : Behaviour.vdCacheEntryWriteBackLater n b e_req init) :
   ∃ e_dir ∈ b.es, e_dir.isDirectoryEvent ∧ b.dirAccessOfRequest n init e_req e_dir
  := by
  have ax6 := hreq_encap_dir.reqAccessDir b e_req he_req_in_b init
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases e_req
  . case cacheEvent ce =>
    match hdown : ce.down with
    | false =>
      match hreq : ce.req with
      | ⟨⟨rw,true,consistency⟩, hvalid_req⟩ =>
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          sorry
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          match ax6 with
          | .coherentRequest hcoh_req =>
            use hcoh_req.reqEncapDir.reqEncapCorrDir.choose
            apply And.intro
            . case h.left => exact hcoh_req.reqEncapDir.reqEncapCorrDir.choose_spec.left
            . case h.right =>
              apply And.intro
              . case left => exact hcoh_req.reqEncapDir.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent.isDir
              . case right =>
                apply dirAccessOfRequest.encapDir
                simp_all only [Bool.not_eq_true]
                have h := hcoh_req.notDowngrade
                apply reqMissingPerms.noPermsForNonNcRelAcqWeakWrite
                -- refine .noPermsForNonNcRelAcqWeakWrite ?_ ?_ ?_
                . case hreq_missing_perms.hreq_not_down =>
                  exact hcoh_req.notDowngrade
                . case hreq_missing_perms.hreq_not_nc_rel_acq_ww =>
                  simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
                    Event.isAcquire, Event.isNCRelease, Event.isNcWeakWrite,
                    CacheEvent.isAcquire, CacheEvent.isNcRelease, CacheEvent.isNcWeakWrite,
                    ValidRequest.isAcquire, ValidRequest.isNcRelease, ValidRequest.isNcWeakWrite,
                    hreq]
                . case hreq_missing_perms.hno_perms =>
                  simp[Behaviour.eventOnStateNoPerms, eventOnStateHasPerms]
                  simp[Event.req]
                  rw [hreq]
                  subst state_req_made_on
                  subst event_req
                  simp [hreq_has_perms]
                . case hencap_dir =>
                  exact hcoh_req.reqEncapDir.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent
          | .nonCoherentRelease hnc_rel =>
            sorry
          | .acquire _ => sorry
          | .weakWrite _ => sorry
          | .weakRead _ => sorry
          | .evictVdWB _ => sorry
          | .evictSCPutM _ => sorry
          | .evictSCPutS _ => sorry
      | ⟨⟨.r,false,.Weak⟩, {}⟩ =>
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          by_cases hnot_on_vd : state_req_made_on ≠ Vd
          . case pos => sorry
          . case neg =>
            /- [NOTE] Use Behaviour.hasPermsNotVd .ncWeakReadHasPermsNotVd
            in Behaviour.dirAccessOfRequest from the Goal to show this case isn't true. -/
            sorry
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          match ax6 with
          | .weakRead hweak_r =>
            use hweak_r.encapDirEvent.reqEncapCorrDir.choose
            apply And.intro
            . case h.left => exact hweak_r.encapDirEvent.reqEncapCorrDir.choose_spec.left
            . case h.right =>
              apply And.intro
              . case left => exact hweak_r.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent.isDir
              . case right =>
                apply dirAccessOfRequest.encapDir
                apply reqMissingPerms.noPermsForNonNcRelAcqWeakWrite
                . case hreq_missing_perms.hreq_not_down =>
                  exact hweak_r.ncWeakReq.notDowngrade
                . case hreq_missing_perms.hreq_not_nc_rel_acq_ww =>
                  simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire,
                    Event.isNCRelease, Event.isNcWeakWrite, hreq]
                . case hreq_missing_perms.hno_perms =>
                  simp[eventOnStateNoPerms]
                  exact hreq_has_perms
                . case hencap_dir =>
                  exact hweak_r.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent
          | .coherentRequest hcoh_req => sorry
          | .nonCoherentRelease hnc_rel => sorry
          | .acquire _ => sorry
          | .weakWrite _ => sorry
          | .evictVdWB _ => sorry
          | .evictSCPutM _ => sorry
          | .evictSCPutS _ => sorry
      | ⟨⟨.r,false,.Acq⟩, {}⟩ =>
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on.c ∧ ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          sorry
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          match ax6 with
          | .acquire hacq =>
            use hacq.encapDirEvent.reqEncapCorrDir.choose
            apply And.intro
            . case h.left => exact hacq.encapDirEvent.reqEncapCorrDir.choose_spec.left
            . case h.right =>
              apply And.intro
              . case left => exact hacq.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent.isDir
              . case right =>
                apply dirAccessOfRequest.encapDir
                apply reqMissingPerms.ncRelAcqWeakWriteNotOnCoherentState
                . case hreq_missing_perms.hreq_not_down =>
                  exact hacq.notDowngrade
                . case hreq_missing_perms.hreq_nc_rel_acq =>
                  simp[Event.isNcRelAcq, Event.isAcquire]
                  simp[hreq]
                . case hreq_missing_perms.hno_perms =>
                  dsimp[acqRelWeakWriteNoPerms, eventOnCoherentState, eventOnStateHasPerms]
                  exact hreq_has_perms
                . case hencap_dir =>
                  exact hacq.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent
          | .weakWrite hweak_r => sorry
          | .coherentRequest hcoh_req => sorry
          | .nonCoherentRelease hnc_rel => sorry
          | .weakRead _ => sorry
          | .evictVdWB _ => sorry
          | .evictSCPutM _ => sorry
          | .evictSCPutS _ => sorry
      | ⟨⟨.w,false,.Weak⟩, {}⟩ =>
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on = SW
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          sorry
        . case neg =>
          /- Show a future event writes back. -/
          sorry
          /-
          match ax6 with
          | .weakWrite hweak_w =>
            use hweak_w.ncWeakReq.encapDirEvent.reqEncapCorrDir.choose
            apply And.intro
            . case h.left => exact hweak_w.ncWeakReq.encapDirEvent.reqEncapCorrDir.choose_spec.left
            . case h.right =>
              apply And.intro
              . case left => exact hweak_w.ncWeakReq.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent.isDir
              . case right =>
                constructor
                intro hmissing_perms
                exact hweak_w.ncWeakReq.encapDirEvent.reqEncapCorrDir.choose_spec.right.reqEncapCorrespondingDirEvent
          | .coherentRequest hcoh_req =>
            have h := hcoh_req.isCoherent
            simp[Event.req, hreq] at h
          | .nonCoherentRelease hnc_rel =>
            have h := hnc_rel.existsDirWb.choose_spec.right.isRelease
            simp[hreq] at h
          | .acquire hacq =>
            have h := hacq.isAcquire
            simp[hreq] at h
          | .weakRead hweak_r =>
            absurd hweak_r.isRead
            simp[Request.isRead, hreq]
          | .evictVdWB he_vd =>
            have h := he_vd.isDowngrade
            simp[hdown] at h
          | .evictSCPutM hputm =>
            have h := hputm.isPutM
            simp[hreq] at h
          | .evictSCPutS hputs =>
            have h := hputs.isPutS
            simp[hreq] at h
          -/
      | ⟨⟨.w,false,.Rel⟩, {}⟩ =>
        let event_req := (Event.cacheEvent ce)
        let state_req_made_on := b.stateBefore n (init.stateAt n event_req) event_req |>.cache
        by_cases hreq_has_perms : state_req_made_on.c ∧ ce.req.MRS ≤ state_req_made_on
        . case pos =>
          /- Request has permissions, must exist predecessor that obtained permissions previously. -/
          sorry
        . case neg =>
          /- Request has no permissions, so encapsulates a directory event to access the Directory. -/
          match ax6 with
          | .nonCoherentRelease hnc_rel =>
            use hnc_rel.existsDirWb.choose
            -- use hnc_rel.choose_spec.right.encapsDirWB.reqEncapCorrespondingDirEvent
            apply And.intro
            . case h.left => exact hnc_rel.existsDirWb.choose_spec.right.encapsDirWB.reqEncapCorrespondingDirEvent.dirInB
            . case h.right =>
              apply And.intro
              . case left => exact hnc_rel.existsDirWb.choose_spec.right.encapsDirWB.reqEncapCorrespondingDirEvent.isDir
              . case right =>
                apply dirAccessOfRequest.encapDir
                apply reqMissingPerms.ncRelAcqWeakWriteNotOnCoherentState
                . case hreq_missing_perms.hreq_not_down => exact hnc_rel.notDowngrade
                . case hreq_missing_perms.hreq_nc_rel_acq =>
                  simp[Event.isNcRelAcq, Event.isNCRelease]
                  simp[hreq]
                . case hreq_missing_perms.hno_perms =>
                  dsimp[acqRelWeakWriteNoPerms]
                  exact hreq_has_perms
                . case hencap_dir =>
                  exact hnc_rel.existsDirWb.choose_spec.right.encapsDirWB.reqEncapCorrespondingDirEvent
          | .weakWrite hweak_r =>
            have h := hweak_r.ncWeakReq.isWeak; simp[hreq] at h
          | .coherentRequest hcoh_req =>
            have h := hcoh_req.isCoherent
            simp[Event.req, hreq] at h
          | .acquire hacq =>
            have h := hacq.isAcquire
            simp[hreq] at h
          | .weakRead hweak_r =>
            have h := hweak_r.ncWeakReq.isWeak
            simp[hreq] at h
          | .evictVdWB he_vd =>
            have h := he_vd.isVdWriteBack
            simp[hreq] at h
          | .evictSCPutM hputm =>
            have h := hputm.isPutM
            simp[hreq] at h
          | .evictSCPutS hputs =>
            have h := hputs.isPutS
            simp[hreq] at h
    | true =>
      match ax6 with
      | .evictVdWB he_vd =>
        use he_vd.encapWBDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left =>
          exact he_vd.encapWBDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right =>
          apply And.intro
          . case left =>
            exact he_vd.encapWBDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent.isDir
          . case right =>
            apply dirAccessOfRequest.encapDir
            apply reqMissingPerms.downgrade
            . case hreq_missing_perms.hreq_is_down => exact he_vd.isDowngrade
            . case hreq_missing_perms.hreq_on_mrs_state => exact he_vd.madeOnMrs
            . case hencap_dir => exact he_vd.encapWBDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
      | .evictSCPutM hputm =>
        use hputm.encapPutMDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left =>
          exact hputm.encapPutMDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right =>
          apply And.intro
          . case left =>
            exact hputm.encapPutMDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent.isDir
          . case right =>
            apply dirAccessOfRequest.encapDir
            apply reqMissingPerms.downgrade
            . case hreq_missing_perms.hreq_is_down => exact hputm.isDowngrade
            . case hreq_missing_perms.hreq_on_mrs_state => exact hputm.madeOnMrs
            . case hencap_dir => exact hputm.encapPutMDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
      | .evictSCPutS hputs =>
        use hputs.encapPutSDirEvent.evictEncapCorrDir.choose
        apply And.intro
        . case h.left =>
          exact hputs.encapPutSDirEvent.evictEncapCorrDir.choose_spec.left
        . case h.right =>
          apply And.intro
          . case left =>
            exact hputs.encapPutSDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent.isDir
          . case right =>
            apply dirAccessOfRequest.encapDir
            apply reqMissingPerms.downgrade
            . case hreq_missing_perms.hreq_is_down => exact hputs.isDowngrade
            . case hreq_missing_perms.hreq_on_mrs_state => exact hputs.madeOnMrs
            . case hencap_dir => exact hputs.encapPutSDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
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
  . case directoryEvent _ => simp at ax6

/-- Def. Prop constraints for Def 2.37 case where the request has coherent permissions and is then defined as it's own linearization event. -/
structure Behaviour.requestWithCoherentPermsLinearizes (b : Behaviour n) (e_req e_lin : Event n) (init : InitialSystemState n) : Prop where
  reqHasCoherentPerms : b.eventOnCoherentStateAtLeastMRS n e_req init
  reqIsLin : e_lin = e_req

/-- Def. Wrapper structure : Prop. for Def 2.37-/
structure Behaviour.requestWithCoherentPermLin : Prop where
  linearizingRequest : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b.es, ∃ e_lin : Event n, b.requestWithCoherentPermsLinearizes n e_req e_lin init

/-- Def. 2.37. Linearization Event Corresponding to a Request Event. If a Request Event `e_req` is made on a `Coherent` state with sufficient
permissions, the linearization event `e_lin` of `e_req` is `e_req`. Otherwise, `e_lin` is the Directory Event `e_dir` stated by Lemma 3. -/
-- [TODO]: add structure defining what each case entails.
inductive Behaviour.linearizationEventOfRequest
| requestLin : Behaviour.requestWithCoherentPermLin n → Behaviour.linearizationEventOfRequest
| dirLin : /- Structure with `Behaviour.exists_e_dir_relating_e_req` goes here when it's ready. -/ Behaviour.linearizationEventOfRequest
