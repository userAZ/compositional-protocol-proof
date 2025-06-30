import CompositionalProtocolProof.Behaviours
import Canonical

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

def Event.dirEventOfReqEvent (e_dir e_req : Event n) : Prop := match e_dir, e_req with
| .directoryEvent de, .cacheEvent ce => de.eReq = ce
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
structure Behaviour.requestCoherentNoPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  isCoherent : e_req.req.val.coherent
  noPerms : (b.stateBefore n (init.stateAt n e_req) e_req).cache < e_req.req.MRS
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
  notCoherent : ¬ e_req.Coherent
  isRelease : e_req.req.val.consistency = .Rel
  encapsDirWB : b.reqEncapsulatesDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req) e_dir_wb
  encapGetVFromI : b.ncReleaseOnI n (Event.cacheEvent e_req) e_dir_wb init

structure Behaviour.nonCoherentRelease (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  notDowngrade : ¬ e_req.down
  existsDirWb : ∃ e_dir_wb ∈ b.es, b.nonCoherentReleaseEncapDirEvents n e_req e_dir_wb init

/- Def: Props for a non-coherent Acquire encapsulating a Directory Event. -/
structure Behaviour.acquireEncapDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  notDowngrade : ¬ e_req.down
  isAcquire : e_req.req.val.consistency = .Acq
  madeOnNCStates : let made_on_state := b.stateBefore n (init.stateAt n (Event.cacheEvent e_req)) (Event.cacheEvent e_req)
    made_on_state = VdEntry n ∨ made_on_state = VcEntry n ∨ made_on_state = IEntry n
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

/-- Def: Props stating when a non-coherent weak operation (read/write) encapsulates a Directory Event -/
structure Behaviour.ncWeakRequestEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  notCoherent : ¬ e_req.Coherent
  isWeak : e_req.req.val.consistency = .Weak
  madeOnIState : b.stateBefore n (init.stateAt n (Event.cacheEvent e_req)) (Event.cacheEvent e_req) = IEntry n
  notDowngrade : ¬ e_req.down

/-- Prop: NC Weak Read encaps a dir event -/
structure Behaviour.ncWeakReadEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  ncWeakReq : b.ncWeakRequestEncapDirEvent n init e_req
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)
  isRead : e_req.req.val.isRead

/-- Prop: NC Weak Read encaps a dir event -/
structure Behaviour.ncWeakWriteEncapDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : CacheEvent n) : Prop where
  ncWeakReq : b.ncWeakRequestEncapDirEvent n init e_req
  encapDirEvent : b.reqEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) false (Event.cacheEvent e_req) -- [NOTE] One of two places where `rel_wb` is false
  isWrite : e_req.req.val.isWrite

def Behaviour.eventOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache = e_req.req.MRS

/-- Def Props stating when an Evicting Weak Non-Coherent Write accesses the Directory -/
structure Behaviour.evictVdWBEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isDowngrade : e_req.down
  isVdWriteBack : e_req.req.val = ⟨.w, false, .Weak⟩
  mrsVdState : e_req.req.MRS = Vd
  madeOnMrs : b.eventOnMRSState n init (Event.cacheEvent e_req)
  encapWBDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

structure Behaviour.evictSCPutMEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isDowngrade : e_req.down
  isPutM : e_req.req.val = ⟨.w, true, .SC⟩
  mrsSWState : e_req.req.MRS = SW
  madeOnMrs : b.eventOnMRSState n init (Event.cacheEvent e_req)
  encapPutMDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

structure Behaviour.evictSCPutSEncapsulatesDirEvent (b : Behaviour n) (e_req : CacheEvent n) (init : InitialSystemState n) : Prop where
  isDowngrade : e_req.down
  isPutS : e_req.req.val = ⟨.r, true, .SC⟩
  mrsMRState : e_req.req.MRS = MR
  madeOnMrs : b.eventOnMRSState n init (Event.cacheEvent e_req)
  encapPutSDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n (Event.cacheEvent e_req)) true (Event.cacheEvent e_req)

/-- Axiom 6: When a Request Event encapsulates Directory Events to access/request from the Directory. -/
inductive Behaviour.requestAccessesDirectory (b : Behaviour n) (ce : CacheEvent n) (init : InitialSystemState n) : Prop
| coherentRequest : b.requestCoherentNoPerms n (Event.cacheEvent ce) init → Behaviour.requestAccessesDirectory b ce init
| nonCoherentRelease : b.nonCoherentRelease n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: have a struct and fields for OnI and OnV
| acquire : b.acquireEncapDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : Not on MR
| weakWrite : b.ncWeakWriteEncapDirEvent n init ce → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| weakRead : b.ncWeakReadEncapDirEvent n init ce → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| evictVdWB : b.evictVdWBEncapsulatesDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutM : b.evictSCPutMEncapsulatesDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutS : b.evictSCPutSEncapsulatesDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}

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

/-- Def. Prop on a Request Event `e_req`.
The state `e_req` is made on is not sufficient to be able to complete the request in cache.
For Acq, Non-Coherent Rel, and Weak Writes, this means the state it's made on is lower than it's `Minimum Required State (MRS)` AND is not coherent.
For other requests, SC, Coherent, and Weak Reads, this means it's state it's made on is lower that it's `MRS`.
In the case of Weak Reads, the state it's made on excludes `Vd`. -/
inductive Behaviour.reqMissingPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop
| downgrade : e_req.down → b.eventOnMRSState n init e_req → Behaviour.reqMissingPerms b init e_req
| noPermsForNonNcRelAcqWeakWrite : ¬ e_req.down → e_req.notNcRelAcqWeakWrite n → b.eventOnStateNoPerms n init e_req → Behaviour.reqMissingPerms b init e_req
| ncRelAcqWeakWriteNotOnCoherentState : ¬ e_req.down → e_req.isNcRelAcq → b.acqRelWeakWriteNoPerms n init e_req → Behaviour.reqMissingPerms b init e_req

structure Behaviour.reqEncapDirHasNoPermsLeavesStateAtLeast (b : Behaviour n) (init : InitialSystemState n) (state : State) (e_req e_dir : Event n) : Prop where
  missingPerms : b.reqMissingPerms n init e_req
  stateAfterAtLeast : b.reqLeavesStateAtLeast n e_req init state
  encapDir : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir

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

structure Behaviour.isReqHasPermsNotVd (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  hasPerms : b.hasPerms n init e_req
  onCoherentStateOrVc : b.stateReqMadeOn n init e_req ≠ Vd

/-- Wrapper structure Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
inductive Behaviour.reqHasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop
| hasPerms : e_req.isCoherent → b.hasPerms n init e_req → Behaviour.reqHasPerms b init e_req
| ncRelAcqWeakWriteHasCoherentPerms : e_req.isNcRelAcqWeakWrite → b.isReqHasPermsOnCoherentState n init e_req → Behaviour.reqHasPerms b init e_req
| ncWeakReadHasPermsNotVd : e_req.isNcWeakRead → b.isReqHasPermsNotVd n init e_req → Behaviour.reqHasPerms b init e_req

/-- Def. Structure stating a request event `e_req` has insufficient permissions, so it encapsulates directory event. -/
structure Behaviour.inreqHasPermsSoEncapDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  noPerms : b.reqMissingPerms n init e_req
  reqEncapDir : e_req.Encapsulates n e_dir

/-- Alternate Def of a request event `e_req` that has insufficient permissions, so it encapsulates a directory event. -/
def Behaviour.inreqHasPermsSoEncapDir' (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  b.reqMissingPerms n init e_req → ∃ e_dir ∈ b.es, e_dir.isDirectoryEvent ∧ e_req.Encapsulates n e_dir

def Behaviour.predWithCorrespondingDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  (b.reqWithCorrespondDirLeavesStateAtLeast n e_pred init (b.stateBefore n (init.stateAt n e_req) e_req |>.cache))

def Behaviour.immBottomPredEncapCorrDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predWithCorrespondingDirLeavesStateAtLeastReq n · e_req init)

def Behaviour.predHasNoPermsAndEncapDirAndLeavesStateAtLeastReq (b : Behaviour n) (init : InitialSystemState n) (e_pred e_dir e_req : Event n) : Prop :=
  b.reqEncapDirHasNoPermsLeavesStateAtLeast n init (b.stateBefore n (init.stateAt n e_req) e_req |>.cache) e_pred e_dir

def Behaviour.immBottomPredEncapDirAndHasNoPermsAndLeavesStateAtLeast (b : Behaviour n) (init : InitialSystemState n) (e_pred e_dir e_req : Event n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predHasNoPermsAndEncapDirAndLeavesStateAtLeastReq n init · e_dir e_req)

def Behaviour.reqHasPermsSoDirPred (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop :=
  ∃ e_pred ∈ b.es, b.immBottomPredEncapDirAndHasNoPermsAndLeavesStateAtLeast n init e_pred e_dir e_req

/-- Alternate Def of a request event `e_req` that has insufficient permissions, so it encapsulates a directory event. -/
def Behaviour.reqHasPermsSoDirPred' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.reqHasPerms n init e_req → ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/-- Inductive Prop. State where is the directory event that obtains permissions for a Coherent Request. -/
inductive Behaviour.dirEventOfCoherentReq (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| encapDir : b.inreqHasPermsSoEncapDir n init e_req e_dir → Behaviour.dirEventOfCoherentReq b e_req e_dir init
| orderBeforeDir : b.reqHasPermsSoDirPred n init e_req e_dir → Behaviour.dirEventOfCoherentReq b e_req e_dir init -- [NOTE]: not technically necessary

structure Behaviour.ncWeakReqOnVd (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  weakReq : e_req.isNcWeak
  reqOnOrAfterVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n ∨ b.stateAfter n (init.stateAt n e_req) e_req = VdEntry n

/-- Succeeding Request Event on Vd that accesses the Directory -/
structure Behaviour.reqOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  stateBeforeAsVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n
  -- [NOTE]: Remebmer to use Axiom 6 to solve this.
  encapCorresponding : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir

def Behaviour.succOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_succ e_dir : Event n) : Prop :=
  (b.reqOnVdWithCorrespondingDir n init e_succ e_dir)

/-- Def. Prop. there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
def Behaviour.immBottomSuccOnVdEncapCorrDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop :=
  ∃ e_succ ∈ b.es, b.ImmediateBottomSuccSatisfyingProp n e_req e_succ (b.succOnVdWithCorrespondingDir n init · e_dir)

/-- Trying something new: separately state the cases of where -/
inductive Behaviour.dirAccessOfRequest (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop
| encapDir : b.reqMissingPerms n init e_req → b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir → Behaviour.dirAccessOfRequest b init e_req e_dir
| orderBeforeDir : b.reqHasPerms n init e_req → b.reqHasPermsSoDirPred n init e_req e_dir → Behaviour.dirAccessOfRequest b init e_req e_dir
| orderAfterDir : b.ncWeakReqOnVd n init e_req → b.immBottomSuccOnVdEncapCorrDir n init e_req e_dir → Behaviour.dirAccessOfRequest b init e_req e_dir

/-- Alternate Def of Inductive Prop. State where is the directory event that obtains permissions for a Coherent Request. -/
structure Behaviour.dirEventOfCoherentReq' (b : Behaviour n)  (e_req : Event n) (init : InitialSystemState n) : Prop where
  encapDir : b.inreqHasPermsSoEncapDir' n init e_req
  orderBeforeDir : b.reqHasPermsSoDirPred' n e_req init

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

/-- Alternate top level def, for struct. -/
def Behaviour.cohReqDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isCoherent → ¬e_req.down → b.dirEventOfCoherentReq' n e_req init

/- Defs describing where a Non-Coherent Weak Read's Directory Event that links the Read's data to the total order of Directory Entry Events. -/

/-- Def. Prop Non-Coherent Weak Read on Vc or SW must have had an immediate bottom predecessor request event that brought the entry state to Vc or SW. -/
structure Behaviour.ncWeakReadVcOrSWDirBefore (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqOnVcOrSw : b.stateBefore n (init.stateAt n e_req) e_req = VcEntry n ∨ b.stateBefore n (init.stateAt n e_req) e_req = SWEntry n
  immPredEncapDir : b.reqHasPermsSoDirPred n init e_req e_dir

/-- Alternate def (for Lemma 3). for Non-Coherent Weak Read on Vc or SW must have had an immediate bottom predecessor request event that brought the entry state to Vc or SW.-/
def Behaviour.ncWeakReadVcOrSWDirBefore' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.stateBefore n (init.stateAt n e_req) e_req = VcEntry n ∨ b.stateBefore n (init.stateAt n e_req) e_req = SWEntry n
  → b.reqHasPermsSoDirPred' n e_req init

/-- Wrapper Def there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
structure Behaviour.weakReqOnVdSoDirSucc (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  immSuccEncapDir : ∃ e_succ ∈ b.es, b.immBottomSuccOnVdEncapCorrDir n init e_req e_succ

/-- Def. Prop Non-Coherent Weak Read on Vd must have an immediate bottom successor request event that will write back the entry to directory or get SW permissions. -/
structure Behaviour.ncWeakReadOrWriteVdDirBefore (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqOnVd : b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n
  immSuccEncapDir : b.weakReqOnVdSoDirSucc n e_req init

def Behaviour.ncWeakReadOrWriteVdDirBefore' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.stateBefore n (init.stateAt n e_req) e_req = VdEntry n → b.weakReqOnVdSoDirSucc n e_req init

/-- Def. Inductive Prop on Non-Coherent Weak Read and where is it's directory event that ties it to the directory entry's total order. -/
inductive Behaviour.dirEventOfNCWeakRead (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| encapDir : b.inreqHasPermsSoEncapDir n init e_req e_dir → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderBeforeDir : b.ncWeakReadVcOrSWDirBefore n e_req e_dir init → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderAfterDir : b.ncWeakReadOrWriteVdDirBefore n e_req e_dir init → Behaviour.dirEventOfNCWeakRead b e_req e_dir init

/-- Alternate def for Lemma 3 -/
structure Behaviour.dirEventOfNCWeakRead' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  encapDir : b.inreqHasPermsSoEncapDir' n init e_req
  orderBeforeDir : b.ncWeakReadVcOrSWDirBefore' n e_req init
  orderAfterDir : b.ncWeakReadOrWriteVdDirBefore' n e_req init

/-- Top level def for a Non-Coherent Weak Read's Directory Event relation. -/
structure Behaviour.ncWeakRead (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqNcWeakRead : e_req.isNcWeakRead
  dirOfNCWR : b.dirEventOfNCWeakRead n e_req e_dir init
  notDowngrade : ¬e_req.down

/-- Alternate top level def, for struct. -/
def Behaviour.ncWeakReadDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isNcWeakRead → ¬e_req.down → b.dirEventOfNCWeakRead' n e_req init

/-- Def. a Request is made on a state that has coherent permissions, so the directory event linking it to the total order of events at the dir entry is predecessor the request. -/
structure Behaviour.reqHasCoherentPermsSoDirPred (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  hasPerms : b.reqHasPerms n init e_req
  isCoherent : (b.stateBefore n (init.stateAt n e_req) e_req).cache.c
  immPredEncapDir : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/-- Alternate def for Lemma 3 -/
def Behaviour.reqHasCoherentPermsSoDirPred' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  (hasPerms : b.reqHasPerms n init e_req) → (isCoherent : (b.stateBefore n (init.stateAt n e_req) e_req).cache.c) →
  ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/- Defs describing where a Non-Coherent Weak Write's Directory Event that links the Write's data to the total order of Directory Entry Events. -/
inductive Behaviour.dirEventOfNCWeakWrite (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| orderBeforeDir : b.reqHasCoherentPermsSoDirPred n e_req e_dir init → Behaviour.dirEventOfNCWeakWrite b e_req e_dir init -- [NOTE]: not technically necessary
| orderAfterDir : b.ncWeakReadOrWriteVdDirBefore n e_req e_dir init → Behaviour.dirEventOfNCWeakWrite b e_req e_dir init

/-- Alternate def for: describing where a Non-Coherent Weak Write's Directory Event that links the Write's data to the total order of Directory Entry Events. -/
structure Behaviour.dirEventOfNCWeakWrite' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  orderBeforeDir : b.reqHasCoherentPermsSoDirPred' n e_req init
  orderAfterDir : b.ncWeakReadOrWriteVdDirBefore' n e_req init

/-- Top level def for a Non-Coherent Weak Write's Directory Event relation. -/
structure Behaviour.ncWeakWrite (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqNcWeakWrite : e_req.isNcWeakWrite
  dirOfNCWWOrderAfter : b.dirEventOfNCWeakWrite n e_req e_dir init
  notDowngrade : ¬e_req.down

/-- Alternate top level def, for struct. -/
def Behaviour.ncWeakWriteDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isNcWeakWrite → ¬e_req.down → b.dirEventOfNCWeakWrite' n e_req init

/-- Top level def for a Non-Coherent Acquire's Directory Event relation. An Acquire always encapsulates a directory event. -/
structure Behaviour.ncAcquire (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  reqNcAcquire : e_req.isAcquire
  -- reqEncapDir : e_req.Encapsulates n e_dir
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
  notDowngrade : ¬e_req.down

/-- Alternate top level def, for struct. -/
def Behaviour.ncAcqDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isAcquire → ¬e_req.down → b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

/-- Top level def for a Non-Coherent Release's Directory Event relation. -/
structure Behaviour.ncRelease (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  reqNcRelease : e_req.isNCRelease
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
  notDowngrade : ¬e_req.down
  /-
  dirWrite : e_dir.isWrite
  reqEncapDir : e_req.Encapsulates n e_dir-/

/- Alternate top level def, for struct. -/
/- remove old relations
def Behaviour.ncRelDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isNCRelease → ¬e_req.down →
    b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
-/

/- Lemma 3 Goal. -/
/- remove old relations
inductive Behaviour.reqDirPrecondition (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop
| coherentReqNoPerms : b.coherentReqDirEventNoPerms n init e_req → Behaviour.reqDirPrecondition b e_req init
| coherentReqHasPerms : b.coherentReqDirEventHasPerms n init e_req → Behaviour.reqDirPrecondition b e_req init
| ncWeakRead : (∃ e_dir ∈ b.es, b.ncWeakRead n e_req e_dir init) → Behaviour.reqDirPrecondition b e_req init
| ncAcq : (b.ncAcquire n e_req init) → Behaviour.reqDirPrecondition b e_req init
| ncWeakWrite : (∃ e_dir ∈ b.es, b.ncWeakWrite n e_req e_dir init) → Behaviour.reqDirPrecondition b e_req init
| ncRel : (b.ncRelease n e_req init) → Behaviour.reqDirPrecondition b e_req init
-/

-- [TODO] Put axioms into Behaviour.
/- remove old relations
structure Behaviour.reqDirRelation' (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  cohReqRelation : b.cohReqDirRelation n e_req init
  ncWeakReadDirRelation : b.ncWeakReadDirRelation n e_req init
  ncWeakWriteDirRelation : b.ncWeakWriteDirRelation n e_req init
  ncRelDirRelation : b.ncRelDirRelation n e_req init
  ncAcqDirRelation : b.ncAcqDirRelation n e_req init
-/

-- [NOTE] use `Behaviour.vdCacheEntryWriteBackLater` in the Vd succeeding Dir Events case

-- [TODO] Add Lemma (or Def) to state there exists a previous event `e_pred` before Event `e`, that sets the state that `e` is made on.
lemma State.lt_coherence_true_false_is_false (s₁ s₂ : State)
(hs₁_coh : s₁.c) (hs₂_coh : ¬ s₂.c) : ¬ s₁ ≤ s₂ := by
  match hs₁ : s₁, hs₂ : s₂ with
  | ⟨perm₁, true⟩, ⟨perm₂, false⟩ =>
    match perm₁, perm₂ with
    | some .wr, some .wr => decide
    | some .r, some .wr => decide
    | some .wr, some .r => decide
    | some .r, some .r => decide
    | none, some .r => decide
    | some .r, none => decide
    | none, some .wr => decide
    | some .wr, none => decide
    | none, none => decide
  | ⟨perm₁, false⟩, _ => simp at hs₁_coh
  | _, ⟨perm₂, true⟩ => simp at hs₂_coh

/-- `Helper Lemma 1` in Lemma 3's re-write -/
lemma Behaviour.exists_predecessor_setting_state''
  (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  (hreq_not_downgrade : ¬ e_req.down)
  (hhave_perms : reqHasPerms n b init e_req)
  (hinit_i : (init.stateAt n e_req).cache = I)
  (hcoherent_perms : (b.stateBefore n (init.stateAt n e_req) e_req).cache ≠ Vd)
  (hax6 : Behaviour.axRequestAccessesDirectory n)
  (hreq_is_ce : e_req.isCacheEvent n)
  :
  ∃ e_dir ∈ b.es, e_dir.isDirectoryEvent ∧ b.dirAccessOfRequest n init e_req e_dir
  := by
  -- by_contra hno_imm_pred_getting_state
  /- first show there's a predecessor `e_pred`, that produces state `s` that `e_req` is made on.
  We know `s` is at least `e_req.MRS` -/
  -- have hmrs_le_s := hhave_perms.hasPerms
  -- simp[hasPerms] at hmrs_le_s
  /- By cases on `e_req.MRS`, we know `s` is `≥` a State that isn't `I`. -/
  match he : e_req with
  | .cacheEvent ce =>
    by_cases hcoherent : (Event.cacheEvent ce).isCoherent
    . case pos =>
      -- have hreq_has_perms := hhave_perms.hasPerms hcoherent

      let state_req_made_on := b.stateBefore n (init.stateAt n e_req) e_req |>.cache

      /- For any request, the state it was made on is greater or equal to it's MRS. -/
      match hreq : ce.req with
      | ⟨⟨rw,true,_⟩,_⟩ =>
        match hstate : b.stateBefore n (init.stateAt n e_req) e_req |>.cache with
        | ⟨_,true⟩ =>
          -- simp[hasPerms, Event.req, ValidRequest.MRS, hreq, hstate] at hreq_has_perms
          -- simp[stateBefore] at hreq_has_perms
          -- simp[List.stateAtE] at hreq_has_perms
          sorry
        | ⟨_,false⟩ =>
          -- not possible
          rw[he] at hstate
          -- simp[hasPerms, Event.req, ValidRequest.MRS, hreq, hstate] at hreq_has_perms
          have hmade_on_state_non_coherent : ¬ (b.stateBefore n (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce) |>.cache.c) := by
            simp
            rw[hstate]
          have hreq_mrs_coherent : ce.req.MRS.c := by simp[ValidRequest.MRS, hreq]
          exfalso
          apply State.lt_coherence_true_false_is_false
            ce.req.MRS (b.stateBefore n (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce) |>.cache)
            hreq_mrs_coherent hmade_on_state_non_coherent
          -- simp[hasPerms, Event.req] at hreq_has_perms
          -- exact hreq_has_perms
          sorry

      | ⟨⟨.r,false,.Weak⟩,{}⟩ => simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq] at hcoherent
      | ⟨⟨.w,false,.Weak⟩,{}⟩ => simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq] at hcoherent
      | ⟨⟨.w,false,.Rel⟩,{}⟩ =>  simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq] at hcoherent
      | ⟨⟨.r,false,.Acq⟩,{}⟩ =>  simp[Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent, hreq] at hcoherent
      /-
      -- By reqHasPerms, we know what S is.
      by_cases hmrs : e_req.req.MRS.p = none
      . case pos =>
        simp[Event.req] at hmrs
        simp[he] at hmrs
        simp[ValidRequest.MRS] at hmrs
        split at hmrs
        case h_1 => simp[ReadWrite.toPerms] at hmrs
        case h_2 => simp at hmrs
        case h_3 => simp at hmrs
        case h_4 => simp at hmrs
      . case neg =>-/
        /- MRS isn't I, and `MRS ≤ s`, so `s` is set by a corresponding `e_pred`.
        Now `e_pred` either encapsulates a Directory Event `e_dir`, or doesn't.
        If it doesn't, then `e_pred` has an `e_pred'`. -/
        /- show there's a predecessor somehow? use def of stateBefore? -/
    . case neg => sorry
  | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce
  -- cases (b.stateBefore n e_req (init.stateAt n e_req)).cache
  /-
  have h : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init := by
    by_cases hexists_req_pred : ∃ e_pred' ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred' e_req init
    . case pos => exact hexists_req_pred
    . case neg =>
      --
      sorry-/

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
                . case a.a =>
                  exact hcoh_req.notDowngrade
                . case a.a =>
                  simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite,
                    Event.isAcquire, Event.isNCRelease, Event.isNcWeakWrite, hreq]
                . case a.a =>
                  simp[Behaviour.eventOnStateNoPerms, eventOnStateHasPerms]
                  simp[Event.req]
                  rw [hreq]
                  subst state_req_made_on
                  subst event_req
                  simp [hreq_has_perms]
                . case a =>
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
                . case a.a =>
                  exact hweak_r.ncWeakReq.notDowngrade
                . case a.a =>
                  simp[Event.notNcRelAcqWeakWrite, Event.isNcRelAcqWeakWrite, Event.isAcquire,
                    Event.isNCRelease, Event.isNcWeakWrite, hreq]
                . case a.a =>
                  simp[eventOnStateNoPerms]
                  exact hreq_has_perms
                . case a =>
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
                . case a.a =>
                  exact hacq.notDowngrade
                . case a.a =>
                  simp[Event.isNcRelAcq, Event.isAcquire]
                  simp[hreq]
                . case a.a =>
                  dsimp[acqRelWeakWriteNoPerms, eventOnCoherentState, eventOnStateHasPerms]
                  exact hreq_has_perms
                . case a =>
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
                . case a.a => exact hnc_rel.notDowngrade
                . case a.a =>
                  simp[Event.isNcRelAcq, Event.isNCRelease]
                  simp[hreq]
                . case a.a =>
                  dsimp[acqRelWeakWriteNoPerms]
                  exact hreq_has_perms
                . case a =>
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
            . case a.a => exact he_vd.isDowngrade
            . case a.a => exact he_vd.madeOnMrs
            . case a => exact he_vd.encapWBDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
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
            . case a.a => exact hputm.isDowngrade
            . case a.a => exact hputm.madeOnMrs
            . case a => exact hputm.encapPutMDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
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
            . case a.a => exact hputs.isDowngrade
            . case a.a => exact hputs.madeOnMrs
            . case a => exact hputs.encapPutSDirEvent.evictEncapCorrDir.choose_spec.right.evictEncapCorrespondingDirEvent
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
