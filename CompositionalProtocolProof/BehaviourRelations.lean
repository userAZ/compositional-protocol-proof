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

noncomputable def Behaviour.reqToDirOfRequestEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : ValidRequest :=
  let state_before := b.stateBefore n e_req init
  e_req.reqToDirOfRequestEvent n state_before.cache

/-- Axiom 3. The Request field of a Directory Event corresponding to a Request Event (Cache Event). -/
structure Behaviour.requestDirectoryEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEvent : e_dir.isDirEventOfReqEvent n e_req
  sameAddr : e_req.addr = e_dir.addr
  dirReq :  e_dir.req = b.reqToDirOfRequestEvent n e_req init -- from analysis on e_req and the state it's made on
  dirState : e_dir.isDirEventOfDirState n (b.stateAfter n e_dir init).directory

def Event.dirEventOfReqEvent (e_dir e_req : Event n) : Prop := match e_dir, e_req with
| .directoryEvent de, .cacheEvent ce => de.eReq = ce
| _, _ => false

structure Behaviour.cacheEncapsulatesCorrespondingDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapDir : e_req.Encapsulates n e_dir
  dirCorresponds : b.requestDirectoryEvent n e_req e_dir init
  dirOfReq : e_dir.dirEventOfReqEvent n e_req
  dirInB : e_dir ∈ b.es
  reqInB : e_req ∈ b.es

structure Behaviour.cacheEncapCorrespondingDirEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : Prop where
  cacheDirEvent : ∃ e_dir ∈ b.es, b.cacheEncapsulatesCorrespondingDirEvent n e_req e_dir init

structure Behaviour.reqEncapsulatesDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  reqEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n e_req e_dir init
  notDowngrade : ¬ e_dir.down

structure Behaviour.reqEncapCorrespondingDirEvent (b : Behaviour n) (e_req : Event n) (init : EntryState n) : Prop where
  reqEncapCorrDir : ∃ e_dir ∈ b.es, b.reqEncapsulatesDirEvent n e_req e_dir init

structure Behaviour.evictEncapsulatesCorrespondingDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : EntryState n) : Prop where
  evictEncapCorrespondingDirEvent : b.cacheEncapsulatesCorrespondingDirEvent n e_req e_dir init
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
inductive Behaviour.requestAccessesDirectory (b : Behaviour n) (ce : CacheEvent n) (init : InitialSystemState n) : Prop
| coherentRequest : b.requestCoherentNoPerms n (Event.cacheEvent ce) init → Behaviour.requestAccessesDirectory b ce init
| nonCoherentRelease : b.nonCoherentRelease n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: have a struct and fields for OnI and OnV
| acquire : b.acquireEncapDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : Not on MR
| weakWrite : b.ncWeakRequestEncapDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| weakRead : b.ncWeakRequestEncapDirEvent n ce init → Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
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
  vdStateAfterEvent : b.stateAfter n e (init.stateAt n e) = VdEntry n
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
  atPrevOwner : e_fwd_down.downgradeAtPrevOwner n (b.stateBefore n e_dir (init.stateAt n e_dir)).directory
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
  reqDirOnSW   : b.stateBefore n e_dir (init.stateAt n e_dir) = SWEntry n
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
  cWriteOnMR : b.stateBefore n e_dir (init.stateAt n e_dir) = MREntry n
  fwdSharers : b.downgradeAtSharers n (b.stateBefore n e_dir (init.stateAt n e_dir)).directory e_req e_dir

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
  reqDirOnSW : b.stateBefore n e_dir (init.stateAt n e_dir) = SWEntry n
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
  dirCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n e_dir e_req (init.stateAt n e_req)
  isVcInval : e_inval.isVcInval
  acqEncapDir : e_req.Encapsulates n e_dir
  broadcastInval : b.broadcastToOtherEntriesAfterDir n e_req e_inval e_dir

/-- Def. Non-Coherent Release WritesBack Other Entries in Vd before accessing the Directory -/
structure Behaviour.relWriteBackOtherEntries (b : Behaviour n) (e_req e_wb e_dir : Event n) (init : InitialSystemState n) : Prop where
  isNCRel : e_req.isNCRelease
  isDir : e_dir.isDirectoryEvent
  dirCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n e_dir e_req (init.stateAt n e_req)
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
  ∃ e_dir ∈ b.es, b.cacheEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)

def Behaviour.reqLeavesStateAtLeast (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (state : State) : Prop :=
  state ≤ (b.stateAfter n e_req (init.stateAt n e_req)).cache

structure Behaviour.reqWithCorrespondDirLeavesStateAtLeast (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (state : State) : Prop where
  encapCorresponding : b.reqEncapCorrespondingDir n e_req init
  stateAfterAtLeast : b.reqLeavesStateAtLeast n e_req init state

def Behaviour.eventOnCoherentStateAtLeastMRS (b : Behaviour n) (e : Event n) (init : InitialSystemState n) : Prop := match e with
| .cacheEvent ce => let state_made_on := init.stateAt n e |>.cache n;
  state_made_on.c ∧ ce.req.MRS ≤ (b.stateBefore n e (init.stateAt n e)).cache n
| .directoryEvent _ => false

/-- (Old. Don't use.) A Transitive Relation from a Request Event to a Directory Event. For Lemma 3. -/
def Event.relates (e₁ e₂ : Event n) : Prop := e₁.Encapsulates n e₂ ∨ e₁.Ordered n e₂

/- Defs describing where a Coherent Request's Directory Event that links the Request's data to the total order of Directory Entry Events. -/

/-- Def. Prop on a Request Event `e_req`. The state it's made on is lower than it's `Minimum Required State (MRS)`. -/
def Behaviour.missingPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  (b.stateBefore n e_req (init.stateAt n e_req)).cache < e_req.req.MRS

/-- Wrapper structure Def. Prop on a Request Event `e_req`. `e_req` is made on a state where it doesn't have it's `MRS`.-/
structure Behaviour.insufficientReqPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  noPerms : b.missingPerms n e_req init

/-- Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
def Behaviour.hasPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  e_req.req.MRS ≤ (b.stateBefore n e_req (init.stateAt n e_req)).cache

/-- Wrapper structure Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
structure Behaviour.sufficientReqPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  hasPerms : b.hasPerms n e_req init
  acqRelHasCoherentPerms : e_req.isAcquire ∨ e_req.isNCRelease → (b.stateBefore n e_req (init.stateAt n e_req)).cache.c

/-- Def. Structure stating a request event `e_req` has insufficient permissions, so it encapsulates directory event. -/
structure Behaviour.insufficientReqPermsSoEncapDir (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  noPerms : b.missingPerms n e_req init
  reqEncapDir : e_req.Encapsulates n e_dir

/-- Alternate Def of a request event `e_req` that has insufficient permissions, so it encapsulates a directory event. -/
def Behaviour.insufficientReqPermsSoEncapDir' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.missingPerms n e_req init → ∃ e_dir ∈ b.es, e_req.Encapsulates n e_dir

def Behaviour.predWithCorrespondingDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  (b.reqWithCorrespondDirLeavesStateAtLeast n e_pred init (b.stateBefore n e_req (init.stateAt n e_req) |>.cache))

def Behaviour.immBottomPredEncapCorrDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predWithCorrespondingDirLeavesStateAtLeastReq n · e_req init)

structure Behaviour.reqHasPermsSoDirPred (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  hasPerms : b.sufficientReqPerms n e_req init
  immPredEncapDir : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/-- Alternate Def of a request event `e_req` that has insufficient permissions, so it encapsulates a directory event. -/
def Behaviour.reqHasPermsSoDirPred' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.sufficientReqPerms n e_req init → ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/-- Inductive Prop. State where is the directory event that obtains permissions for a Coherent Request. -/
inductive Behaviour.dirEventOfCoherentReq (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| encapDir : b.insufficientReqPermsSoEncapDir n e_req e_dir init → Behaviour.dirEventOfCoherentReq b e_req e_dir init
| orderBeforeDir : b.reqHasPermsSoDirPred n e_req e_dir init → Behaviour.dirEventOfCoherentReq b e_req e_dir init -- [NOTE]: not technically necessary

/-- Alternate Def of Inductive Prop. State where is the directory event that obtains permissions for a Coherent Request. -/
structure Behaviour.dirEventOfCoherentReq' (b : Behaviour n)  (e_req : Event n) (init : InitialSystemState n) : Prop where
  encapDir : b.insufficientReqPermsSoEncapDir' n e_req init
  orderBeforeDir : b.reqHasPermsSoDirPred' n e_req init

/-- Top Level Def. Prop on a Coherent Request `e_coh_req`, and where will the directory event that gave it cache permissions for `e_coh_req`'s access is. -/
structure Behaviour.coherentReqDirEvent (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  coherentReq : e_req.isCoherent
  dirOfReq : b.dirEventOfCoherentReq n e_req e_dir init
  notDowngrade : ¬e_req.down

/-- Alternate top level def, for struct. -/
def Behaviour.cohReqDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isCoherent → ¬e_req.down → b.dirEventOfCoherentReq' n e_req init

/- Defs describing where a Non-Coherent Weak Read's Directory Event that links the Read's data to the total order of Directory Entry Events. -/

/-- Def. Prop Non-Coherent Weak Read on Vc or SW must have had an immediate bottom predecessor request event that brought the entry state to Vc or SW. -/
structure Behaviour.ncWeakReadVcOrSWDirBefore (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqOnVcOrSw : b.stateBefore n e_req (init.stateAt n e_req) = VcEntry n ∨ b.stateBefore n e_req (init.stateAt n e_req) = SWEntry n
  immPredEncapDir : b.reqHasPermsSoDirPred n e_req e_dir init

/-- Alternate def (for Lemma 3). for Non-Coherent Weak Read on Vc or SW must have had an immediate bottom predecessor request event that brought the entry state to Vc or SW.-/
def Behaviour.ncWeakReadVcOrSWDirBefore' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.stateBefore n e_req (init.stateAt n e_req) = VcEntry n ∨ b.stateBefore n e_req (init.stateAt n e_req) = SWEntry n
  → b.reqHasPermsSoDirPred' n e_req init

structure Behaviour.reqOnVdWithCorrespondingDir (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  stateBeforeAsVd : b.stateBefore n e_req (init.stateAt n e_req) = VdEntry n
  encapCorresponding : b.reqEncapCorrespondingDir n e_req init

def Behaviour.succOnVdWithCorrespondingDir (b : Behaviour n) (e_succ : Event n) (init : InitialSystemState n) : Prop :=
  (b.reqOnVdWithCorrespondingDir n e_succ init)

/-- Def. Prop. there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
def Behaviour.immBottomSuccOnVdEncapCorrDir (b : Behaviour n) (e_req e_succ : Event n) (init : InitialSystemState n) : Prop :=
  b.ImmediateBottomSuccSatisfyingProp n e_req e_succ (b.succOnVdWithCorrespondingDir n · init)

/-- Wrapper Def there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
structure Behaviour.weakReqOnVdSoDirSucc (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  immSuccEncapDir : ∃ e_succ ∈ b.es, b.immBottomSuccOnVdEncapCorrDir n e_req e_succ init

/-- Def. Prop Non-Coherent Weak Read on Vd must have an immediate bottom successor request event that will write back the entry to directory or get SW permissions. -/
structure Behaviour.ncWeakReadOrWriteVdDirBefore (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  reqOnVd : b.stateBefore n e_req (init.stateAt n e_req) = VdEntry n
  immSuccEncapDir : b.weakReqOnVdSoDirSucc n e_req init

def Behaviour.ncWeakReadOrWriteVdDirBefore' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.stateBefore n e_req (init.stateAt n e_req) = VdEntry n → b.weakReqOnVdSoDirSucc n e_req init

/-- Def. Inductive Prop on Non-Coherent Weak Read and where is it's directory event that ties it to the directory entry's total order. -/
inductive Behaviour.dirEventOfNCWeakRead (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| encapDir : b.insufficientReqPermsSoEncapDir n e_req e_dir init → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderBeforeDir : b.ncWeakReadVcOrSWDirBefore n e_req e_dir init → Behaviour.dirEventOfNCWeakRead b e_req e_dir init
| orderAfterDir : b.ncWeakReadOrWriteVdDirBefore n e_req e_dir init → Behaviour.dirEventOfNCWeakRead b e_req e_dir init

/-- Alternate def for Lemma 3 -/
structure Behaviour.dirEventOfNCWeakRead' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  encapDir : b.insufficientReqPermsSoEncapDir' n e_req init
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
  hasPerms : b.sufficientReqPerms n e_req init
  isCoherent : (b.stateBefore n e_req (init.stateAt n e_req)).cache.c
  immPredEncapDir : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init

/-- Alternate def for Lemma 3 -/
def Behaviour.reqHasCoherentPermsSoDirPred' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  (hasPerms : b.sufficientReqPerms n e_req init) → (isCoherent : (b.stateBefore n e_req (init.stateAt n e_req)).cache.c) →
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
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)
  notDowngrade : ¬e_req.down

/-- Alternate top level def, for struct. -/
def Behaviour.ncAcqDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isAcquire → ¬e_req.down → b.cacheEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)

/-- Top level def for a Non-Coherent Release's Directory Event relation. -/
structure Behaviour.ncRelease (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  reqNcRelease : e_req.isNCRelease
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)
  notDowngrade : ¬e_req.down
  /-
  dirWrite : e_dir.isWrite
  reqEncapDir : e_req.Encapsulates n e_dir-/

/-- Alternate top level def, for struct. -/
def Behaviour.ncRelDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  Behaviour.axRequestAccessesDirectory n → e_req.isNCRelease → ¬e_req.down →
    b.cacheEncapCorrespondingDirEvent n e_req (init.stateAt n e_req)

/-- Lemma 3 Goal. -/
inductive Behaviour.reqDirRelation (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop
| coherentReq : (∃ e_dir ∈ b.es, b.coherentReqDirEvent n e_req e_dir init) → Behaviour.reqDirRelation b e_req init
| ncWeakRead : (∃ e_dir ∈ b.es, b.ncWeakRead n e_req e_dir init) → Behaviour.reqDirRelation b e_req init
| ncAcq : (b.ncAcquire n e_req init) → Behaviour.reqDirRelation b e_req  init
| ncWeakWrite : (∃ e_dir ∈ b.es, b.ncWeakWrite n e_req e_dir init) → Behaviour.reqDirRelation b e_req init
| ncRel : (b.ncRelease n e_req init) → Behaviour.reqDirRelation b e_req init

structure Behaviour.reqDirRelation' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  cohReqRelation : b.cohReqDirRelation n e_req init
  ncWeakReadDirRelation : b.ncWeakReadDirRelation n e_req init
  ncWeakWriteDirRelation : b.ncWeakWriteDirRelation n e_req init
  ncRelDirRelation : b.ncRelDirRelation n e_req init
  ncAcqDirRelation : b.ncAcqDirRelation n e_req init

-- [NOTE] use `Behaviour.vdCacheEntryWriteBackLater` in the Vd succeeding Dir Events case

-- [TODO] Add Lemma (or Def) to state there exists a previous event `e_pred` before Event `e`, that sets the state that `e` is made on.
lemma Behaviour.exists_predecessor_setting_state (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) :
  -- let state_req_is_made_on := b.stateBefore n e_req (init.stateAt n e_req) |>.cache;
  ∃ e_pred ∈ b.es, b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.reqWithCorrespondDirLeavesStateAtLeast n · init (b.stateBefore n e_req (init.stateAt n e_req) |>.cache)) := by
  by_cases (∃ e_pred ∈ b.es, b.reqLeavesStateAtLeast n e_pred init (init.stateAt n e_req).cache)
  . case pos hpred_leaves_state =>
    apply Exists.intro
    case w => exact hpred_leaves_state.choose
    case h =>
      apply And.intro
      . case left =>
        exact hpred_leaves_state.choose_spec.left
      . case right =>
        have h := hpred_leaves_state.choose_spec.right
        unfold reqLeavesStateAtLeast at h
        sorry
  . case neg hpred_not_leave_state =>
    -- apply Exists.intro
    sorry

/-
def Behaviour.exists_predecessor_setting_state' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop :=
  ∃ e_pred ∈ b.es, b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.reqWithCorrespondDirLeavesStateAs n · init (b.stateBefore n e_req (init.stateAt n e_req) |>.cache))
-/

lemma Behaviour.exists_predecessor_setting_state' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) (hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) :
  ∃ e_pred ∈ b.es, b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.reqLeavesStateAtLeast n · init (b.stateBefore n e_req (init.stateAt n e_req)).cache) := by
  sorry

-- [TODO] expand relation (from Event.relates) to cover the current state.
lemma Behaviour.coherent_req_exists_related_e_dir (b : Behaviour n) (init : InitialSystemState n)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) (e_req : Event n) (he_req_in_b : e_req ∈ b.es)
(rw : ReadWrite) (consistency : Consistency) (hvalid_req : ({ rw := rw, coherent := true, consistency := consistency } : Request).IsValid)
(hreq : e_req.req = ⟨{ rw := rw, coherent := true, consistency := consistency }, hvalid_req⟩) :
  ∃ e_dir ∈ b.es, Event.relates n e_req e_dir := by
  -- Apply Axiom 6 `Behaviour.axRequestAccessesDirectory` here. Move it's input args into it's def.
  have made_on_state := b.stateBefore n e_req (init.stateAt n e_req)

  have ax6 := hreq_encap_dir.reqAccessDir b e_req he_req_in_b init
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases e_req
  . case cacheEvent ce =>
    simp[Event.req] at hreq
    -- do we have enough perms on this state.
    by_cases (made_on_state.cache < ce.req.MRS)
    . case pos hno_perms =>
      match ax6 with
      | .coherentRequest hcoherent_no_perms =>
        -- [TODO] match on the state `e_req` is made on as well!
        have h := hcoherent_no_perms.reqEncapDir.reqEncapCorrDir
        have hreq_encap_dir := h.choose_spec.right.reqEncapCorrespondingDirEvent.reqEncapDir
        have hdir_in_b := h.choose_spec.right.reqEncapCorrespondingDirEvent.dirInB
        apply Exists.intro
        case w => exact h.choose
        case h =>
          apply And.intro
          . case left => exact hdir_in_b
          . case right =>
            unfold Event.relates
            apply Or.intro_left
            exact hreq_encap_dir
      | .nonCoherentRelease hnc_rel =>
        have h := hnc_rel.choose_spec.right.notCoherent
        unfold CacheEvent.Coherent at h
        have hreq_coherent : ce.req.val.coherent = true := by
          simp[hreq]
        contradiction
      | .acquire hacq =>
        -- Cannot be a coherent acquire.
        have hacq_constraint := hvalid_req.no_cacq
        unfold Request.NoCoherentAcquire at hacq_constraint
        simp at hacq_constraint
        have hconsistency_acq := hacq.isAcquire
        absurd hconsistency_acq
        rw[hreq] at hconsistency_acq
        simp at hconsistency_acq
        contradiction
        -- simp_all only [not_true_eq_false]
      | .weakWrite hweak_w =>
        have hnot_coherent := hweak_w.notCoherent
        simp[CacheEvent.Coherent] at hnot_coherent
        simp[hreq] at hnot_coherent
      | .weakRead hweak_r =>
        have hnot_coherent := hweak_r.notCoherent
        simp[CacheEvent.Coherent] at hnot_coherent
        simp[hreq] at hnot_coherent
      | .evictVdWB hvd_wb =>
        have his_vd_wb := hvd_wb.isVdWriteBack
        simp[hreq] at his_vd_wb
      | .evictSCPutM hputm =>
        have hevict_encap_dir := hputm.encapPutMDirEvent.evictEncapCorrDir.choose_spec
        have hencap_dir := hevict_encap_dir.right.evictEncapCorrespondingDirEvent.reqEncapDir
        apply Exists.intro
        case w =>
          . exact hputm.encapPutMDirEvent.evictEncapCorrDir.choose
        case h =>
          apply And.intro
          . case left => exact hevict_encap_dir.left
          . case right =>
            unfold Event.relates
            apply Or.intro_left
            exact hencap_dir
      | .evictSCPutS hputs =>
        have hevict_encap_dir := hputs.encapPutSDirEvent.evictEncapCorrDir.choose_spec
        have hencap_dir := hevict_encap_dir.right.evictEncapCorrespondingDirEvent.reqEncapDir
        apply Exists.intro
        case w =>
          . exact hputs.encapPutSDirEvent.evictEncapCorrDir.choose
        case h =>
          apply And.intro
          . case left => exact hevict_encap_dir.left
          . case right =>
            unfold Event.relates
            apply Or.intro_left
            exact hencap_dir
    . case neg hhas_perms =>
      /- Use some reasoning like `Behaviour.exists_predecessor_setting_state` to state there's
      a directory event encapsulated by a previous cache event. -/
      -- [TODO] Want to replace this lemma with exists_predecessor_setting_state', and state the pred encaps a directory event separately?
      let hpred_encap_dir := Behaviour.exists_predecessor_setting_state n b (Event.cacheEvent ce) init hreq_encap_dir;
      let h := hpred_encap_dir.choose_spec.right
      let h_choose := hpred_encap_dir.choose
      simp at h
      obtain ⟨hpred, himm_pred_same_succ_state⟩ := h
      unfold Event.PropOnEvent at himm_pred_same_succ_state
      simp at himm_pred_same_succ_state
      have h1 := himm_pred_same_succ_state.encapCorresponding.choose_spec.right
      obtain ⟨e_dir, hedir_in_b, hce_encap_dir⟩ := h1
      have h2 := hce_encap_dir.reqEncapDir

      have hdir_encap_by_pred : e_dir.EncapsulatedBy n hpred_encap_dir.choose := by simp [h2]
      have hpred_before_req : hpred_encap_dir.choose < Event.cacheEvent ce := by
        exact hpred.isImmPred.isPred

      apply Exists.intro
      case mk.mk.intro.intro.w => exact e_dir
      case mk.mk.intro.intro.h =>
        apply And.intro
        . case left => exact hedir_in_b
        . case right =>
          unfold Event.relates
          apply Or.intro_right
          unfold Event.Ordered
          apply Or.intro_right
          calc (e_dir.EncapsulatedBy n) hpred_encap_dir.choose := hdir_encap_by_pred
            (Event.OrderedBefore n) _ (Event.cacheEvent ce) := hpred_before_req
  . case directoryEvent _ => simp at ax6

lemma Behaviour.nc_weak_read_req_exists_related_e_dir' (b : Behaviour n) (init : InitialSystemState n)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) (e_req : Event n) (he_req_in_b : e_req ∈ b.es)
(rw : ReadWrite) (consistency : Consistency) (hvalid_req : ({ rw := rw, coherent := true, consistency := consistency } : Request).IsValid)
(hreq : e_req.req = ⟨{ rw := rw, coherent := true, consistency := consistency }, hvalid_req⟩)
(he_req_coh : Event.isCoherent n e_req)
(he_req_not_down : ¬Event.down n e_req = true) :
  -- b.reqDirRelation n e_req init
  ∃ e_dir ∈ b.es, dirEventOfCoherentReq n b e_req e_dir init
  := by
  sorry

lemma Behaviour.nc_acq_req_exists_related_e_dir (b : Behaviour n) (init : InitialSystemState n)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) (e_req : Event n) (he_req_in_b : e_req ∈ b.es)
(hvalid_req : ({ rw := .r, coherent := false, consistency := .Acq } : Request).IsValid)
(hreq : e_req.req = ⟨{ rw := .r, coherent := false, consistency := .Acq }, hvalid_req⟩) :
  -- b.reqDirRelation n e_req init
  ∃ e_dir ∈ b.es, Event.relates n e_req e_dir
  := by
  have made_on_state := b.stateBefore n e_req (init.stateAt n e_req)

  have ax6 := hreq_encap_dir.reqAccessDir b e_req he_req_in_b init
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases e_req
  . case cacheEvent ce =>
    simp at ax6
    simp[Event.req] at hreq

    match ax6 with
    | .acquire hacq =>
      obtain ⟨e_dir, hreq_encap_dir⟩ := hacq.encapDirEvent.reqEncapCorrDir
      have h := hreq_encap_dir.right.reqEncapCorrespondingDirEvent.reqEncapDir

      use e_dir
      apply And.intro
      . case h.left => exact hreq_encap_dir.left
      . case h.right =>
        simp[Event.relates]
        simp[Or.intro_left, h]
    | .coherentRequest hcoh_req =>
      have hcoherent := hcoh_req.isCoherent
      simp[Event.req] at hcoherent
      have h_not_coh : ¬ ce.req.val.coherent := by simp[hreq]
      contradiction
    | .nonCoherentRelease hnc_rel =>
      unfold nonCoherentRelease at hnc_rel
      obtain ⟨e_dir_wb, hrel_encap_dir⟩ := hnc_rel
      have hreq_is_acq : ce.req.val.consistency = .Acq := by simp[hreq]
      absurd hrel_encap_dir.right.isRelease
      simp [hreq_is_acq]
    | _ => sorry
  . case directoryEvent _ => simp at ax6

lemma Behaviour.nc_rel_req_exists_related_e_dir (b : Behaviour n) (init : InitialSystemState n)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n) (e_req : Event n) (he_req_in_b : e_req ∈ b.es)
(hvalid_req : ({ rw := .w, coherent := false, consistency := .Rel } : Request).IsValid)
(hreq : e_req.req = ⟨{ rw := .w, coherent := false, consistency := .Rel }, hvalid_req⟩) :
  -- b.reqDirRelation n e_req init
  ∃ e_dir ∈ b.es, Event.relates n e_req e_dir
  := by
  have made_on_state := b.stateBefore n e_req (init.stateAt n e_req)

  have ax6 := hreq_encap_dir.reqAccessDir b e_req he_req_in_b init
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases e_req
  . case cacheEvent ce =>
    simp at ax6
    simp[Event.req] at hreq

    match ax6 with
    | .nonCoherentRelease hnc_rel =>
      unfold nonCoherentRelease at hnc_rel
      obtain ⟨e_dir_wb, hrel_encap_dir⟩ := hnc_rel
      have h := hrel_encap_dir.right.encapsDirWB.reqEncapCorrespondingDirEvent.reqEncapDir

      use e_dir_wb
      apply And.intro
      . case h.left => exact hrel_encap_dir.left
      . case h.right =>
        simp[Event.relates]
        simp[Or.intro_left, h]
    | .coherentRequest hcoh_req =>
      have hcoh := hcoh_req.isCoherent
      simp[Event.req] at hcoh
      have h_not_coh : ¬ ce.req.val.coherent := by simp[hreq]
      contradiction
    | .acquire hacq =>
      have hcoh := hacq.isAcquire
      simp[Event.req] at hcoh
      have h_not_acq : ¬ ce.req.val.consistency = .Acq := by simp[hreq]
      contradiction
    | .weakWrite hww => sorry
    | .weakRead hwr => sorry
    | .evictVdWB he_vd_wb => sorry
    | .evictSCPutM hsc_putm => sorry
    | .evictSCPutS hsc_puts => sorry
  . case directoryEvent _ => simp at ax6

/-
structure Behaviour.hasCoherentPerms (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n) : Prop where
  coherentState : (b.stateBefore n e_req (init.stateAt n e_req)).cache.c
  mrsLeS : e_req.req.MRS ≤ (b.stateBefore n e_req (init.stateAt n e_req)).cache
-/
lemma Behaviour.exists_predecessor_setting_state'' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n)
  (hhave_perms : sufficientReqPerms n b e_req init)
  (hinit_i : (init.stateAt n e_req).cache = I)
  (hcoherent_perms : (b.stateBefore n e_req (init.stateAt n e_req)).cache ≠ Vd)
  (hax6 : Behaviour.axRequestAccessesDirectory n)
  (hreq_is_ce : e_req.isCacheEvent n)
  :
  ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init := by
  by_contra hno_imm_pred_getting_state
  /- first show there's a predecessor `e_pred`, that produces state `s` that `e_req` is made on.
  We know `s` is at least `e_req.MRS` -/
  have hmrs_le_s := hhave_perms.hasPerms
  simp[hasPerms] at hmrs_le_s
  /- By cases on `e_req.MRS`, we know `s` is `≥` a State that isn't `I`. -/
  match he : e_req with
  | .cacheEvent ce =>
    match hmrs : e_req.req.MRS with
    | ⟨some .wr, true⟩ => sorry
    | ⟨some .r, true⟩ => sorry
    | ⟨some .wr, false⟩ => sorry
    | ⟨some .r, false⟩ => sorry
    | ⟨none, true⟩ => sorry
    | ⟨none, false⟩ =>
      match hreq : e_req.req with
      | ⟨⟨rw,false,_⟩,_⟩ =>
        match rw with
        | .w => sorry
        | .r =>
          simp[Event.req] at hmrs hreq
          simp[he] at hmrs hreq
          simp[hreq] at hmrs
          simp[ValidRequest.MRS] at hmrs
          split at hmrs
          case h_1 => simp at hmrs
          case h_2 => simp at hmrs
          case h_3 => simp at hmrs
          case h_4 =>
            -- simp[hmrs]
            simp at hmrs
      | _ => sorry
  | .directoryEvent _ => simp[Event.isCacheEvent] at hreq_is_ce
  -- cases (b.stateBefore n e_req (init.stateAt n e_req)).cache
  /-
  have h : ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init := by
    by_cases hexists_req_pred : ∃ e_pred' ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred' e_req init
    . case pos => exact hexists_req_pred
    . case neg =>
      --
      sorry-/

lemma Behaviour.exists_predecessor_setting_state_encap_dir_event'' (b : Behaviour n) (e_req : Event n) (init : InitialSystemState n)
  (hhave_perms : sufficientReqPerms n b e_req init)
  :
  ∃ e_pred ∈ b.es, b.immBottomPredEncapCorrDirLeavesStateAtLeastReq n e_pred e_req init := by
  sorry

-- [TODO] constrain goal to say not just `e_req` relates `e_dir`, but either encapsulates if lacking permissions, or a previous one if have perms,
-- of a future one if Weak Non-Coherent on Vd
/-- Lemma 3. For each Cache Request Event `e_req`, there exists a unique event `e_dir` relating `e_req` to the total order of events at
`e_req`'s corresonponding Directory entry. -/
lemma Behaviour.exists_e_dir_relating_e_req (b : Behaviour n) (init : InitialSystemState n)
(e_req : Event n) (he_req_in_b : e_req ∈ b.es)
(hreq_encap_dir : Behaviour.axRequestAccessesDirectory n)
(hvd_wb_later : Behaviour.vdCacheEntryWriteBackLater n b e_req init) :
  ∃ e_dir ∈ b.es, e_req.relates n e_dir
  -- b.reqDirRelation n e_req init
  := by
  have ax6 := hreq_encap_dir.reqAccessDir b e_req he_req_in_b init
  unfold Behaviour.requestAccessesDirectoryWrapper at ax6
  simp at ax6
  cases e_req
  . case cacheEvent ce =>
    match hreq : ce.req with
    | ⟨⟨rw,true,consistency⟩, hvalid_req⟩ =>
      apply coherent_req_exists_related_e_dir n b init hreq_encap_dir (Event.cacheEvent ce) he_req_in_b rw consistency hvalid_req hreq
      -- sorry
      -- apply b.coherent_req_exists_related_e_dir' n init hreq_encap_dir (Event.cacheEvent ce) he_req_in_b rw consistency hvalid_req hreq
    | ⟨⟨.r,false,.Weak⟩, {}⟩ =>
      /-
      match ax6 with
      | .coherentRequest hcoherent_no_perms => sorry
      | .nonCoherentRelease hnc_rel => sorry
      | .acquire hacq => sorry
      | .weakWrite hweak_w => sorry
      | .weakRead hweak_r => sorry
      | .evictVdWB hvd_wb => sorry
      | .evictSCPutS hputs => sorry
      -/
      sorry
    | ⟨⟨.r,false,.Acq⟩, {}⟩ =>
      sorry
    | ⟨⟨.w,false,.Weak⟩, {}⟩ => sorry
    | ⟨⟨.w,false,.Rel⟩, {}⟩ =>
      sorry
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
