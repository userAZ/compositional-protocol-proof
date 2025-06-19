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
