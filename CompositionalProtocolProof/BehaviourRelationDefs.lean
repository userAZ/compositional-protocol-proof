import CompositionalProtocolProof.Behaviours
import CompositionalProtocolProof.BehaviourHelpers

variable (n : Nat)

/-
structure Request.IsValid (r : Request) where
  non_coherent : r.NoSCNonCoherent := by simp
  no_write_acq : r.NoWriteAcquire := by simp
  no_read_rel : r.NoReadRelease := by simp
  no_cacq : r.NoCoherentAcquire := by simp
  no_cwr : r.NoCoherentWeakRead := by simp
-/

noncomputable def Behaviour.cacheStateMadeOn (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : State :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache
noncomputable def Behaviour.directoryStateMadeOn (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : DirectoryState n :=
  (b.stateBefore n (init.stateAt n e_req) e_req).directory

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

def Behaviour.eventOnCoherentStateAtLeastMRS (b : Behaviour n) (e : Event n) (init : InitialSystemState n) : Prop := match e with
| .cacheEvent _ => b.eventOnCoherentState n init e ∧ b.eventOnStateHasPerms n init e
| .directoryEvent _ => False

def Behaviour.acqRelWeakWriteNoPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  ¬ (b.eventOnCoherentState n init e_req ∧ b.eventOnStateHasPerms n init e_req)

noncomputable def Event.reqToDirOfRequestEvent (e_req : Event n) (state_before : State) : ValidRequest :=
  match e_req.req, state_before, e_req.down with
  | ⟨⟨.w, false, _⟩, _⟩, ⟨none, false⟩ /- made on I state -/, false => ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩
  | ⟨⟨.w, false, _⟩, _⟩, ⟨none, true⟩ /- handle this case just in case -/, false => ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩
  | ⟨⟨.r, false, .Acq⟩, _⟩, ⟨some .wr, false⟩ /- made on Vd state -/, _ => ⟨⟨.w, false, .Weak⟩, by simp[Request.IsValid']⟩
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
  sameDown : e_dir.down = e_req.down
  dirState : e_dir.isDirEventOfDirState n (b.stateAfter n init e_dir).directory
  sameProtocol : e_req.sameProtocol n e_dir

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
  sameProtocol : e_req.protocol = e_dir.protocol
  dirInB : e_dir ∈ b
  reqInB : e_req ∈ b

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

structure Event.acqEncapInvalAfterDir (e_req e_dir e_inval : Event n) (addr : Addr) : Prop where
  dirBeforeInval : e_dir.OrderedBefore n e_inval
  vcInval : e_inval.isVcInval
  acqEncapInval : e_req.Encapsulates n e_inval
  sameCid : e_req.cid = e_inval.cid
  otherAddr : e_inval.addr = addr
  cacheEvent : e_inval.isCacheEvent

/--Axiom 4. Acquire invalidates other Vc cache entries after it's directory access. -/
structure Behaviour.acquireInvalidates (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isAcquire : e_req.isAcquire
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n init true e_req
  invalOther : ∀ addr ≠ e_req.addr, ∃ e_inval ∈ b, e_req.acqEncapInvalAfterDir n e_dir e_inval addr

/-- Wrapper for Axiom 4. An Acquire invalidates Vc entries. -/
def Behaviour.acqInvalWrapper : Prop := ∀ b : Behaviour n, ∀ e_req e_dir : Event n,
  b.acquireInvalidates n e_req e_dir

/-- Axiom 5. Non Coherent Release writes back other Vd cache entries before it's directory access. -/
structure Behaviour.ncReleaseWritesBack (b : Behaviour n) (e_req e_dir : Event n) : Prop where
  isRelease : e_req.isNcRelease
  encapDirEvent : ∀ init : EntryState n, b.reqEncapCorrespondingDirEvent n init true e_req
  writeBackOther : ∀ addr ≠ e_req.addr, ∃ e_wb ∈ b.es, e_wb.OrderedBefore n e_dir ∧ e_wb.isVdWriteBack

def Behaviour.ncRelWriteBackWrapper : Prop := ∀ b : Behaviour n, ∀ e_req e_dir : Event n,
  b.ncReleaseWritesBack n e_req e_dir

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
  existsDirWb : ∃ e_dir_wb ∈ b, b.nonCoherentReleaseEncapDirEvents n e_req e_dir_wb init

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

def Behaviour.evictOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache = e_req.MRS

def Behaviour.eventOnMRSState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateBefore n (init.stateAt n e_req) e_req).cache = e_req.req.MRS

/-- Def Props stating when an Evicting Weak Non-Coherent Write accesses the Directory -/
structure Behaviour.evictVdWBEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  isDowngrade : e_req.down
  isVdWriteBack : e_req.req.val = ⟨.w, false, .Weak⟩
  mrsVdState : e_req.MRS = Vd
  madeOnMrs : b.evictOnMRSState n init e_req
  encapWBDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

structure Behaviour.evictSCPutMEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  isDowngrade : e_req.down
  isPutM : e_req.req.val = ⟨.w, true, .SC⟩
  mrsSWState : e_req.MRS = SW
  madeOnMrs : b.evictOnMRSState n init e_req
  encapPutMDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

structure Behaviour.evictSCPutSEncapsulatesDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  isDowngrade : e_req.down
  isPutS : e_req.req.val = ⟨.r, true, .SC⟩
  mrsMRState : e_req.MRS = MR
  madeOnMrs : b.evictOnMRSState n init e_req
  encapPutSDirEvent : b.evictEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req

/-- Axiom 6: When a Request Event encapsulates Directory Events to access/request from the Directory. -/
inductive Behaviour.requestAccessesDirectory (b : Behaviour n) (ce : CacheEvent n) (init : InitialSystemState n) : Prop
| coherentRequest (hcohrent_req_of_no_perms : b.requestCoherentNoPerms n init (Event.cacheEvent ce)) : Behaviour.requestAccessesDirectory b ce init
| nonCoherentRelease (hnc_rel : b.nonCoherentRelease n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: have a struct and fields for OnI and OnV
| acquire (hacq_encap_dir : b.acquireEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : Not on MR
| weakWrite (hncww_encap_dir : b.ncWeakWriteEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| weakRead (hncwr_encap_dir : b.ncWeakReadEncapDirEvent n init ce) : Behaviour.requestAccessesDirectory b ce init -- TODO: struct field : On I
| evictVdWB (hevict_vd_wb_encap_dir : b.evictVdWBEncapsulatesDirEvent n init (Event.cacheEvent ce)) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutM (hevict_put_m_encap_dir : b.evictSCPutMEncapsulatesDirEvent n init (Event.cacheEvent ce)) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}
| evictSCPutS (hevict_put_s_encap_dir : b.evictSCPutSEncapsulatesDirEvent n init (Event.cacheEvent ce)) : Behaviour.requestAccessesDirectory b ce init -- TODO: downgrade field true, AND struct field: is one of {VdWriteBack, Coherent Write, Coherent Read}

/-- Axiom 6 Event → CacheEvent Wrapper. -/
def Behaviour.requestAccessesDirectoryWrapper (b : Behaviour n) (e : Event n) (init : InitialSystemState n) : Prop := match e with
  | .cacheEvent ce => b.requestAccessesDirectory n ce init
  | .directoryEvent _ => false

/-- Axiom 6 Structure Wrapper for use in Lemmas. -/
def Behaviour.axRequestAccessesDirectory : Prop :=
  ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e ∈ b, b.requestAccessesDirectoryWrapper n e init

structure Behaviour.vdStateBeforeWBOrGetSW (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop where
  onVd : (b.stateBefore n (init.stateAt n e) e).cache = Vd
  isWBOrGetSW : e.isVdWriteBack ∨ e.isCoherentWrite

/-- Axiom 7, a Cache Entry in Vd State may writeback -/
structure Behaviour.vdCacheEntryWriteBackLater (b : Behaviour n) (init : InitialSystemState n) (e : Event n) /-(vd_wb_e : Event n)-/ : Prop where
  vdStateAfterEvent : b.stateAfter n (init.stateAt n e) e = VdEntry n
  wbImmPred : ∃ vd_wb_e ∈ b.es, b.ImmediateBottomSuccSatisfyingProp n e vd_wb_e (b.vdStateBeforeWBOrGetSW n init ·)

/-- Axiom 7 Wrapper. -/
def Behaviour.vdCacheEntryWBOrGetSWLaterWrapper : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e : Event n,
  b.vdCacheEntryWriteBackLater n init e

/-- Def. state that two events `e₁` `e₂` are orderedBefore if their Deid fields are orderedBefore. -/
structure Behaviour.orderedDeidEvents (b : Behaviour n) (e₁ e₂ : Event n) : Prop where
  orderedDeid : e₁.deidOrderBefore n e₂
  orderedEvents : e₁.OrderedBefore n e₂
  e₁InB : e₁ ∈ b
  e₂InB : e₂ ∈ b

/-- Axiom 8, messages from the directory are ordered by Cache Event `deid?` field. -/
def Behaviour.deidOrdered : Prop := ∀ b : Behaviour n, ∀ e₁ e₂ : Event n, b.orderedDeidEvents n e₁ e₂

/-- Def. Constraints on fields of Forwarded Downgrade. -/
structure Behaviour.requestDowngradePrevOwner (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir e_fwd_down : Event n) : Prop where
  atPrevOwner : e_fwd_down.downgradeAtPrevOwner n (b.stateBefore n (init.stateAt n e_dir) e_dir).directory
  fwdFromRequester : e_req.downgradeCorrespondingToRequest n e_fwd_down
  idCorrespondDir : e_fwd_down.fromDirectory n e_dir
  dirEncapDowngrade : e_dir.Encapsulates n e_fwd_down -- already have from Request Encaps Directory Event
  reqEncapDir : e_req.Encapsulates n e_dir
  sameAddrAsReq : e_fwd_down.addr = e_req.addr
  downAtCache : e_fwd_down.isCacheEvent

/- Def. Constraints on fields of Forwarded Downgrade events, and Grant Events. -/
structure Behaviour.downgradeAtPrevOwner (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir e_fwd_down e_grant : Event n) : Prop where
  downgradePrevOwner : b.requestDowngradePrevOwner n init e_req e_dir e_fwd_down
  grantRels : e_req.encapGrantAfterDirEvent n e_dir e_grant

/- Def. When a Coherent Request causes a Forwarded Downgrade to the previous owner at the Directory. (and a Grant Event) -/
structure Behaviour.fwdCoherentRequestToOwner (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  reqDirOnSW   : (b.stateBefore n (init.stateAt n e_dir) e_dir).state = SW
  fwdPrevOwner : ∃ e_down ∈ b, ∃ e_grant ∈ b, b.downgradeAtPrevOwner n init e_req e_dir e_down e_grant

def Event.swDowngradeSharersParameters (e_req e_down : Event n) (sharer : CacheId n) : Prop :=
  match e_req, e_down with
  | .cacheEvent request, .cacheEvent downgrade =>
    request.downgradeOfReqToCache n downgrade sharer
  | _, _ => false

structure Event.swDowngradeSharers (e_req e_dir e_down e_grant : Event n) (sharer : CacheId n): Prop where
  downgradeParameters : e_req.swDowngradeSharersParameters n e_down sharer
  downgradeOrdering : e_req.fwdMRDowngradeEventOrdering n e_dir e_down e_grant

/-- Def. Downgrade to sharers -/
def Behaviour.downgradeAtSharers (b : Behaviour n) (dir_state : DirectoryState n) (e_req e_dir : Event n) : Prop := match dir_state with
  | .MR _ sharers => ∃ e_grant ∈ b.es, ∀ s ∈ sharers, s ≠ e_req.cid → ∃ e_down ∈ b.es,
    e_req.swDowngradeSharers n e_dir e_down e_grant s
  | _ => false

/-- Def. fwd coherent request to other Sharer caches -/
structure Behaviour.fwdCoherentRequestToSharers (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  cWriteOnMR : (b.stateBefore n (init.stateAt n e_dir) e_dir).state = MR
  fwdSharers : b.downgradeAtSharers n (b.stateBefore n (init.stateAt n e_dir) e_dir).directory e_req e_dir

/- Def. Which directory states will a Coherent Write Request cause downgrades at other caches. Includes Props on Downgrade Events to
other caches. -/
inductive Behaviour.coherentWriteAtDirectoryEncapDowngrades (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop
| cWriteOnSW : b.fwdCoherentRequestToOwner n init e_req e_dir → Behaviour.coherentWriteAtDirectoryEncapDowngrades b init e_req e_dir
| cWriteOnMR : b.fwdCoherentRequestToSharers n init e_req e_dir → Behaviour.coherentWriteAtDirectoryEncapDowngrades b init e_req e_dir

/-- Def. When a coherent write to the Directory downgrades other caches. -/
structure Behaviour.coherentWriteDowngradeOthers (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  isDirEvent : e_dir.isDirectoryEvent
  dirCoherentWrite : e_dir.req.isCoherentWrite
  isCacheEvent : e_req.isCacheEvent
  reqCoherentWrite : e_req.req.isCoherentWrite
  downgradeOtherCaches : b.coherentWriteAtDirectoryEncapDowngrades n init e_req e_dir

/-- Axiom 9, Coherent-Write request to Directory results in Downgrade at other caches axiom. -/
def Behaviour.coherentWriteDirDowngradeOthers : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_req ∈ b.es, ∀ e_dir ∈ b, b.coherentWriteDowngradeOthers n init e_req e_dir

/- Def. Which directory states will a Coherent Read Request cause downgrades at other caches. Includes Props on Downgrade Events to
other caches. -/
inductive Behaviour.coherentRequestAtDirectoryEncapDowngrades (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop
| cReadOnSW : b.fwdCoherentRequestToOwner n init e_req e_dir → Behaviour.coherentRequestAtDirectoryEncapDowngrades b e_req e_dir init

/-- Def. Props on Coherent Read Request event accessing the directory -/
structure Behaviour.coherentReadDowngradeOthers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  isDirEvent : e_dir.isDirectoryEvent
  dirCoherentRead : e_dir.req.isCoherentRead
  isCacheEvent : e_req.isCacheEvent
  reqCoherentRead : e_req.req.isCoherentRead
  downgradeOtherCaches : b.coherentRequestAtDirectoryEncapDowngrades n e_req e_dir init

/-- Axiom 10. Coherent-Read request to Directory results in Downgrade at other caches axiom. -/
def Behaviour.coherentReadDirDowngradeOthers : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_req ∈ b.es, ∀ e_dir ∈ b.es, b.coherentReadDowngradeOthers n e_req e_dir init

/-- Prop Structure Helper for Axiom 11. Coherent Evict at Directory encapsulates a Grant OrderedAfter the Directory Event. -/
structure Behaviour.coherentEvictDirGrantOrdering (b : Behaviour n) (e_req e_dir e_grant : Event n) : Prop where
  isEvict : e_req.isEvict
  reqEncapDir : e_req.Encapsulates n e_dir
  reqDirGrantOrderings : e_req.encapGrantAfterDirEvent n e_dir e_grant

/-- Axiom 11. Coherent Evict at Directory encapsulates a Grant OrderedAfter the Directory Event. -/
def Behaviour.coherentEvictGetsGrant : Prop :=
  ∀ b : Behaviour n, ∀ e_req ∈ b, ∀ e_dir ∈ b, ∃ e_grant ∈ b, b.coherentEvictDirGrantOrdering n e_req e_dir e_grant

structure Behaviour.nonCoherentReqOnSWDowngradeOthers (b : Behaviour n) (e_req e_dir : Event n) (init : InitialSystemState n) : Prop where
  dirNCReq : e_dir.req.NonCoherent
  isDir : e_dir.isDirectoryEvent
  isCache : e_req.isCacheEvent
  reqDirOnSW : (b.stateBefore n (init.stateAt n e_dir) e_dir).state = SW
  fwdPrevOwner : ∃ e_down ∈ b, b.requestDowngradePrevOwner n init e_req e_dir e_down

/-- Axiom 12. Non-Coherent Write/Read on SW Directory State results in Downgrades. -/
def Behaviour.nonCoherentRequestDowngradeOthers : Prop :=
  ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b, ∀ e_dir ∈ b,
    b.nonCoherentReqOnSWDowngradeOthers n e_req e_dir init

/-- Def.a (broadcast before e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEventBefore (b : Behaviour n) (addr : Addr) (e_base e_original e_dir: Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b, e_base.baseEncapBroadcastBefore n addr' e_original e_cast_copy e_dir

/-- Def.b (broadcast after e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEventAfter (b : Behaviour n) (addr : Addr) (e_base e_original e_dir : Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b.es, e_base.baseEncapBroadcastAfter n addr' e_original e_cast_copy e_dir

/-- Def.c (broadcast after e_dir) For all other entry addresses, an event `e_original` is copied and broadcast to other entries. -/
structure Behaviour.broadcastEvent (b : Behaviour n) (addr : Addr) (e_base e_original : Event n) : Prop where
  broadcastToEntries : ∀ addr' ≠ addr, ∃ e_cast_copy ∈ b, e_base.baseEncapBroadcast n addr' e_original e_cast_copy

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
  isCache : e_inval.isCacheEvent
  sameCid : e_inval.cid = e_req.cid
  acqEncapDir : e_req.Encapsulates n e_dir
  broadcastInval : b.broadcastToOtherEntriesAfterDir n e_req e_inval e_dir

/-- Def. Non-Coherent Release WritesBack Other Entries in Vd before accessing the Directory -/
structure Behaviour.relWriteBackOtherEntries (b : Behaviour n) (e_req e_wb e_dir : Event n) (init : InitialSystemState n) : Prop where
  isNCRel : e_req.isNcRelease
  isDir : e_dir.isDirectoryEvent
  dirCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_dir e_req
  isVdWriteBack : e_wb.isVdWriteBack
  isCache : e_wb.isCacheEvent
  sameCid : e_wb.cid = e_req.cid
  relEncapDir : e_req.Encapsulates n e_dir
  broadcastWB : b.broadcastToOtherEntriesBeforeDir n e_req e_wb e_dir

structure Behaviour.broadcastWbFromDowngrade (b : Behaviour n) (e_down e_wb : Event n) where
  isVdWriteBack : e_wb.isVdWriteBack
  broadcastWB : b.broadcastToOtherEntries n e_down e_wb
  gotDowngrade : e_down.down -- Assume it arrives on SW state.

structure Behaviour.generateDowngradeToBroadcast (b : Behaviour n) (e_wb e_down : Event n) where
  wbCache : e_wb.isCacheEvent
  wbSameCidAsDown : e_wb.cid = e_down.cid
  broadcastWb : b.broadcastWbFromDowngrade n e_down e_wb

/-- Def. (Lazy) Coherent Release WritesBack Other Entries in Vd when receiving a downgrade.
We assume it to be Lazy if it's Protocol Interface contains a Non-Coherent Weak Write. -/
structure Behaviour.coherentRelDowngradeWriteBackOthers (b : Behaviour n) (e_down : Event n) (pi : ProtocolInterface) : Prop where
  broadcastWBs : ∃ e_wb ∈ b, b.generateDowngradeToBroadcast n e_wb e_down
  -- Coherent Release is Lazy, because we have a Non-Coherent WeakWrite in the Protocol Interface
  cRelInPI : CoherentRelease ∈ pi --(e_down.interfaceMatchingProtocol n pi).val
  ncWeakWriteInPI : NonCoherentWeakWrite ∈ pi -- (e_down.interfaceMatchingProtocol n p_i).val

/-- Axiom 13. Release and Acquire Broadcast WriteBacks and Invalidations to other cache entries Axiom. -/
structure Behaviour.relAcqBroadcast : Prop where
  acquireInvals : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b, ∃ e_inval ∈ b, ∀ e_dir ∈ b, b.acqInvalOtherEntries n e_req e_inval e_dir init
  ncReleaseWBs : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b, ∃ e_wb ∈ b, ∀ e_dir ∈ b, b.relWriteBackOtherEntries n e_req e_wb e_dir init
  downgradeWB : ∀ b : Behaviour n, ∀ e_down ∈ b, ∀ pi : ProtocolInterface, b.coherentRelDowngradeWriteBackOthers n e_down pi

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

/- Defs describing where a Coherent Request's Directory Event that links the Request's data to the total order of Directory Entry Events. -/

def Event.isNcRelAcqWeakWrite : Event n → Prop
| e => e.isAcquire ∨ e.isNcRelease ∨ e.isNcWeakWrite
def Event.notNcRelAcqWeakWrite : Event n → Prop
| e => ¬ e.isNcRelAcqWeakWrite

def Event.isNcRelAcqWeakWriteRead : Event n → Prop
| e => e.isAcquire ∨ e.isNcRelease ∨ e.isNcWeakWrite ∨ e.isNcWeakRead
def Event.notNcRelAcqWeakWriteRead : Event n → Prop
| e => ¬ e.isNcRelAcqWeakWriteRead

def Event.isNcRelAcq : Event n → Prop
| e => e.isAcquire ∨ e.isNcRelease
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
| downgrade (hreq_is_down : e_req.down) (hreq_on_mrs_state : b.evictOnMRSState n init e_req) : Behaviour.reqMissingPerms b init e_req
| noPermsForNonNcRelAcqWeakWrite (hreq_not_down : ¬ e_req.down) (hreq_not_nc_rel_acq_ww : e_req.notNcRelAcqWeakWrite n) (hno_perms : b.eventOnStateNoPerms n init e_req) : Behaviour.reqMissingPerms b init e_req
| ncRelAcqWeakWriteNotOnCoherentState (hreq_not_down : ¬ e_req.down) (hreq_nc_rel_acq : e_req.isNcRelAcq) (hno_perms : b.acqRelWeakWriteNoPerms n init e_req) : Behaviour.reqMissingPerms b init e_req

structure Behaviour.reqHasNoPermsLeavesStateAtLeast (b : Behaviour n) (init : InitialSystemState n) (state : State) (e_req : Event n) : Prop where
  missingPerms : b.reqMissingPerms n init e_req
  notDown : ¬ e_req.down -- try something new with the condition?
  stateAfterAtLeast : b.reqLeavesStateAtLeast n e_req init state
  reqCache : e_req.isCacheEvent
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

noncomputable def Behaviour.reqMadeOnCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop :=
  (b.stateReqMadeOn n init e_req).c

structure Behaviour.reqHasPermsOnCoherentState (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  hasPerms : b.hasPerms n init e_req
  onCoherentState : b.reqMadeOnCoherentState n init e_req

structure Behaviour.reqHasPermsNotVd (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop where
  hasPerms : b.hasPerms n init e_req
  notOnVd : b.stateReqMadeOn n init e_req ≠ Vd
  -- coherentState : b.isReqMadeOnCoherentState n init e_req

/-- Wrapper structure Def. Prop on a Request Event `e_req`. The state it's made on is at least it's `Minimum Required State (MRS)`. -/
inductive Behaviour.reqHasPerms (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) : Prop
| hasPerms : e_req.isCoherent → b.hasPerms n init e_req → Behaviour.reqHasPerms b init e_req
| ncRelAcqWeakWriteHasCoherentPerms : e_req.isNcRelAcqWeakWrite → b.reqHasPermsOnCoherentState n init e_req → Behaviour.reqHasPerms b init e_req
| ncWeakReadHasPermsNotVd : e_req.isNcWeakRead → b.reqHasPermsNotVd n init e_req → Behaviour.reqHasPerms b init e_req

/-- Def. Structure stating a request event `e_req` has insufficient permissions, so it encapsulates directory event. -/
structure Behaviour.isReqHasNoPermsSoEncapDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  noPerms : b.reqMissingPerms n init e_req
  reqEncapDir : e_req.Encapsulates n e_dir

def Behaviour.predWithCorrespondingDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  (b.reqWithCorrespondDirLeavesStateAtLeast n e_pred init (b.stateBefore n (init.stateAt n e_req) e_req |>.cache))

def Behaviour.immBottomPredEncapCorrDirLeavesStateAtLeastReq (b : Behaviour n) (e_pred e_req : Event n) (init : InitialSystemState n) : Prop :=
  b.ImmediateBottomPredSatisfyingProp n e_pred e_req (b.predWithCorrespondingDirLeavesStateAtLeastReq n · e_req init)

def Behaviour.predHasNoPermsAndLeavesStateAtLeastReq (b : Behaviour n) (init : InitialSystemState n) (e_pred e_req : Event n) : Prop :=
  b.reqHasNoPermsLeavesStateAtLeast n init (e_req.req.MRS) e_pred

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
  notDown : ¬ e_req.down
  weakReq : e_req.isNcWeak
  reqOnOrAfterVd : (b.stateBefore n (init.stateAt n e_req) e_req).cache n = Vd ∨ (b.stateAfter n (init.stateAt n e_req) e_req).cache n = Vd
  reqCache : e_req.isCacheEvent

/-- Succeeding Request Event on Vd that accesses the Directory -/
structure Behaviour.reqOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop where
  stateBeforeAsVd : (b.stateBefore n (init.stateAt n e_req) e_req) = VdEntry n
  -- stateAfterNotVd : (b.stateAfter n (init.stateAt n e_req) e_req).cache ≠ Vd
  isRelAcqOrVdWB : e_req.isAcquire ∨ e_req.isNcRelease ∨ e_req.isCRelease ∨ e_req.isVdWriteBack
    ∨ e_req.isSCWrite ∨ e_req.isSCRead
  -- [NOTE]: Remebmer to use Axiom 6 to solve this.
  encapCorresponding : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir

def Behaviour.succOnVdWithCorrespondingDir (b : Behaviour n) (init : InitialSystemState n) (e_succ e_dir : Event n) : Prop :=
  b.reqOnVdWithCorrespondingDir n init e_succ e_dir

/-- Def. Prop. there exists an immediate bottom successor on Vd State, encapsulating a corresponding directory event. -/
def Behaviour.immBottomSuccOnVdEncapCorrDir (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop :=
  ∃ e_succ ∈ b, b.ImmediateBottomSuccSatisfyingProp n e_req e_succ (b.succOnVdWithCorrespondingDir n init · e_dir)

def Behaviour.stateBeforeAtLeast (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n) (state : State) : Prop :=
  state ≤ (b.stateBefore n (init.stateAt n e_req) e_req).cache

structure Behaviour.stateBeforeAndAfterAtLeast (b : Behaviour n) (init : InitialSystemState n) (e_inter e_req : Event n) : Prop where
  hinter_state_before_at_least : b.stateBeforeAtLeast n init e_inter e_req.req.MRS
  hinter_state_before_at_least_req_made_on_state : b.stateBeforeAtLeast n init e_inter (b.stateReqMadeOn n init e_req)
  hinter_leaves_state_at_least : b.reqLeavesStateAtLeast n e_inter init e_req.req.MRS
  hinter_leaves_state_at_least_red_made_on_state : b.reqLeavesStateAtLeast n e_inter init (b.stateReqMadeOn n init e_req)
  hinter_same_protocol : e_inter.sameProtocol n e_req

/-- Trying something new: separately state the cases of where -/
inductive Behaviour.dirAccessOfRequest (b : Behaviour n) (init : InitialSystemState n) (e_req e_dir : Event n) : Prop
| encapDir (hreq_missing_perms : b.reqMissingPerms n init e_req)
  (hencap_dir : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e_req) true e_req e_dir)
  : Behaviour.dirAccessOfRequest b init e_req e_dir
| orderBeforeDir
  (hreq_has_perms : b.reqHasPerms n init e_req)
  (hexists_pred_getting_perms : b.reqHasPermsSoDirPred n init e_req)
  (hpred_accesses_dir : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n hexists_pred_getting_perms.choose) true hexists_pred_getting_perms.choose e_dir)
  /- All requests between the predecessor and e_req `e_inter` that
     gets permissions (`hexists_pred_getting_perms.choose`) and `e_req` have permissions (like `b.reqHasPerms`),
     and leave the cache state with at least as much permissions (`b.reqLeavesStateAtLeast`  n `e_inter` init e_req.req.MRS).
     -/
  (hinter_leaves_state_at_least : ∀ e_inter ∈ b,
    e_inter.OrderedBetween n (hexists_pred_getting_perms.choose) e_req →
    b.stateBeforeAndAfterAtLeast n init e_inter e_req)
  (hpred_same_protocol : hexists_pred_getting_perms.choose.sameProtocol n e_req)
  (hnot_down : ¬ e_req.down)
  (hpred_produces_state_at_least_req_made_on_state : b.reqLeavesStateAtLeast n hexists_pred_getting_perms.choose init (b.stateReqMadeOn n init e_req))
  (hpred_not_down : ¬ hexists_pred_getting_perms.choose.down)
  : Behaviour.dirAccessOfRequest b init e_req e_dir
| orderAfterDir (hweak_read_on_vd : b.ncWeakReqOnVd n init e_req) (hsucc_encap_dir : b.immBottomSuccOnVdEncapCorrDir n init e_req e_dir)
  (hsucc_same_protocol : hsucc_encap_dir.choose.sameProtocol n e_req)
  (hnot_down : ¬ e_req.down)
  : Behaviour.dirAccessOfRequest b init e_req e_dir

-- Prove rf relation.

def Behaviour.dirAccessOfRequest.isDirEvent {b : Behaviour n} {init : InitialSystemState n} {e_req e_dir : Event n} (h : b.dirAccessOfRequest n init e_req e_dir) : e_dir.isDirectoryEvent :=
  match h with
  | .encapDir _ hencap_dir => hencap_dir.isDir
  | .orderBeforeDir _ _ hpred_accesses_dir _ _ _ _ _ => hpred_accesses_dir.isDir
  | .orderAfterDir _ hsucc_encap_dir _ _ => hsucc_encap_dir.choose_spec.right.satisfyP.encapCorresponding.isDir

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
  reqNcRelease : e_req.isNcRelease
  encapDirCorresponds : b.cacheEncapCorrespondingDirEvent n (init.stateAt n e_req) true e_req
  notDowngrade : ¬e_req.down
  /-
  dirWrite : e_dir.isWrite
  reqEncapDir : e_req.Encapsulates n e_dir-/

-- [NOTE] use `Behaviour.vdCacheEntryWriteBackLater` in the Vd succeeding Dir Events case
