import CompositionalProtocolProof.Requests
import CompositionalProtocolProof.RequestPPOs
import CompositionalProtocolProof.States

variable (n : Nat)

abbrev RequesterId := CacheId
abbrev DirectoryId := ℕ
abbrev Addr := ℕ
abbrev Downgrade := Bool
abbrev EventId := ℕ
abbrev DirectoryEventId := ℕ

abbrev TimeStart := ℕ
abbrev TimeEnd := ℕ

structure Occurrence where
  oStart : ℕ
  oEnd : ℕ
  oWellFormed : oStart < oEnd
deriving DecidableEq, BEq

/-- Encapsulates relation on Occurrences. One event starts another event and waits for it to finish. -/
def Occurrence.Encapsulates (o₁ o₂ : Occurrence) : Prop := o₁.oStart < o₂.oStart ∧ o₂.oEnd < o₁.oEnd
/- Would be nice to have an Encapsulation class, with a nice infix symbol.
/-- `ENCAP α` is the typeclass which supports the notation `x ??? y` where `x y : α`.-/
class ENCAP (α : Type u) where
  /-- The encapsulation relation: `x ??? y` -/
  encap : α → α → Prop
/-- Abbreviation for `DecidableRel (· ??? · : α → α → Prop)`. -/
abbrev DecidableENCAP (α : Type u) [ENCAP α] := DecidableRel (ENCAP.encap : α → α → Prop)
-- instance Occurrence.instEncap : ENCAP Occurrence := { lt := Occurrence.lt}
-/

instance Occurrence.instDecidableEncap (o₁ o₂ : Occurrence) : Decidable (o₁.Encapsulates o₂) :=
  inferInstanceAs (Decidable (o₁.oStart < o₂.oStart ∧ o₂.oEnd < o₁.oEnd))

/-- Less-than (lt) relation on Occurrences,
i.e. two occurrences occur before one another in real-time -/
def Occurrence.lt (o₁ o₂ : Occurrence) : Prop := o₁.oEnd < o₂.oStart

instance Occurrence.instLT : LT Occurrence := { lt := Occurrence.lt}

instance Occurrence.instDecidableLT (o₁ o₂ : Occurrence) : Decidable (o₁ < o₂) :=
  inferInstanceAs (Decidable (o₁.oEnd < o₂.oStart))

class TypeEvent (e : Type) where
  o : e → Occurrence
  oStart : e → TimeStart
  oEnd : e → TimeEnd
  oWellFormed : (self : e) → (oStart self < oEnd self)

variable (n : Nat)

structure CacheEvent where
  o : Occurrence
  oStart := o.oStart
  oEnd := o.oEnd
  oWellFormed : oStart < oEnd
  req : ValidRequest
  rid : RequesterId n
  cid : CacheId n
  addr : Addr
  down : Downgrade
  deid? : Option DirectoryEventId
  eid : EventId
deriving DecidableEq, BEq
instance : TypeEvent (CacheEvent n) where
  o := CacheEvent.o
  oStart := CacheEvent.oStart
  oEnd := CacheEvent.oEnd
  oWellFormed := CacheEvent.oWellFormed

instance cacheEventInstBEq : BEq (CacheEvent n) where
  beq a b := a = b

instance cacheEventInstLawfulBEq : LawfulBEq (CacheEvent n) where
  eq_of_beq := by simp
  rfl := by simp

structure DirectoryEvent where
  o : Occurrence
  oStart := o.oStart
  oEnd := o.oEnd
  oWellFormed : oStart < oEnd
  req : ValidRequest
  dirS : (DirectoryState n)
  did : DirectoryId
  addr : Addr
  down : Downgrade
  eReq : (CacheEvent n)
  deid : DirectoryEventId
  pInst : ProtocolInstance
deriving DecidableEq, BEq
instance : TypeEvent (DirectoryEvent n) where
  o := DirectoryEvent.o
  oStart := DirectoryEvent.oStart
  oEnd := DirectoryEvent.oEnd
  oWellFormed := DirectoryEvent.oWellFormed

instance dirEventInstBEq : BEq (DirectoryEvent n) where
  beq a b := a = b

instance dirEventInstLawfulBEq : LawfulBEq (DirectoryEvent n) where
  eq_of_beq := by simp
  rfl := by simp

inductive Event
| cacheEvent : (CacheEvent n) → Event
| directoryEvent : (DirectoryEvent n) → Event
deriving DecidableEq, BEq

instance : Inhabited (Event n) where
  default := Event.cacheEvent (
    CacheEvent.mk
      (Occurrence.mk 0 1 (by simp))
      0
      1
      (by simp)
      (⟨⟨.r, false, .Weak⟩,by simp[Request.IsValid']⟩)
      (CacheId.proxy (.global) : CacheId n)
      (CacheId.proxy (.global) : CacheId n)
      0
      false
      none
      0
  )

@[simp]
instance eventInstBEq : BEq (Event n) where
  beq a b := a = b

@[simp]
instance eventInstLawfulBEq : LawfulBEq (Event n) where
  eq_of_beq := by simp
  rfl := by simp

def Event.o (e : Event n) : Occurrence := match e with
  | cacheEvent ce => ce.o
  | directoryEvent de => de.o

def Event.oStart (e : Event n) : TimeStart := match e with
  | cacheEvent ce => ce.oStart
  | directoryEvent de => de.oStart

def Event.oEnd (e : Event n) : TimeEnd := match e with
  | cacheEvent ce => ce.oEnd
  | directoryEvent de => de.oEnd

def Event.oWellFormed (e : Event n) : e.oStart < e.oEnd := match e with
  | cacheEvent ce => ce.oWellFormed
  | directoryEvent de => de.oWellFormed

instance : TypeEvent (Event n) where
  o := Event.o n
  oStart := Event.oStart n
  oEnd := Event.oEnd n
  oWellFormed := Event.oWellFormed n

def Event.req : Event n → ValidRequest
| .cacheEvent ce => ce.req
| .directoryEvent de => de.req
def Event.addr : Event n → Addr
| .cacheEvent ce => ce.addr
| .directoryEvent de => de.addr
def Event.atCid : Event n → CacheId n → Prop
| .cacheEvent ce, cid => ce.cid = cid
| .directoryEvent _, _ => false

inductive Struct
| directory : ProtocolInstance → Struct
| cache : CacheId n → Struct
deriving DecidableEq

def Struct.atCache : Struct n → Prop
| .cache _ => True
| .directory _ => False

def Event.struct : Event n → Struct n
| .directoryEvent de => .directory de.pInst
| .cacheEvent ce => .cache ce.cid

def CacheEvent.isFromSelf : CacheEvent n → Prop
| ce => ce.cid = ce.rid

structure CacheEvent.isEvict (ce : CacheEvent n) : Prop where
  selfRequester : ce.isFromSelf
  downgrade : ce.down

def Event.isEvict : Event n → Prop
| .cacheEvent ce => ce.isEvict
| .directoryEvent _ => true

structure CacheEvent.isEvictSW (ce : CacheEvent n) : Prop where
  evict : ce.isEvict
  coherentWrite : ce.req.isCoherentWrite

structure CacheEvent.isEvictMR (ce : CacheEvent n) : Prop where
  evict : ce.isEvict
  coherentWrite : ce.req.isCoherentRead

def Event.isEvictSW : Event n → Prop
| .cacheEvent ce => ce.isEvictSW
| .directoryEvent _ => true

def Event.isEvictMR : Event n → Prop
| .cacheEvent ce => ce.isEvictMR
| .directoryEvent _ => true

/-- The protocol instance of an event. -/
def Event.protocol (e_req : Event n) : ProtocolInstance := match e_req with
  | .cacheEvent ce => match ce.cid with
    | .proxy pi => pi
    | .cache pci => match pci with
      | .globalP _ => .global
      | .cluster1 _ => .cluster1
      | .cluster2 _ => .cluster2
  | .directoryEvent de => de.pInst

def Event.isCacheEvent : Event n → Prop
| .directoryEvent _ => false
| .cacheEvent _ => true

structure Event.isClusterCache (e_cache : Event n) : Prop where
  eAtCache : e_cache.isCacheEvent
  eCluster : e_cache.protocol = .cluster1 ∨ e_cache.protocol = .cluster2

def Event.isDirectoryEvent : Event n → Prop
| .directoryEvent _ => true
| .cacheEvent _ => false

structure Event.isClusterDir (e_dir : Event n) : Prop where
  dirAtDir : e_dir.isDirectoryEvent
  dirCluster : e_dir.protocol = .cluster1 ∨ e_dir.protocol = .cluster2

def Event.isCacheEventAtCid : Event n → CacheId n → Prop
| e, cid => match e with
  | .directoryEvent _ => false
  | .cacheEvent ce => ce.cid = cid

def Event.isCacheEventDowngrade : Event n → Prop
| .directoryEvent _ => false
| .cacheEvent ce => ce.down

def Event.isDirEventOfDirState : Event n → DirectoryState n → Prop
| e_dir, dir_state => match e_dir with
  | .directoryEvent de => de.dirS = dir_state
  | .cacheEvent _ => false

def Event.isCoherent : Event n → Prop
| .cacheEvent ce => ce.req.isCoherent
| .directoryEvent _ => false

def CacheEvent.isAcquire : CacheEvent n → Prop
| ce => ce.req.isAcquire

def Event.isAcquire : Event n → Prop
| .cacheEvent ce => ce.isAcquire
| .directoryEvent _ => false

def Event.isNonCoherent : Event n → Prop
| .cacheEvent ce => ¬ ce.req.val.coherent
| .directoryEvent _ => false

def Event.isWeak : Event n → Prop
| .cacheEvent ce => ce.req.val.consistency = .Weak
| .directoryEvent _ => false

def CacheEvent.isNonCoherent : CacheEvent n → Prop
| ce => ce.req.isNonCoherent

def CacheEvent.isWeak : CacheEvent n → Prop
| ce => ce.req.isWeak

def CacheEvent.isNcWeak : CacheEvent n → Prop
| ce => ce.isNonCoherent ∧ ce.isWeak

def Event.isNcWeak : Event n → Prop
| e => e.isNonCoherent ∧ e.isWeak

def CacheEvent.isNcWeakRead : CacheEvent n → Prop
| ce => ce.req.isNcWeakRead

def Event.isNcWeakRead : Event n → Prop
| .cacheEvent ce => ce.isNcWeakRead
| .directoryEvent _ => false

def Event.isNcWeakRead' : Event n → Prop
| e => e.req.isNcWeakRead

def CacheEvent.isNcWeakWrite : CacheEvent n → Prop
| ce => ce.req.isNcWeakWrite

def Event.isNcWeakWrite : Event n → Prop
| .cacheEvent ce => ce.isNcWeakWrite
| .directoryEvent _ => false

def Event.isCWeakWrite : Event n → Prop
| e => e.req.isCWeakWrite

def CacheEvent.isNcRelease : CacheEvent n → Prop
| ce => ce.req.isNcRelease

def Event.isNcRelease : Event n → Prop
| .cacheEvent ce => ce.isNcRelease
| .directoryEvent _ => false

def Event.isCRelease : Event n → Prop
| .cacheEvent ce => ce.req.val = ⟨.w, true, .Rel⟩
| .directoryEvent _ => false

def Event.isWrite : Event n → Prop
| .cacheEvent ce => ce.req.val.isWrite
| .directoryEvent _ => false

def Event.isCoherentWrite : Event n → Prop
| e => e.isCoherent ∧ e.isWrite

def Event.isRead : Event n → Prop
| .cacheEvent ce => ce.req.val.isRead
| .directoryEvent _ => false

def Event.isCoherentRead : Event n → Prop
| e => e.isCoherent ∧ e.isRead

structure CacheEvent.vcInval (e : CacheEvent n) : Prop where
  isDown : e.down
  isWeakRead : e.req.val = ⟨.r, false, .Weak⟩

structure CacheEvent.vdWriteBack (e : CacheEvent n) : Prop where
  isDown : e.down
  isWeakWrite : e.req.val = ⟨.w, false, .Weak⟩

def Event.isVcInval : Event n → Prop
| .cacheEvent ce => ce.vcInval
| .directoryEvent _ => false

def Event.isVdWriteBack : Event n → Prop
| .cacheEvent ce => ce.vdWriteBack
| .directoryEvent _ => false

def Event.down : Event n → Bool
| .cacheEvent ce => ce.down
| .directoryEvent de => de.down

noncomputable def CacheEvent.MRS : CacheEvent n → State
| ce => match ce.down with
  | false => ce.req.MRS
  | true => ⟨ce.req.val.rw.toPerms, ce.req.val.coherent⟩

noncomputable def Event.MRS : Event n → State
| e => match e.down with
  | false => e.req.MRS
  | true => ⟨e.req.val.rw.toPerms, e.req.val.coherent⟩

def Event.isDirWrite : Event n → Prop
| .cacheEvent _ => False
| .directoryEvent de => de.req.val.isWrite

def Event.isDirNotDown : Event n → Prop
| .cacheEvent _ => False
| .directoryEvent de => ¬ de.down

def DirectoryEvent.isEvict (de : DirectoryEvent n) : Prop := de.down

def Event.isDirEvict : Event n → Prop
| .cacheEvent _ => False
| .directoryEvent de => de.isEvict

def Event.isDirRead : Event n → Prop
| .cacheEvent _ => False
| .directoryEvent de => de.req.val.isRead

def Event.isDirMatchingRW : Event n → Event n → Prop
| .cacheEvent _ , _ => False
| .directoryEvent de, e => de.req.val.rw = e.req.val.rw

-- def CacheEvent.requestEvent (e : CacheEvent) : Prop := e.cid = e.rid
-- def CacheEvent.sameAddress (e : CacheEvent) : Prop := e.cid = e.rid

-- abbrev CoherentRequest := {e : CacheEvent // e.r.coherent = true}
-- abbrev NonCoherentRequest := {e : CacheEvent // e.r.coherent = false}

def Event.isSCWrite (e : Event n) : Prop := e.req.isSCWrite
def Event.isSCRead (e : Event n) : Prop := e.req.isSCRead

def UniqueCacheEventIds (ce₁ ce₂ : CacheEvent n) : Prop := ce₁.eid ≠ ce₂.eid

-- NOTE: TODO: Update this to use a Vector for CacheIds, and Addresses.
def InitialSystemState.stateAt (init : InitialSystemState n) (e : Event n) : EntryState n := match e with
  | .cacheEvent ce => Sum.inl <| init.cacheStates (ce.cid)
  | .directoryEvent de => Sum.inr <| init.directoryStates de.pInst

def InitialSystemState.stateAtCid (init : InitialSystemState n) (cid : CacheId n) : State := init.cacheStates (cid)

def InitialSystemState.stateAtStruct (init : InitialSystemState n) (struct : Struct n) : State :=
  match struct with
  | .directory pi => (init.directoryStates pi).toState
  | .cache cid => init.cacheStates cid

def InitialSystemState.entryStateAtStruct (init : InitialSystemState n) (struct : Struct n) : EntryState n :=
  match struct with
  | .directory pi => Sum.inr (init.directoryStates pi)
  | .cache cid => Sum.inl (init.cacheStates cid)

/-- Events are at the same Cache. -/
def Event.sameCid (e₁ e₂ : Event n) : Prop :=
  match e₁, e₂ with
  | .cacheEvent ce₁, .cacheEvent ce₂ => ce₁.cid = ce₂.cid
  | _, _ => False

def Event.cid (e : Event n) : CacheId n := match e with
  | .cacheEvent ce => ce.cid
  | .directoryEvent _ => panic! "Error: getting an Event's Cid, but was given a DirectoryEvent?"

def Event.clusterNonProxyCacheEvent (e : Event n) : Prop := match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy _ => False
    | .cache pci => match pci with
      | .cluster1 _ => True
      | .cluster2 _ => True
      | .globalP _ => False
  | .directoryEvent _ => False

/-- Def 2.38: Is a Request Pair a PPO Pair. -/
structure Event.isPPOPair (e₁ e₂ : Event n) : Prop where
  requestPPO : e₁.req.isPPOPair e₂.req
  sameCache : e₁.sameCid n e₂

/-- Handle a relation on a (cache) event's Cid and another Cid. -/
def Event.propOnBinaryCid (e : Event n) (p : CacheId n → CacheId n → Prop) : CacheId n → Prop := match e with
  | .cacheEvent ce => p ce.cid
  | .directoryEvent _ => (λ _ => False)

def Event.differentCidInSameProtocol (e : Event n) (cid : CacheId n) : Prop :=
  e.propOnBinaryCid n (CacheId.differentIdSameProtocol n) cid

def Event.propOnUnitaryCid (e : Event n) (p : CacheId n → Prop) : Prop := match e with
  | .cacheEvent ce => p ce.cid
  | .directoryEvent _ => False

def Event.eventOfDifferentCidInSameProtocol (e₁ e₂ : Event n) : Prop :=
  e₂.propOnUnitaryCid n (e₁.propOnBinaryCid n (CacheId.differentIdSameProtocol n))

/-- State that an event `e_greq` is a Global Cache (not Proxy) Event. -/
def Event.reqAtGlobalCache (e_greq : Event n) : Prop := match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP _ => True
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

def DirectoryEvent.sameRequester (de₁ de₂ : DirectoryEvent n) : Prop := de₁.eReq.cid = de₂.eReq.cid

def Event.directoryEventSameRequester (e₁ e₂ : Event n) : Prop := match e₁, e₂ with
| .directoryEvent de₁, .directoryEvent de₂ => de₁.sameRequester n de₂
| _, _ => False

/-- Def: From the protocol request interfaces of the 3 protocols (`p_i`), state the
  protocol interface (set of requests) Event `e` is a part of. -/
def Event.interfaceMatchingProtocol (e : Event n) (p_i : Protocol.interface) : ProtocolInterface :=
  match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy pi => match pi with
      | .global => p_i.global_pi -- panic! "We do not consider proxy caches in the global protocol."
      | .cluster1 => p_i.cluster1_pi
      | .cluster2 => p_i.cluster2_pi
    | .cache pci => match pci with
      | .globalP _ => p_i.global_pi
      | .cluster1 _ => p_i.cluster1_pi
      | .cluster2 _ => p_i.cluster2_pi
  | .directoryEvent de => match de.pInst with
    | .global => p_i.global_pi
    | .cluster1 => p_i.cluster1_pi
    | .cluster2 => p_i.cluster2_pi
