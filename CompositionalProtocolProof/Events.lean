import CompositionalProtocolProof.Requests
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
deriving DecidableEq

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

inductive Event
| cacheEvent : (CacheEvent n) → Event
| directoryEvent : (DirectoryEvent n) → Event
deriving DecidableEq, BEq

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
| directory : Struct
| cache : CacheId n → Struct
deriving DecidableEq

def Event.struct : Event n → Struct n
| .directoryEvent _ => .directory
| .cacheEvent ce => .cache ce.cid

def Event.isCacheEvent : Event n → Prop
| .directoryEvent _ => true
| .cacheEvent _ => false

def Event.isDirectoryEvent : Event n → Prop
| .directoryEvent _ => true
| .cacheEvent _ => false

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

def Event.isAcquire : Event n → Prop
| .cacheEvent ce => ce.req.val = ⟨.r, false, .Acq⟩
| .directoryEvent _ => false

def Event.isNCRelease : Event n → Prop
| .cacheEvent ce => ce.req.val = ⟨.w, false, .Rel⟩
| .directoryEvent _ => false

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

-- def CacheEvent.requestEvent (e : CacheEvent) : Prop := e.cid = e.rid
-- def CacheEvent.sameAddress (e : CacheEvent) : Prop := e.cid = e.rid

-- abbrev CoherentRequest := {e : CacheEvent // e.r.coherent = true}
-- abbrev NonCoherentRequest := {e : CacheEvent // e.r.coherent = false}

def UniqueCacheEventIds (ce₁ ce₂ : CacheEvent n) : Prop := ce₁.eid ≠ ce₂.eid

-- NOTE: TODO: Update this to use a Vector for CacheIds, and Addresses.
def InitialSystemState.stateAt (init : InitialSystemState n) (e : Event n) : EntryState n := match e with
  | .cacheEvent ce => Sum.inl <| init.cacheStates (ce.cid)
  | .directoryEvent de => Sum.inr <| init.directoryStates de.pInst
