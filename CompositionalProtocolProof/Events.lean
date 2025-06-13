import CompositionalProtocolProof.Requests
import CompositionalProtocolProof.States

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

structure CacheEvent where
  o : Occurrence
  oStart := o.oStart
  oEnd := o.oEnd
  oWellFormed : oStart < oEnd
  req : ValidRequest
  rid : RequesterId
  cid : CacheId
  addr : Addr
  down : Downgrade
  deid? : Option DirectoryEventId
  eid : EventId
deriving DecidableEq, BEq
instance : TypeEvent CacheEvent where
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
  dirS : DirectoryState
  did : DirectoryId
  addr : Addr
  down : Downgrade
  eReq : CacheEvent
  deid : DirectoryEventId
deriving DecidableEq, BEq
instance : TypeEvent DirectoryEvent where
  o := DirectoryEvent.o
  oStart := DirectoryEvent.oStart
  oEnd := DirectoryEvent.oEnd
  oWellFormed := DirectoryEvent.oWellFormed

inductive Event
| cacheEvent : CacheEvent → Event
| directoryEvent : DirectoryEvent → Event
deriving DecidableEq, BEq

def Event.o (e : Event) : Occurrence := match e with
  | cacheEvent ce => ce.o
  | directoryEvent de => de.o

def Event.oStart (e : Event) : TimeStart := match e with
  | cacheEvent ce => ce.oStart
  | directoryEvent de => de.oStart

def Event.oEnd (e : Event) : TimeEnd := match e with
  | cacheEvent ce => ce.oEnd
  | directoryEvent de => de.oEnd

def Event.oWellFormed (e : Event) : e.oStart < e.oEnd := match e with
  | cacheEvent ce => ce.oWellFormed
  | directoryEvent de => de.oWellFormed

instance : TypeEvent Event where
  o := Event.o
  oStart := Event.oStart
  oEnd := Event.oEnd
  oWellFormed := Event.oWellFormed

def Event.req : Event → ValidRequest
| .cacheEvent ce => ce.req
| .directoryEvent de => de.req
def Event.addr : Event → Addr
| .cacheEvent ce => ce.addr
| .directoryEvent de => de.addr
def Event.atCid : Event → CacheId → Prop
| .cacheEvent ce, cid => ce.cid = cid
| .directoryEvent _, _ => false

inductive Struct
| directory : Struct
| cache : CacheId → Struct
deriving DecidableEq

def Event.struct : Event → Struct
| .directoryEvent _ => .directory
| .cacheEvent ce => .cache ce.cid

def Event.isDirectoryEvent : Event → Prop
| .directoryEvent _ => true
| .cacheEvent _ => false

def Event.isCacheEventAtCid : Event → CacheId → Prop
| e, cid => match e with
  | .directoryEvent _ => false
  | .cacheEvent ce => ce.cid = cid

def Event.isCacheEventDowngrade : Event → Prop
| .directoryEvent _ => false
| .cacheEvent ce => ce.down

-- def CacheEvent.requestEvent (e : CacheEvent) : Prop := e.cid = e.rid
-- def CacheEvent.sameAddress (e : CacheEvent) : Prop := e.cid = e.rid

-- abbrev CoherentRequest := {e : CacheEvent // e.r.coherent = true}
-- abbrev NonCoherentRequest := {e : CacheEvent // e.r.coherent = false}

def UniqueCacheEventIds (ce₁ ce₂ : CacheEvent) : Prop := ce₁.eid ≠ ce₂.eid
