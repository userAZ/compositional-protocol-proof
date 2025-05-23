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

structure Occurence where
  oStart : ℕ
  oEnd : ℕ
  wellFormed : oStart < oEnd

class TypeEvent (e : Type) where
  o : e → Occurence
  oStart : e → TimeStart
  oEnd : e → TimeEnd

structure CacheEvent where
  o : Occurence
  oStart := o.oStart
  oEnd := o.oEnd
  wellFormed : oStart < oEnd
  r : Request
  rid : RequesterId
  cid : CacheId
  a : Addr
  d : Downgrade
  deid? : Option DirectoryEventId
  eid : EventId
instance : TypeEvent CacheEvent where
  o := CacheEvent.o
  oStart := CacheEvent.oStart
  oEnd := CacheEvent.oEnd

structure DirectoryEvent where
  o : Occurence
  oStart := o.oStart
  oEnd := o.oEnd
  wellFormed : oStart < oEnd
  r : Request
  dirS : DirectoryState
  did : DirectoryId
  a : Addr
  d : Downgrade
  eReq : CacheEvent
  deid : DirectoryEventId
instance : TypeEvent DirectoryEvent where
  o := DirectoryEvent.o
  oStart := DirectoryEvent.oStart
  oEnd := DirectoryEvent.oEnd

inductive Event
| cacheEvent : CacheEvent → Event
| directoryEvent : DirectoryEvent → Event

def Event.o (e : Event) : Occurence :=
  match e with
  | cacheEvent ce => ce.o
  | directoryEvent de => de.o
def Event.oStart (e : Event) : TimeStart := e.o.oStart
def Event.oEnd (e : Event) : TimeStart := e.o.oEnd

instance : TypeEvent Event where
  o := Event.o
  oStart := Event.oStart
  oEnd := Event.oEnd

-- def CacheEvent.requestEvent (e : CacheEvent) : Prop := e.cid = e.rid
-- def CacheEvent.sameAddress (e : CacheEvent) : Prop := e.cid = e.rid

-- abbrev CoherentRequest := {e : CacheEvent // e.r.coherent = true}
-- abbrev NonCoherentRequest := {e : CacheEvent // e.r.coherent = false}

def UniqueCacheEventIds (ce₁ ce₂ : CacheEvent) : Prop := ce₁.eid ≠ ce₂.eid
