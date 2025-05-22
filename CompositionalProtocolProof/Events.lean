import CompositionalProtocolProof.Requests
import CompositionalProtocolProof.States

abbrev RequesterId := CacheId
abbrev DirectoryId := ℕ
abbrev Addr := ℕ
abbrev Downgrade := Bool
abbrev EventId := ℕ
abbrev DirectoryEventId := ℕ

structure Occurence where
  oStart : ℕ
  oEnd : ℕ
  wellFormed : oStart < oEnd

structure CacheEvent where
  o : Occurence
  r : Request
  rid : RequesterId
  cid : CacheId
  a : Addr
  d : Downgrade
  deid? : Option DirectoryEventId
  eid : EventId

structure DirectoryEvent where
  o : Occurence
  r : Request
  dirS : DirectoryState
  rid : RequesterId
  did : DirectoryId
  a : Addr
  d : Downgrade
  eReq : CacheEvent
  deid : DirectoryEventId

def UniqueCacheEventIds (ce₁ ce₂ : CacheEvent) : Prop := ce₁.eid ≠ ce₂.eid
