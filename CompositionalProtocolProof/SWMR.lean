import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

-- [NOTE] Probably want a lemma about subsingleton input
open scoped Classical in
noncomputable def Set.toOption {α} (s : Set α) : Option (α) :=
  by classical exact
  if h : Nonempty s then some h.some
  else none

noncomputable def Behaviour.eventToState (b : Behaviour n) (init : InitialSystemState n) (e? : Option (Event n)) (cid : CacheId n) : State :=
  match e? with
  | .none => init.stateAtCid n cid
  | .some e => (b.stateAfter n (init.stateAt n e) e).cache

/-- Project the (Subsingleton) set of events at CacheId `cid` that's the immediate Finishes Before event of an Event `e`.
(although the title is "events", the set is Subsingleton, as shown by Lemma
`Behaviour.immediateFinishesBeforeEvents_is_subsingleton` in Behaviours.lean) -/
def Behaviour.eventsEndingImmediatelyBeforeEvent (b : Behaviour n) (e : Event n) (cid : CacheId n) :=
  {e' ∈ b.eventsEndingImmediatelyBefore n e | e.atCid n cid}

-- [NOTE] may need to prove finite
def ProtocolInstance.cidSetAtProtocolInstance (pi : ProtocolInstance) := {c : CacheId n | c.atProtocol n pi}

def ProtocolInstance.cidSetAtProtocolInstance_is_finite (pi : ProtocolInstance)
  : (pi.cidSetAtProtocolInstance n).Finite := by
  simp[cidSetAtProtocolInstance]
  simp[Set.Finite,]
  constructor
  . case a =>
    -- simp[CacheId.atProtocol]
    sorry
  . case n =>
    sorry

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_finset (pi : ProtocolInstance) : Finset (CacheId n) :=
  Set.Finite.toFinset (ProtocolInstance.cidSetAtProtocolInstance_is_finite n pi)

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_list (pi : ProtocolInstance) : List (CacheId n) :=
  (pi.cidSetAtProtocolInstance_to_finset n).toList

/-- Assumption: The set of events from projecting the events at `cid` is singleton. -/
noncomputable def Behaviour.stateOfSubsingletonCidSet
  (b : Behaviour n) (init : InitialSystemState n) (cid : CacheId n) (s : Set (Event n)) : State :=
  b.eventToState n init {e ∈ s | e.atCid n cid}.toOption cid

-- [NOTE] may need to prove this is Set.Countable
def Behaviour.stateOfEventSet (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : Set State :=
  let events_ending_immediately_before_event_ends := b.eventsEndingImmediatelyBefore n e
  let cids := pi.cidSetAtProtocolInstance n
  cids.image (b.stateOfSubsingletonCidSet n init · events_ending_immediately_before_event_ends)

-- Try: State that projections of SW state and MR state from `stateOfEventSet` satisfy SWMR

def SWMR (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : Prop :=
  let cache_states := b.stateOfEventSet n init pi e
  sorry


/- Want to state: the state of all caches in a protocol is SWMR
(SW ≤ 1, exclusive or, MR ≥ 0, SW = 1 → MR = 0, and MR > 0 → SW = 0) -/
