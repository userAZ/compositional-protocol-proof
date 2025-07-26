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

lemma Set.toOption_singleton {α} {s : Set α} (hsingleton : s.IsSingleton) : ∃ e, s = {e} → s.toOption = some e := by
  use hsingleton.choose
  intro hs_singleton
  simp only [toOption, Option.dite_none_right_eq_some,]
  have hs_nonempty' : Nonempty s := by
    simp []
    use hsingleton.choose
    simp[Set.eq_singleton_iff_unique_mem] at hs_singleton
    obtain ⟨hsingle_in_s, helem_of_s⟩ := hs_singleton
    simp[hsingle_in_s]
  use hs_nonempty'
  obtain ⟨_,hxs_eq_singleton⟩ := Set.eq_singleton_iff_unique_mem.mp hs_singleton
  simp
  apply hxs_eq_singleton
  . case h.intro.a =>
    apply Nonempty.some_mem
    . case h =>
      use hsingleton.choose

lemma Set.toOption_singleton' {α} {s : Set α} (e : α) (hsingleton : s = {e}) : s.toOption = some e := by sorry

noncomputable def Behaviour.eventToState (b : Behaviour n) (init : InitialSystemState n) (e? : Option (Event n)) (struct : Struct n) : State :=
  match e? with
  | .none => init.stateAtStruct n struct
  | .some e => (b.stateAfter n (init.stateAt n e) e).state

/-- Project the (Subsingleton) set of events at CacheId `cid` that's the immediate Finishes Before event of an Event `e`.
(although the title is "events", the set is Subsingleton, as shown by Lemma
`Behaviour.immediateFinishesBeforeEvents_is_subsingleton` in Behaviours.lean) -/
def Behaviour.eventsEndingImmediatelyBeforeEvent (b : Behaviour n) (e : Event n) (cid : CacheId n) :=
  {e' ∈ b.eventsEndingImmediatelyBefore n e | e.atCid n cid}

def ProtocolInstance.cidSetAtProtocolInstance (pi : ProtocolInstance) := {c : CacheId n | c.atProtocol n pi}

lemma ProtocolInstance.cidSetAtProtocolInstance_is_finite (pi : ProtocolInstance)
  : (pi.cidSetAtProtocolInstance n).Finite := by
  simp[cidSetAtProtocolInstance]
  simp[Set.Finite,]
  simp [Subtype.finite]

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_finset (pi : ProtocolInstance) : Finset (CacheId n) :=
  Set.Finite.toFinset (ProtocolInstance.cidSetAtProtocolInstance_is_finite n pi)

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_list (pi : ProtocolInstance) : List (CacheId n) :=
  (pi.cidSetAtProtocolInstance_to_finset n).toList

/-- Assumption: The set of events from projecting the events at `cid` is singleton. -/
noncomputable def Behaviour.stateOfSubsingletonCidSet
  (b : Behaviour n) (init : InitialSystemState n) (cid : CacheId n) (s : Set (Event n)) : State :=
  b.eventToState n init {e ∈ s | e.atCid n cid}.toOption (Struct.cache cid)

/-- List of Cache States After Events immediately finishing before an Event `e`, including State After `e`. -/
noncomputable def Behaviour.cidSetAtProtocolInstance.cacheStatesFinishBeforeEvent
  (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : List State :=
  let events_ending_immediately_before_event_ends := b.eventsEndingImmediatelyBefore n e
  let cid_list := pi.cidSetAtProtocolInstance_to_list n
  cid_list.map (b.stateOfSubsingletonCidSet n init · events_ending_immediately_before_event_ends)

structure List.swmr (l : List State) : Prop where
  swExclusiveMR : ¬ (SW ∈ l ∧ MR ∈ l) -- Cannot have both SW and MR at the same time
  exclusiveSW : l.count SW ≤ 1 -- Can only have 1 exclusive writer

def SWMR (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : Prop :=
  (Behaviour.cidSetAtProtocolInstance.cacheStatesFinishBeforeEvent n b init pi e).swmr

def SWMR.wrapper : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ pi : ProtocolInstance, ∀ e ∈ b, SWMR n b init pi e
