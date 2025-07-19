import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

-- [NOTE] Probably want a lemma about subsingleton input
open scoped Classical in
noncomputable def Set.toOption {α} (s : Set α) : Option (α) :=
  by classical exact
  if h : s = ∅ then
    none
  else
    have nonempty : Nonempty s := by
      simp[← Set.nonempty_iff_ne_empty'] at h
      simp[h]
    Option.some (Classical.choice nonempty).val

noncomputable def Behaviour.eventToState (b : Behaviour n) (init : InitialSystemState n) (e? : Option (Event n)) (cid : CacheId n) : State :=
  match e? with
  | .none => init.stateAtCid n cid
  | .some e => (b.stateAfter n (init.stateAt n e) e).cache

/-- (although the title is "events", the set is Subsingleton) -/
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

def SWMR (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, ∀ cid : CacheId n, e.differentCidInSameProtocol n cid → sorry

/- Want to state: the state of all caches in a protocol is SWMR
(SW ≤ 1, exclusive or, MR ≥ 0, SW = 1 → MR = 0, and MR > 0 → SW = 0) -/

/-
def SWMR (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e

def SWMR' (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e
-/
