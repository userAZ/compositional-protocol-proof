import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

/- Want to state: the state of all caches in a protocol is SWMR
(SW ≤ 1, exclusive or, MR ≥ 0, SW = 1 → MR = 0, and MR > 0 → SW = 0) -/

/-
def SWMR (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e

def SWMR' (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e
-/
