import CompositionalProtocolProof.Behaviours
import Mathlib

lemma Behaviour.state_after_eq_succeeding_state_before' {n l} {init : EntryState n} {e_req : Event n}
  : List.stateAfter n (l ++ [e_req]) init =
    Event.SucceedingState n e_req (List.stateAfter n l init) := by
  induction l generalizing init with
  | nil =>
    simp[List.stateAfter]
  | cons head tail ih =>
    rw[List.stateAfter.eq_def]
    rw[List.stateAfter.eq_def]
    simp
    apply ih

lemma Behaviour.state_after_eq_succeeding_state_before (b : Behaviour n) (init : InitialSystemState n) (e_req : Event n)
  : (stateAfter n b (InitialSystemState.stateAt n init e_req) e_req) = e_req.SucceedingState n (stateBefore n b (InitialSystemState.stateAt n init e_req) e_req)
  := by
  apply state_after_eq_succeeding_state_before'
