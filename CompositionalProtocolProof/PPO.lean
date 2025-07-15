import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.RequestPPOs

variable (n : Nat)

/-- Def 2.38: Is a Request Pair a PPO Pair. -/
def Event.isPPOPair (e₁ e₂ : Event n) : Prop := e₁.req.isPPOPair e₂.req

/-- Def 2.39: A Request Pair is in PPO -/
def Event.LinearizationOrder (b : Behaviour n) (init : InitialSystemState n)
  (e₁ e₂ : Event n) (lin : Behaviour.linearizationEventOfRequestWrapper n)
  : Prop :=
  match lin b init e₁, lin b init e₂ with
  | .requestLin e₁_lin_e, .requestLin e₂_lin_e
  | .dirLin e₁_lin_e, .requestLin e₂_lin_e
  | .requestLin e₁_lin_e, .dirLin e₂_lin_e
  | .dirLin e₁_lin_e, .dirLin e₂_lin_e => e₁_lin_e.choose.OrderedBefore n e₂_lin_e.choose

lemma Behaviour.events_are_in_ppo {b : Behaviour n} {init : InitialSystemState n} (e₁ e₂ : Event n) (lin : Behaviour.linearizationEventOfRequestWrapper n)
  : e₁.isPPOPair n e₂ → e₁.LinearizationOrder n b init e₂ lin := by
  sorry
