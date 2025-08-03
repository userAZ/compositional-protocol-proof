import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.RequestPPOs

variable (n : Nat)

noncomputable def Behaviour.linearizationEventOfRequest.linearizationEvent {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
  (e_lin : Behaviour.linearizationEventOfRequest n b init e) : Event n := match e_lin with
  | .requestLin lin_e => lin_e.choose
  | .dirLin lin_e => lin_e.choose

/-- Def 2.39: A Request Pair is in PPO -/
def Event.LinearizationOrder (b : Behaviour n) (init : InitialSystemState n)
  (e₁ e₂ : Event n) (lin : Behaviour.linearizationEventOfRequestWrapper n)
  : Prop :=
  let e_lin₁ := lin b init e₁ |>.linearizationEvent
  let e_lin₂ := lin b init e₂ |>.linearizationEvent
  e_lin₁.OrderedBefore n e_lin₂
  ∨ ∀ e₃ ∈ b,
    match lin b init e₃ with
    | .requestLin _ => False -- Cannot have another request `e₃` linearize with cache permissions
    | .dirLin e_lin₃ =>
      e_lin₂.orderedBeforeToSameEntry n e_lin₃.choose → e_lin₁.lazyLinearizationOrder n e_lin₂ e_lin₃.choose

/-- Lemma 10 -/
lemma Behaviour.events_are_in_ppo {b : Behaviour n} {init : InitialSystemState n}
  (e₁ e₂ : Event n) (hsame_protocol : e₁.sameProtocol n e₂) (lin : Behaviour.linearizationEventOfRequestWrapper n)
  : e₁.isPPOPair n e₂ → e₁.LinearizationOrder n b init e₂ lin := by
  sorry
