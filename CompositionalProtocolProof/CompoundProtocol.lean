import CompositionalProtocolProof.Protocol
import CompositionalProtocolProof.BehaviourShim

variable (n : Nat)

structure CompoundProtocol where
  global : Protocol n
  cluster1 : Protocol n
  cluster2 : Protocol n
  shimAxioms : ShimAxioms n
  globalWellFormed : global.pi = .global
  globalSWMR : global.requests.isSWMR
  cluster1WellFormed : cluster1.pi = .cluster1
  cluster2WellFormed : cluster2.pi = .cluster2
  linearizationOfEvent : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b,
    Behaviour.linearizationEventOfRequest n b init e_req
