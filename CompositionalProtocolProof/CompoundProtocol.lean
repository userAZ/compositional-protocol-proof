import CompositionalProtocolProof.Protocol
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization

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
  linearizationOfEvent : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req : Event n,
    Behaviour.linearizationEventOfRequest n b init e_req
  compoundLinearizationEvent : Behaviour.clusterRequestLinearizationEvent.wrapper n
  noConsistencyOfAcqOnSw : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e₁ ∈ b, ∀ e₂ ∈ b,
    e₁.req.isAcquire → e₁.isPPOPair n e₂ → (∃ e_cmplin ∈ b,
      Behaviour.eventCompoundLinearizes.atCache n b init e₁ e_cmplin (linearizationOfEvent b init e₁)) → False
  weakWriteAndNonCoherentRelCannotLinearizeAtCache : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e₁ ∈ b, ∀ e₂ ∈ b,
    e₁.req.isNcRelease ∧ e₂.req.isWeak ∨ e₁.req.isWeak ∧ e₂.req.isNcRelease → (∃ e ∈ [e₁, e₂], (∃ e_cmplin ∈ b,
    Behaviour.eventCompoundLinearizes.atCache n b init e e_cmplin (linearizationOfEvent b init e)) ) → False

def CompoundProtocol.globalCidToProtocol (cmp : CompoundProtocol n) (g_cid : Fin 2) : Protocol n := match g_cid with
  | 0 => cmp.cluster1
  | 1 => cmp.cluster2

def CompoundProtocol.clusterProtocolCorrespondingToGlobalProtocol (cmp : CompoundProtocol n) (e_greq : Event n) : Protocol n :=
  cmp.globalCidToProtocol n (e_greq.globalCacheEventCid n)

/- ----------------------------------------------- -/
