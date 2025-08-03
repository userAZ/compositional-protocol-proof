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

def CompoundProtocol.globalCidToProtocol (cmp : CompoundProtocol n) (g_cid : Fin 2) : Protocol n := match g_cid with
  | 0 => cmp.cluster1
  | 1 => cmp.cluster2

def CompoundProtocol.clusterProtocolCorrespondingToGlobalProtocol (cmp : CompoundProtocol n) (e_greq : Event n) : Protocol n :=
  cmp.globalCidToProtocol n (e_greq.globalCacheEventCid n)

/- ----------------------------------------------- -/
