import CompositionalProtocolProof.Protocol
import CompositionalProtocolProof.BehaviourShim

variable (n : Nat)

structure ShimAxioms where
  clusterToGlobal : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_dir : Event n, e_dir.isDirectoryEvent → Behaviour.Shim.ClusterToGlobal n b init e_dir
  globalToCluster : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ p : Protocol n, ∀ e_gdown ∈ b, Behaviour.Shim.GlobalToCluster n b init p e_gdown

structure CompoundProtocol where
  global : Protocol n
  cluster1 : Protocol n
  cluster2 : Protocol n
  shimAxioms : ShimAxioms n
  globalWellFormed : global.pi = .global
  globalSWMR : global.requests.isSWMR
  cluster1WellFormed : cluster1.pi = .cluster1
  cluster2WellFormed : cluster2.pi = .cluster2
