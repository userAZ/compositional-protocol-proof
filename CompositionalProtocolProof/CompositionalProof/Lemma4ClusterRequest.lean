import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourHelpers
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.ProofBasicHelperLemmas

import CompositionalProtocolProof.CompositionalProof.Lemma5GlobalRequest

variable (n : Nat)

lemma CompoundProtocol.clusterDirectoryEvent.satisfies_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_cdir : Event n) (hcdir_in_b : e_gdown ∈ b)
  -- (hcdir : e_cdir.isClusterDirectory)
  -- (hcdir : e_cdir.notDowngrade)
  : CompoundSWMR n b init e_cdir := by
  sorry

/-- Lemma 4 : A Cluster Request Event leaves a protocol in Compound SWMR. -/
lemma Behaviour.cluster_request_enforces_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n)
  (cmp : CompoundProtocol n)
  (e : Event n) (he_in_b : e ∈ b)
  -- Initial or Current state just before Event `e` in Compound SWMR
  (hpred_cdir_cmp_swmr : ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.clusterDirFinishBeforeUnrelated n init e e_cdir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir)
  (hpred_gcache_cmp_swmr : ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBeforeUnrelated n init e e_gcache → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e_gcache)
  : b.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR n init e := by
  sorry
