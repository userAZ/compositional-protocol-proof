import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourRelationDefs

import CompositionalProtocolProof.CompositionalProof.Lemma5GlobalRequest

variable (n : Nat)

def Behaviour.dirEventCorrespondingToCacheEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir e : Event n) : Prop :=
  b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) true e_cdir e ∨
  b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) false e_cdir e

def Behaviour.dirEventNotCorrespondingToCacheEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir e : Event n) : Prop :=
  ¬ b.dirEventCorrespondingToCacheEvent n init e_cdir e

structure Behaviour.clusterDirFinishBeforeUnrelated (b : Behaviour n) (init : InitialSystemState n) (e_cdir e : Event n) : Prop where
  dirFinishBefore : e_cdir.finishesBefore n e
  unrelated : b.dirEventNotCorrespondingToCacheEvent n init e_cdir e

structure Behaviour.globalCacheFinishBeforeUnrelated (b : Behaviour n) (init : InitialSystemState n) (e_gcache e : Event n) : Prop where
  gCacheFinishBefore : e_gcache.finishesBefore n e
  unrelated : ∃ e_dir ∈ b, b.dirEventNotCorrespondingToCacheEvent n init e_dir e ∧ e_dir.Encapsulates n e_gcache

/- Don't need these
structure Behaviour.encapCorrespondingClusterDir (b : Behaviour n) (init : InitialSystemState n) (e_cdir e : Event n) : Prop where
  dirFinishBefore : e_cdir.Encapsulates n e
  unrelated : b.dirEventCorrespondingToCacheEvent n init e_cdir e

structure Behaviour.globalCacheFinishBefore (b : Behaviour n) (init : InitialSystemState n) (e_gcache e : Event n) : Prop where
  gCacheFinishBefore : e_gcache.finishesBefore n e
  unrelated : ∃ e_dir ∈ b, b.encapCorrespondingClusterDir n init e_dir e ∧ e_dir.Encapsulates n e_gcache
-/

/-- Lemma 4 : A Cluster Request Event leaves a protocol in Compound SWMR. -/
lemma Behaviour.cluster_request_enforces_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n)
  (cmp : CompoundProtocol n)
  -- (hcmp_swmr : CompoundSWMR.wrapper n)
  -- Initial or Current state just before Event `e` in Compound SWMR
  (e : Event n) (he_in_b : e ∈ b)
  (hpred_cdir_cmp_swmr : ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.clusterDirFinishBeforeUnrelated n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir)
  (hpred_gcache_cmp_swmr : ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBeforeUnrelated n init e_gcache e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e_gcache)
  : True
  -- ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.encapCorrespondingClusterDir n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir
  -- ∧
  -- ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBefore n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir
  := by
  sorry
