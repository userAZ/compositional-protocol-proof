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

-- Define inductive to describe the statement of Lemma 4.

/-- A Coherent Write Request in state that satisfies Compound SWMR before hand, satisfies Compound SWMR -/
inductive Behaviour.coherentWrite.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSW : Behaviour.coherentWrite.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events
| cacheMRVdVcI : Behaviour.coherentWrite.satisfiesCompoundSWMR b e

inductive Behaviour.coherentRead.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSWOrMR : Behaviour.coherentRead.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events
| cacheI : Behaviour.coherentRead.satisfiesCompoundSWMR b e

inductive Behaviour.ncReleaseWrite.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheVdVc : Behaviour.ncReleaseWrite.satisfiesCompoundSWMR b e
| cacheI : Behaviour.ncReleaseWrite.satisfiesCompoundSWMR b e

inductive Behaviour.ncWeakWrite.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSWVdVc : Behaviour.ncWeakWrite.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events
| cacheI : Behaviour.ncWeakWrite.satisfiesCompoundSWMR b e

inductive Behaviour.ncAcqRead.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSW : Behaviour.ncAcqRead.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events
| cacheVd : Behaviour.ncAcqRead.satisfiesCompoundSWMR b e
| cacheVcI : Behaviour.ncAcqRead.satisfiesCompoundSWMR b e

inductive Behaviour.ncWeakRead.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSWVdVc : Behaviour.ncWeakRead.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events
| cacheI : Behaviour.ncWeakRead.satisfiesCompoundSWMR b e

inductive Behaviour.vcWriteBack.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheVd : Behaviour.vcWriteBack.satisfiesCompoundSWMR b e
| cacheSWVcI : Behaviour.vcWriteBack.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events

inductive Behaviour.vcInvalidation.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSWVdVcI : Behaviour.vcInvalidation.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events

inductive Behaviour.evictSW.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheSW : Behaviour.evictSW.satisfiesCompoundSWMR b e
| cacheMRVdVcI : Behaviour.evictSW.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events

inductive Behaviour.evictMR.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cacheMR : Behaviour.evictMR.satisfiesCompoundSWMR b e
| cacheSWI : Behaviour.evictMR.satisfiesCompoundSWMR b e -- Trivial, no encap'ed events

/-- Any request satisfies Compound SWMR -/
inductive Behaviour.clusterRequest.satisfiesCompoundSWMR (b : Behaviour n) (e : Event n) : Prop
| cohWrite (hcoh_write : e.isCoherentWrite) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| cohRead (hcoh_read : e.isCoherentRead) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| ncRelWrite (hnc_rel_w : e.isNcRelease) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| ncWeakWrite (hnc_weak_w : e.isNcWeakWrite) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| ncAcqRead (hnc_acq_r : e.isAcquire) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| ncWeakRead (hnc_weak_r : e.isNcWeakRead) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| vdWriteBack (hvd_wb : e.isVdWriteBack) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| vcInval (hvc_inval : e.isVcInval) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| evictSW (hevict_sw : e.isEvictSW) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e
| evictMR (hevict_sw : e.isEvictMR) : Behaviour.clusterRequest.satisfiesCompoundSWMR b e

/- [TODO] In Lemma 4, add state restrictions;
Disallow specific Protocol Event state-before/after combinations depending on state.
This avoids those cases when reasoning through cases.
-/

/-- Lemma 4 : A Cluster Request Event leaves a protocol in Compound SWMR. -/
lemma Behaviour.cluster_request_enforces_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n)
  (cmp : CompoundProtocol n)
  -- (hcmp_swmr : CompoundSWMR.wrapper n)
  (e : Event n) (he_in_b : e ∈ b)
  -- Initial or Current state just before Event `e` in Compound SWMR
  (hpred_cdir_cmp_swmr : ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.clusterDirFinishBeforeUnrelated n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir)
  (hpred_gcache_cmp_swmr : ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBeforeUnrelated n init e_gcache e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e_gcache)
  : True
  -- ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.encapCorrespondingClusterDir n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir
  -- ∧
  -- ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBefore n init e_cdir e → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir
  := by
  sorry
