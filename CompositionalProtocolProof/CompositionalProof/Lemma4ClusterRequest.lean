import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourRelationDefs

import CompositionalProtocolProof.CompositionalProof.Lemma5GlobalRequest

variable (n : Nat)

def Behaviour.dirEventCorrespondingToCacheEvent (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop :=
  b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) true e e_cdir ∨
  b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) false e e_cdir

def Behaviour.dirEventNotCorrespondingToCacheEvent (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop :=
  ¬ b.dirEventCorrespondingToCacheEvent n init e e_cdir

structure Behaviour.clusterDirFinishBeforeUnrelated (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop where
  dirFinishBefore : e_cdir.finishesBefore n e
  unrelated : b.dirEventNotCorrespondingToCacheEvent n init e e_cdir

structure Behaviour.globalCacheFinishBeforeUnrelated (b : Behaviour n) (init : InitialSystemState n) (e e_gcache : Event n) : Prop where
  gCacheFinishBefore : e_gcache.finishesBefore n e
  unrelated : ∃ e_dir ∈ b, b.dirEventNotCorrespondingToCacheEvent n init e_dir e ∧ e_dir.Encapsulates n e_gcache

/- Old approach -- Model all outcomes as inductive for the Goal. vs new approach -- all events `e` enforce "CompoundeSWMR" as a goal

structure Behaviour.encapCorrespondingClusterDir (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop where
  dirFinishBefore : e_cdir.Encapsulates n e
  unrelated : b.dirEventCorrespondingToCacheEvent n init e e_cdir

structure Behaviour.globalCacheFinishBefore (b : Behaviour n) (init : InitialSystemState n) (e e_gcache : Event n) : Prop where
  gCacheFinishBefore : e_gcache.finishesBefore n e
  unrelated : ∃ e_dir ∈ b, b.encapCorrespondingClusterDir n init e e_dir ∧ e_dir.Encapsulates n e_gcache

-- Define inductive to describe the statement of Lemma 4.

/-- An Event `e` satisfies Compound SWMR if all events `e_other` finishing before `e` finishes satisfy
compound SWMR. -/
def CompoundSWMR.event_satisfies_cmp_swmr : Prop :=
  ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e ∈ b, ∀ e_other ∈ b,
  e_other.finishesBefore n e → CompoundSWMR.wrapper n

def Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.encapCorrespondingClusterDir n init e e_cdir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir

/- In Lemma 5 file: (so that we may prove this property modularly in Lemma 5.) Import and use in the above. -- Each of these are
  small inductives, stating 2 cases: an event either encapsulates another event, or doesn't (include a negative proof, to show
  a contradiction in the negative case, and stop the proof there).
`e_gcache` may encapsulate another Event `e_gdown`
-/
--[NOTE] don't technically need this specifically for Global cache events.
inductive Behaviour.globalCacheEvent.mayAccessGlobalDir  (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop
-- |

/- State a Cluster Request Event `e` encaps a corresponding directory event `e_dir`.
`e_dir` may encap another Event `e_gcache` (if e_dir needs gcache perms, otherwise there exists no additional encap'd `e_gcache`),
 -/
structure Behaviour.clusterDirEvent.encapGlobalCacheEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir e_gcache : Event n) : Prop where
  cDirEncapGCache : Event.clusterDirEncapCorrespondingGlobalCache n e_cdir e_gcache
  -- [NOTE] `e_gcache` satisfies `Compound SWMR` technically not needed; more worried about `e_gdown`
  gCacheSatisfiesCmpSWMR : Behaviour.globalCacheEvent.satisfiesCompoundSWMR n b init e_gcache
  gCacheMayEncapGDir : Behaviour.globalCacheEvent.mayAccessGlobalDir n b init e_gcache

def Behaviour.existsTransitiveGlobalCacheAccessOfDirEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) : Prop :=
  ∃ e_gcache ∈ b, Behaviour.clusterDirEvent.encapGlobalCacheEvent n b init e_cdir e_gcache

inductive Behaviour.coherentWrite.noPermsDirAccess (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop
| accessGCache (no_global_perms : b.clusterDirNoPermsInGlobalCache n init e_cdir)
  /- [NOTE] State that there exists an e_gcache, and it may or may not encap another. -/
  /- *[TODO]* Update this to say, if the Directory Event is a Cluster Directory Event, then... it may encapsulate a Global Cache Event -/
  (exists_gcache : b.existsTransitiveGlobalCacheAccessOfDirEvent n init e_cdir)
  : Behaviour.coherentWrite.noPermsDirAccess b init e e_cdir
| noGCache (has_global_perms : b.clusterDirHasPermsInGlobalCache n init e_cdir)
  (no_gcache : ¬b.existsGlobalCacheAccessOfDirEvent n e_cdir)
  : Behaviour.coherentWrite.noPermsDirAccess b init e e_cdir

/-[NOTE] Remember to update Axiom 6 to include the `Negative`. i.e. on SW state,
  There does not exist a corresponding directory event that a req encapsulates.
  i.e.for all Events `e` in `b`, it isn't a corresponding Directory Event. -/

/-- A Coherent Write Request in state that satisfies Compound SWMR before hand, satisfies Compound SWMR -/
inductive Behaviour.coherentWrite.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSW (madeOnSW : b.eventOnStateHasPerms n init e)
  /- [TODO] If this is a Cluster Cache Request Event, then define -/
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  /- [TODO] also means that we vacuously satisfy "all Global Cache events enforce Compound SWMR" -/
  : Behaviour.coherentWrite.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events
| cacheMRVdVcI (madeOnMRVdVcI : b.eventOnStateNoPerms n init e)
  /- Things to state:
    (a) encap'd corresponding dir event satisfies Cmp SWMR
    (b) Forall events `e_gdown` in b such that `e_gdown` is related to `e` through a Transitive Relation (TransGen),
    `e_gdown` satisfies Cmp SWMR.
    [NOTE] This requires updating Axioms to specify encapsulated events are in the same Protocol. -/
  : Behaviour.coherentWrite.satisfiesCompoundSWMR b init e

inductive Behaviour.coherentRead.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSWOrMR (madeOnSW : b.eventOnStateHasPerms n init e)
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.coherentRead.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events
| cacheI (madeOnI : b.eventOnStateNoPerms n init e)
  : Behaviour.coherentRead.satisfiesCompoundSWMR b init e

inductive Behaviour.ncReleaseWrite.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheVdVc (madeOnVdVc : b.cacheStateMadeOn n init e ∈ [Vd, Vc])
  : Behaviour.ncReleaseWrite.satisfiesCompoundSWMR b init e
| cacheI (madeOnI : b.cacheStateMadeOn n init e = I)
  : Behaviour.ncReleaseWrite.satisfiesCompoundSWMR b init e

inductive Behaviour.ncWeakWrite.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSWVdVc (madeOnSWVdVc : b.cacheStateMadeOn n init e ∈ [SW, Vd, Vc])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.ncWeakWrite.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events
| cacheI (madeOnI : b.cacheStateMadeOn n init e = I)
  : Behaviour.ncWeakWrite.satisfiesCompoundSWMR b init e

inductive Behaviour.ncAcqRead.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSW (madeOnSW : b.cacheStateMadeOn n init e = SW)
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.ncAcqRead.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events
| cacheVd (madeOnVd : b.cacheStateMadeOn n init e = Vd)
  : Behaviour.ncAcqRead.satisfiesCompoundSWMR b init e
| cacheVcI (madeOnVcI : b.cacheStateMadeOn n init e ∈ [Vc, I])
  : Behaviour.ncAcqRead.satisfiesCompoundSWMR b init e

inductive Behaviour.ncWeakRead.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSWVdVc (madeOnSWVdVc : b.cacheStateMadeOn n init e ∈ [SW, Vd, Vc])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.ncWeakRead.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events
| cacheI (madeOnI : b.cacheStateMadeOn n init e = I)
  : Behaviour.ncWeakRead.satisfiesCompoundSWMR b init e

inductive Behaviour.vcWriteBack.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheVd (madeOnVd : b.cacheStateMadeOn n init e = Vd)
  : Behaviour.vcWriteBack.satisfiesCompoundSWMR b init e
| cacheSWVcI (madeOnSWVcI : b.cacheStateMadeOn n init e ∈ [SW, Vc, I])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.vcWriteBack.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events

inductive Behaviour.vcInvalidation.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSWVdVcI (madeOnSWVdVcI : b.cacheStateMadeOn n init e ∈ [SW, Vd, Vc, I])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.vcInvalidation.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events

inductive Behaviour.evictSW.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheSW (madeOnSW : b.cacheStateMadeOn n init e = SW)
  : Behaviour.evictSW.satisfiesCompoundSWMR b init e
| cacheMRVdVcI (madeOnMRVdVcI : b.cacheStateMadeOn n init e ∈ [MR, Vd, Vc, I])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.evictSW.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events

inductive Behaviour.evictMR.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cacheMR (madeOnMR : b.cacheStateMadeOn n init e = MR)
  : Behaviour.evictMR.satisfiesCompoundSWMR b init e
| cacheSWI (madeOnSWI : b.cacheStateMadeOn n init e ∈ [SW, I])
  (vacuous_satisfy_cmp_swmr : Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR n b init e)
  : Behaviour.evictMR.satisfiesCompoundSWMR b init e -- Trivial, no encap'ed events

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
