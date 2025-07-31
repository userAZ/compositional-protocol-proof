import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourRelationDefs

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
  unrelated : ∀ e_dir ∈ b, b.dirEventNotCorrespondingToCacheEvent n init e_dir e ∧ e_dir.Encapsulates n e_gcache

-- [Simpler] Alternate approach: Define at a higher level of abstraction, simplify the approach
-- Modularly state smaller relations between events (ex. Cache (Request) Event encapsulating a Directory Event.)
-- inductive Behaviour.cacheRequestEvent.mayAccessDir (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
-- | cacheAccessDir () (Behaviour.clusterRequest.allEncapDirEventSatisfiesCmpSWMR) :

structure Event.isGlobalDir (e_dir : Event n) : Prop where
  dirAtDir : e_dir.isDirectoryEvent
  dirGlobal : e_dir.protocol = .global

-- [NOTE] could swap out the `∀ e ∈ b, ...` with `(∃ e ∈ b) → ...`, might be simpler? or not.

def Behaviour.globalDowngradeEvent.fwdOnSW.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e_gcache e_gdir e_gdown : Event n) : Prop :=
  b.requestDowngradePrevOwner n init e_gcache e_gdir e_gdown → CompoundSWMR n b init e_gdown

def Behaviour.globalDowngradeEvent.fwdOnMR.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e_gcache e_gdir e_gdown : Event n) : Prop :=
  ∀ s ∈ (b.directoryStateMadeOn n init e_gdir).CurrentSharers, s ≠ e_gcache.cid →
    Event.swDowngradeSharersParameters n e_gcache e_gdown s → CompoundSWMR n b init e_gdown

inductive Behaviour.globalDowngradeEvent.fwdWrite.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e_gcache e_gdir e_gdown : Event n) : Prop
| dirWasSW (on_sw : (b.directoryStateMadeOn n init e_gdir).toState = SW)
  (downgrade_owner : Behaviour.globalDowngradeEvent.fwdOnSW.satisfiesCompoundSWMR n b init e_gcache e_gdir e_gdown)
  : Behaviour.globalDowngradeEvent.fwdWrite.satisfiesCompoundSWMR b init e_gcache e_gdir e_gdown
| dirWasMR (on_mr : (b.directoryStateMadeOn n init e_gdir).toState = MR)
  (downgrade_sharers : Behaviour.globalDowngradeEvent.fwdOnMR.satisfiesCompoundSWMR n b init e_gcache e_gdir e_gdown)
  : Behaviour.globalDowngradeEvent.fwdWrite.satisfiesCompoundSWMR b init e_gcache e_gdir e_gdown

inductive Behaviour.globalDowngradeEvent.fwdSWOrMR.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e_gcache e_gdir e_gdown : Event n) : Prop
| fwdSWDown (down : e_gdown.down) (fwd_sw : e_gdown.isSCWrite) (global_down_satisfies_cmp_swmr : Behaviour.globalDowngradeEvent.fwdWrite.satisfiesCompoundSWMR n b init e_gcache e_gdir e_gdown)
  : Behaviour.globalDowngradeEvent.fwdSWOrMR.satisfiesCompoundSWMR b init e_gcache e_gdir e_gdown
| fwdMRDown (down : e_gdown.down) (fwd_mr : e_gdown.isSCRead) (global_down_satisfies_cmp_swmr : Behaviour.globalDowngradeEvent.fwdOnSW.satisfiesCompoundSWMR n b init e_gcache e_gdir e_gdown)
  : Behaviour.globalDowngradeEvent.fwdSWOrMR.satisfiesCompoundSWMR b init e_gcache e_gdir e_gdown

/-- Goal for Lemma 4. Split for Lemma 6/7. -/
def Behaviour.globalDowngradeEvent.satisfiesCompoundSMWR (b : Behaviour n) (init : InitialSystemState n) (e_gcache e_gdir : Event n) : Prop :=
    ∀ e_gdown ∈ b, e_gdown.isGlobalDowngrade → Behaviour.globalDowngradeEvent.fwdSWOrMR.satisfiesCompoundSWMR n b init e_gcache e_gdir e_gdown

/-- Goal for Lemma 4. Split for Lemma 5. -/
def Behaviour.globalCacheEvent.satisfiesCompoundSMWR (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) : Prop :=
    ∀ e_gcache ∈ b, e_gcache.isGlobalCache → e_cdir.clusterDirEncapCorrespondingGlobalCache n e_gcache →
    ∀ e_gdir ∈ b, e_gdir.isGlobalDir → b.dirEventCorrespondingToCacheEvent n init e_gcache e_gdir →
    Behaviour.globalDowngradeEvent.satisfiesCompoundSMWR n b init e_gcache e_gdir

/-- Goal for Lemma 4. Stating a corresponding Cluster Directory Event `e_cdir` satisfies Compound SWMR. -/
structure Behaviour.correspondingClusterDirSatisfyCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e e_cdir : Event n) : Prop where
  clusterDirSatisfiesCmpSWMR : CompoundSWMR n b init e_cdir
  globalCacheSatisfiesCmpSWMR : Behaviour.globalCacheEvent.satisfiesCompoundSMWR n b init e_cdir

/-- Goal for Lemma 4. This is the prop used in the top level Goal. For any Cluster Event `e`, any Directory Event `e_cdir` that corresponds to `e`,
`e_cdir` must satisfy `CompoundSWMR`, and any global downgrades transitively related through it must also satisfy `CompoundSWMR` -/
def Behaviour.allCorrespondingGlobalDowngradeSatisfyCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.dirEventCorrespondingToCacheEvent n init e e_cdir →
    b.correspondingClusterDirSatisfyCompoundSWMR n init e e_cdir

structure Behaviour.ncRelOnIEncapTwoDirEvents (b : Behaviour n) (init : InitialSystemState n) (e e_cdir_vc e_cdir_vd : Event n) : Prop where
  vcClusterDir : e_cdir_vc.isClusterDir
  vdClusterDir : e_cdir_vd.isClusterDir
  vcCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) false e e_cdir_vc
  vdCorresponds : b.cacheEncapsulatesCorrespondingDirEvent n (init.stateAt n e) true e e_cdir_vd

structure Behaviour.ncRelDirEventsSatisfyCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e e_cdir_vc e_cdir_vd : Event n) : Prop where
  vcSatisfyCmpSWMR : b.correspondingClusterDirSatisfyCompoundSWMR n init e e_cdir_vc
  vdSatisfyCmpSWMR : b.correspondingClusterDirSatisfyCompoundSWMR n init e e_cdir_vd

def Behaviour.ncRelOnICorrespondingClusterDirSatisfyCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  ∃ e_cdir_vc ∈ b, ∃ e_cdir_vd ∈ b, b.ncRelOnIEncapTwoDirEvents n init e e_cdir_vc e_cdir_vd →
    b.ncRelDirEventsSatisfyCompoundSWMR n init e e_cdir_vc e_cdir_vd

/-- Goal for Lemma 4. Top level goal. -/
inductive Behaviour.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR  (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| ncRelOnI (isNcRel : e.isNcRelease) (onI : b.cacheStateMadeOn n init e = I) (cluster_cache_not_proxy : e.clusterNonProxyCacheEvent n)
  (encapTwoDirs : b.ncRelOnICorrespondingClusterDirSatisfyCompoundSWMR n init e)
  : Behaviour.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR b init e
| ncRelNotOnI (isNcRel : e.isNcRelease) (notOnI : b.cacheStateMadeOn n init e ≠ I) (cluster_cache_not_proxy : e.clusterNonProxyCacheEvent n)
  (any_dir_satisfies_cmp_swmr : b.allCorrespondingGlobalDowngradeSatisfyCompoundSWMR n init e)
  : Behaviour.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR b init e
| notNcRel (isNotNcRel : ¬ e.isNcRelease) (cluster_cache_not_proxy : e.clusterNonProxyCacheEvent n)
  (any_dir_satisfies_cmp_swmr : b.allCorrespondingGlobalDowngradeSatisfyCompoundSWMR n init e)
  : Behaviour.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR b init e

structure Behaviour.allCorresponding.ClusterDirAndGlobalDowngrade.satisfyCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop where

/- Defs firsted used in Lemma 6/7 -/

def CompoundProtocol.globalCidToProtocol (cmp : CompoundProtocol n) (g_cid : Fin 2) : Protocol n := match g_cid with
  | 0 => cmp.cluster1
  | 1 => cmp.cluster2

def ProtocolCacheInstance.globalCacheEventCid (pci : ProtocolCacheInstance n) : Fin 2 := match pci with
  | .globalP fin_2 => fin_2
  | .cluster1 _ => 3 -- Attempt to be smart; Using a value that's not a Fin 2 should produce an error.
  | .cluster2 _ => 3 -- panic! "Error: Expected a Global Cache Event, not a Cluster Cache Event!"

def CacheEvent.globalCacheEventCid (ce_greq : CacheEvent n) : Fin 2 := match ce_greq.cid with
  | .cache p_cache_inst => p_cache_inst.globalCacheEventCid
  | .proxy _ => 3

def Event.globalCacheEventCid (e_greq : Event n) : Fin 2 := match e_greq with
  | .cacheEvent ce => ce.globalCacheEventCid
  | .directoryEvent _ => 3

def CompoundProtocol.clusterProtocolCorrespondingToGlobalProtocol (cmp : CompoundProtocol n) (e_greq : Event n) : Protocol n :=
  cmp.globalCidToProtocol n (e_greq.globalCacheEventCid n)


-- Not sure if I want to use the below defs. remove later

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
