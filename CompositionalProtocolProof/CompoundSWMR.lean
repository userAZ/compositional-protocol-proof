import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.Behaviours
import CompositionalProtocolProof.SWMR
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.Protocol

variable (n : Nat)

noncomputable def Behaviour.globalCacheStateOfDirEventState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : State :=
  let global_cache_cid := Struct.cache (e_dir.globalCidCorrespondingToClusterDir n)
  let global_event_imm_finish_before_dir := (b.immediateFinishesBeforeAtGlobalCacheEvents n e_dir)
  b.stateOfSubsingletonEventSet n init global_cache_cid global_event_imm_finish_before_dir

/-- Directory Event Has permissions. -/
def Behaviour.dirEventStateLeGlobalCacheState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop :=
  e_dir.req.MRS ≤ b.globalCacheStateOfDirEventState n init e_dir

/-- Def 2.47,a: Compound SWMR: directory event has permissions in global cache. -/
structure CompoundSWMR.stateAfterClusterDirEventLeGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) : Prop where
  dirEvent : e_cdir.isClusterDir
  stateAfterLeGlobalCache : b.dirEventStateLeGlobalCacheState n init e_cdir

noncomputable def Behaviour.latestDirectoryStateOfGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : State :=
  let cluster_dir_struct := Struct.directory (e_gcache.clusterDirProtocolCorrespondingToGlobalCache n)
  let cluster_dir_imm_finish_before_global := b.immediateFinishesBeforeAtClusterDirectoryEvents n e_gcache
  b.stateOfSubsingletonEventSet n init cluster_dir_struct cluster_dir_imm_finish_before_global

/-- The corresponding directory has state permissions ≤ the state after a global cache event -/
def Behaviour.dirEventStateLeGlobalCacheState' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop :=
  b.latestDirectoryStateOfGlobalCache n init e_gcache ≤ b.cacheStateMadeOn n init e_gcache

/-- Def 2.47,b: Compound SWMR: global cache downgrade events (or all global cache events) have corresponding state in
the directory that's ≤ global cache event. (i.e. corresponding dir event state finish immediately before global cache event
is ≤ the state after the global cache event) -/
structure CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop where
  gCache : e_gcache.isGlobalCache
  stateAfterLeGlobalCache : b.dirEventStateLeGlobalCacheState n init e_gcache

def Behaviour.clusterDirEvent.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  e.isClusterDir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e

def Behaviour.globalCacheEvent.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  e.isGlobalCache → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e

inductive CompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cDir (cdir_satisfies_cmp_swmr : Behaviour.clusterDirEvent.satisfiesCompoundSWMR n b init e) : CompoundSWMR b init e
| gCache (gcache_satisfies_cmp_swmr : Behaviour.globalCacheEvent.satisfiesCompoundSWMR n b init e) : CompoundSWMR b init e

def CompoundSWMR.wrapper (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isClusterDir ∨ e.isGlobalCache → CompoundSWMR n b init e
