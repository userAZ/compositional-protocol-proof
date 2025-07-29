import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.Behaviours
import CompositionalProtocolProof.SWMR
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.Protocol

variable (n : Nat)

/-- Directory Event Has permissions. -/
def Behaviour.dirEventStateLeGlobalCacheState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop :=
  e_dir.req.MRS ≤ b.globalCacheStateOfDirEventState n init e_dir

/-- Def 2.47,a: Compound SWMR: directory event has permissions in global cache. -/
structure CompoundSWMR.stateAfterClusterDirEventLeGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) : Prop where
  dirEvent : e_cdir.isClusterDir
  stateAfterLeGlobalCache : b.dirEventStateLeGlobalCacheState n init e_cdir

/-- The corresponding directory has state permissions ≤ the state after a global cache event -/
def Behaviour.dirEventStateLeGlobalCacheState' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop :=
  b.latestDirectoryStateOfGlobalCache n init e_gcache ≤ (b.stateAfter n (init.stateAt n e_gcache) e_gcache).cache

/-- Def 2.47,b: Compound SWMR: global cache downgrade events (or all global cache events) have corresponding state in
the directory that's ≤ global cache event. (i.e. corresponding dir event state finish immediately before global cache event
is ≤ the state after the global cache event) -/
structure CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop where
  gCache : e_gcache.isGlobalCache
  stateAfterLeGlobalCache : b.dirEventStateLeGlobalCacheState' n init e_gcache

def Behaviour.clusterDirEvent.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  e.isClusterDir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e

def Behaviour.globalCacheEvent.satisfiesCompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  e.isGlobalCache → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e

inductive CompoundSWMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop
| cDir (cdir_satisfies_cmp_swmr : Behaviour.clusterDirEvent.satisfiesCompoundSWMR n b init e) : CompoundSWMR b init e
| gCache (gcache_satisfies_cmp_swmr : Behaviour.globalCacheEvent.satisfiesCompoundSWMR n b init e) : CompoundSWMR b init e

def CompoundSWMR.wrapper (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isClusterDir ∨ e.isGlobalCache → CompoundSWMR n b init e

------------------------------------------------------------------

/- State at Cluster Directory corresponding to Global Cache `e_gdown` is in Compound SWMR state
before considering `e_gdown`'s translation events to the Cluster Directory. -/

/-- The corresponding directory has state permissions ≤ the state after a global cache event -/
def Behaviour.dirEventState.Before.LeGlobalCacheState' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop :=
  Behaviour.latestDirectoryState.Before.GlobalCache n b init e_gcache ≤ (b.stateBefore n (init.stateAt n e_gcache) e_gcache).cache

structure CompoundSWMR.stateAfterClusterDirEvent.Before.LeGlobalCache' (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : Prop where
  gCache : e_gcache.isGlobalCache
  stateAfterLeGlobalCache : Behaviour.dirEventState.Before.LeGlobalCacheState' n b init e_gcache

def Behaviour.stateBefore.globalCacheEvent.satisfiesCompoundSWMR' (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  e.isGlobalCache → CompoundSWMR.stateAfterClusterDirEvent.Before.LeGlobalCache' n b init e
