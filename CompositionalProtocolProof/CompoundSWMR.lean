import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.Behaviours
import CompositionalProtocolProof.SWMR
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.Protocol

variable (n : Nat)

noncomputable def Behaviour.globalCacheStateOfDirEventState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : State :=
  let global_cache_cid := (e_dir.globalCidCorrespondingToClusterDir n)
  let global_event_imm_finish_before_dir := (b.immediateFinishesBeforeAtGlobalCacheEvents n e_dir)
  b.stateOfSubsingletonGlobalEventSet n init global_cache_cid global_event_imm_finish_before_dir

/-- Directory Event Has permissions. -/
def Behaviour.dirEventStateLeGlobalCacheState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop :=
  e_dir.req.MRS ≤ b.globalCacheStateOfDirEventState n init e_dir

/-- Def 2.47,a: Compound SWMR: directory event has permissions in global cache. -/
structure CompoundSWMR.stateAfterClusterDirEventLeGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop where
  dirEvent : e_dir.isDirectoryEvent
  stateAfterLeGlobalCache : b.dirEventStateLeGlobalCacheState n init e_dir

/- Def 2.47,b: Compound SWMR: global cache downgrade events (or all global cache events) have corresponding state in
the directory that's ≤ global cache event. (i.e. corresponding dir event state finish immediately before global cache event
is ≤ the state after the global cache event) -/

-- def CompoundSWMR.wrapper
