import CompositionalProtocolProof.CompoundSWMR
-- import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.BehaviourShim

import CompositionalProtocolProof.CompositionalProof.ProofBasic
-- import CompositionalProtocolProof.CompositionalProof.Lemma8CompoundEnforcesSWMR

variable (n : Nat)

/- TODO:
1. define an inductive stating the Compound Linearization event of a Cluster Cache Request Event
  is defined by two cases on what the Request's Linearization event is in the cluster:
  (a) a Cluster Directory Event `e_cdir`:
    Either `e_cdir` has permissions or not.
    If not:
      Then there exists a Global Linearization Event (Cache or Directory),
      stemming from Shim Axiom 15.
    If it does:
      `e_cdir` is the linearization Event.
  (b) a Cluster Cache Event:
    There exists a previous event that obtained permissions, and enforced (did not violate) Compound SWMR
    (True because of Lemma 8 -- all Cluster requests do not violate Compound SWMR).
   -/

/- Idea: All cluster request events have a linearization event, that correspond to the cluser directory some how.
Now state that all Cluster Directory events are connected to the global protocol directory (through the
Shim Axiom 15, and the linearziation event of a request the directory event is translated to by Axiom 15.)-/

/- Define Inductive for Lemma 9: Cluster Request Cache Event has a corresponding Global Directory Event. -/

/- Below: Def 2.48-/

def Behaviour.Shim.ClusterToGlobal.hasPerms (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (e_cdir_shim : Behaviour.Shim.ClusterToGlobal n b init e_cdir) : Prop :=
  match e_cdir_shim with
  | .noGlobalCache _ _ => True
  | .encapGlobalCache _ _ => False

def Behaviour.Shim.ClusterToGlobal.noPerms (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (e_cdir_shim : Behaviour.Shim.ClusterToGlobal n b init e_cdir) : Prop :=
  match e_cdir_shim with
  | .noGlobalCache _ _ => False
  | .encapGlobalCache _ _ => True

open scoped Classical in
noncomputable def Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent (b : Behaviour n) (e_cdir : Event n) : Event n :=
  by classical exact
  let e_gcache_finish_before_e_cdir := b.immediateFinishesBeforeAtGlobalCacheNotEncapEvents n e_cdir
  if h : Nonempty e_gcache_finish_before_e_cdir then h.some
  else panic! "Error: Expected this set of immediate finish-before event(s) to be nonempty!"

def Behaviour.compoundLinearizationEvent.OfGlobalCacheEvent {b : Behaviour n} {init : InitialSystemState n} {e_gcache : Event n}
  (gcache's_lin_event : b.linearizationEventOfRequest n init e_gcache) (e_glin : Event n) : Prop :=
  match gcache's_lin_event with
  | .dirLin dir_glin => e_glin = dir_glin.choose
  | .requestLin req_glin => e_glin = req_glin.choose

/- [TODO] Prepare a Lemma, to state the `latest_global_cache_event` before `e_cdir` comes from a set from
`Behaviour.getLatestGlobalCacheEventOfClusterDirectoryEvent` that is Singleton, if the Initial State is `I`, and `e_cdir` has Global Cache Permissions. -/
-- Sorry-lemma is in BehaviourShim.lean called `Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncapEvents_is_singleton`
def Behaviour.Shim.ClusterToGlobal.hasPerms.globalDirectoryEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir e_glin : Event n) (e_cdir_shim : Behaviour.Shim.ClusterToGlobal n b init e_cdir)
  : Prop :=
  match e_cdir_shim with
  | .noGlobalCache _ _ =>
    /- consider the immediatefinishesbefore global cache event, (subsingleton) there must be one (in this case because of the dir access);
    use it's linearization event. -/
    let latest_global_cache_event := b.getLatestGlobalCacheEventOfClusterDirectoryEvent n e_cdir
    ∃ gcache_linearization : b.linearizationEventOfRequest n init latest_global_cache_event,
    Behaviour.compoundLinearizationEvent.OfGlobalCacheEvent n gcache_linearization e_glin
  | .encapGlobalCache _ _ => False

open Classical in
def Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent (shimAxioms : ShimAxioms n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir e_glin : Event n) : Prop :=
  by classical exact
  if h : e_cdir.isDirectoryEvent then
    match (shimAxioms.clusterToGlobal b init e_cdir h) with
    | .noGlobalCache _ _ => False
    | .encapGlobalCache _ encap_gcache_req =>
      ∃ gcache_linearization : b.linearizationEventOfRequest n init encap_gcache_req.choose,
      Behaviour.compoundLinearizationEvent.OfGlobalCacheEvent n gcache_linearization e_glin
  else
    panic! "Error: Expected e_cdir to be a Directory Event."

inductive CompoundProtocol.clusterDirectoryCorrespondingGlobalDirectoryEvent (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (e_cdir_shim : Behaviour.Shim.ClusterToGlobal n b init e_cdir)
  (e_glin : Event n) : Prop
| previousGlobalCacheGotPerms -- (has_global_cache_perms : Behaviour.Shim.ClusterToGlobal.hasPerms n b init e_cdir e_cdir_shim)
  (cdir_previous_gcache : Behaviour.Shim.ClusterToGlobal.hasPerms.globalDirectoryEvent n b init e_cdir e_glin e_cdir_shim)
  : CompoundProtocol.clusterDirectoryCorrespondingGlobalDirectoryEvent b init e_cdir e_cdir_shim e_glin
| getGlobalCachePerms -- (no_global_cache_perms : Behaviour.Shim.ClusterToGlobal.hasPerms n b init e_cdir e_cdir_shim)
  : CompoundProtocol.clusterDirectoryCorrespondingGlobalDirectoryEvent b init e_cdir e_cdir_shim e_glin

-- A directory linearization event has a corresponding event in the global protocol
inductive CompoundProtocol.clusterDirectoryLinearizationEvent (shimAxioms : ShimAxioms n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir e_glin : Event n) : Prop
| previousGlobalCacheGotPerms
  (has_gcache_perms : e_cdir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_cdir).state)
  (e_cdir_is_e_glin : e_glin = e_cdir)
  : CompoundProtocol.clusterDirectoryLinearizationEvent shimAxioms b init e_cdir e_glin
| getGlobalCachePerms
  (no_gcache_perms : ¬ e_cdir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_cdir).state)
  (cdir_request_gcache : Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent n shimAxioms b init e_cdir e_glin)
  : CompoundProtocol.clusterDirectoryLinearizationEvent shimAxioms b init e_cdir e_glin

def Behaviour.reqLinearizesAtCache (b : Behaviour n) (init : InitialSystemState n) (e_creq : Event n) (e_creq_lin : b.linearizationEventOfRequest n init e_creq) : Prop :=
  match e_creq_lin with
  | .requestLin _ => True
  | .dirLin _ => False

def Behaviour.reqLinearizesAtDir (b : Behaviour n) (init : InitialSystemState n) (e_creq : Event n) (e_creq_lin : b.linearizationEventOfRequest n init e_creq) : Prop :=
  match e_creq_lin with
  | .requestLin _ => False
  | .dirLin _ => True

def CompoundProtocol.compoundLinearization.OfReqEncapDirAccess (shimAxioms : ShimAxioms n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq e_glin : Event n) (e_creq_lin : b.linearizationEventOfRequest n init e_creq) : Prop :=
  match e_creq_lin with
  | .requestLin _ => False
  | .dirLin lin_at_dir =>
    CompoundProtocol.clusterDirectoryLinearizationEvent
      n shimAxioms b init (lin_at_dir.choose_spec.right.reqLinearizeAtDir.choose) e_glin

/-- Definition 2.48 -/
inductive ClusterRequestLinearizationEvent (shimAxioms : ShimAxioms n)
  (b : Behaviour n) (init : InitialSystemState n) (e_creq : Event n) (e_creq_lin : b.linearizationEventOfRequest n init e_creq) : Prop
| clusterCacheLin (cluster_cache : e_creq.clusterNonProxyCacheEvent) (lin_at_cache : b.reqLinearizesAtCache n init e_creq e_creq_lin)
  (e_creq_is_e_glin : ∃ e_glin ∈ b, e_glin = e_creq)
  : ClusterRequestLinearizationEvent shimAxioms b init e_creq e_creq_lin
| clusterDirLin (cluster_cache : e_creq.clusterNonProxyCacheEvent) (lin_at_dir : b.reqLinearizesAtDir n init e_creq e_creq_lin)
  (e_glin_deeper : ∃ e_glin ∈ b, CompoundProtocol.compoundLinearization.OfReqEncapDirAccess n shimAxioms b init e_creq e_glin e_creq_lin)
  : ClusterRequestLinearizationEvent shimAxioms b init e_creq e_creq_lin


-- [ TODO ] Want to put Compound Linearization event into the Compound Protocol Def.
