import CompositionalProtocolProof.BehaviourRelationProofs

variable (n : Nat)

--------------- At Pg. 35 of Doc -------------------

def Event.reqAtGlobalCache (e_greq : Event n) (globalCid : Fin 2) : Prop := match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => fin_2 = globalCid
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

def Event.reqAtCorrespondingGCacheOfCDir (e_dir e_greq : Event n) : Prop :=
  match e_dir.protocol with
  | .cluster1 => e_greq.reqAtGlobalCache n 0
  | .cluster2 => e_greq.reqAtGlobalCache n 1
  | .global => False

structure Event.isGlobalCache (e_greq : Event n) : Prop where
  reqAtCache : e_greq.isCacheEvent
  reqGlobal : e_greq.protocol = .global

structure Event.isClusterDir (e_dir : Event n) : Prop where
  dirAtDir : e_dir.isDirectoryEvent
  dirCluster : e_dir.protocol = .cluster1 ∨ e_dir.protocol = .cluster2

/-- Def 2.43: Constraints of the Global Cache Event corresponding to a Cluster Directory Event. -/
structure Event.globalCacheEventOfClusterDir (e_greq e_dir : Event n) where
  reqGlobalCache : e_greq.isGlobalCache
  dirCluster : e_dir.isClusterDir
  gReq : e_dir.reqAtCorrespondingGCacheOfCDir n e_greq -- Global Cache Request corresponds to e_dir's cluster
  matchingOp : e_greq.req = ⟨⟨e_dir.req.val.rw, true, .SC⟩, by simp[Request.IsValid']⟩

structure Event.clusterDirEncapCorrespondingGlobalCache (e_dir e_greq : Event n) : Prop where
  encapGlobalCache : e_dir.Encapsulates n e_greq
  gReqOfCDir : e_greq.globalCacheEventOfClusterDir n e_dir

/-- (Shim) Axiom 15: Cluster Directory Events are translated to Request Events at the corresponding Cache in the Global Protocol. -/
structure Behaviour.Shim.ClusterDirEncapCorrespondingGlobalCache (b : Behaviour n) (e_dir : Event n) where
  dirCluster : e_dir.isClusterDir
  encapGlobalCache : ∃ e_greq ∈ b, Event.clusterDirEncapCorrespondingGlobalCache n e_greq e_dir

def Event.globalCacheCorrespondingCluster (e_greq e_cluster : Event n) : Prop := match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => match fin_2 with
        | 0 => e_cluster.protocol = .cluster1
        | 1 => e_cluster.protocol = .cluster2
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

/-- Def: State that an Event `e` is in the corresponding Cluster to a Global Cache Event `e_gReq` -/
def Event.correspondingClusterOfGlobalCache {α : Type} (e_greq : Event n) (e : α) (protocol : α → ProtocolInstance) : Prop :=
  match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => match fin_2 with
        | 0 => protocol e = .cluster1
        | 1 => protocol e = .cluster2
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

-- /-- (Shim) Axiom 16: Downgrade at a Global Cache is translated to a Cluster Directory access -/
