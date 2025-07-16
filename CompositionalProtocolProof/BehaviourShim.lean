import CompositionalProtocolProof.BehaviourRelationProofs

variable (n : Nat)

--------------- At Pg. 35 of Doc -------------------

def Event.reqAtCorrespondingGCacheOfCDir (e_greq e_dir : Event n) : Prop :=
  match e_greq with
  | .cacheEvent ce => match e_dir with
    | .directoryEvent de => match de.pInst with
      | .cluster1 => match ce.cid with
        | .cache p_cache_inst =>
          match p_cache_inst with
          | .globalP fin_2 _ => fin_2 = 0
          | .cluster1 _ _ => False
          | .cluster2 _ _ => False
        | .proxy _ => False
      | .cluster2 => match ce.cid with
        | .cache p_cache_inst =>
          match p_cache_inst with
          | .globalP fin_2 _ => fin_2 = 1
          | .cluster1 _ _ => False
          | .cluster2 _ _ => False
        | .proxy _ => False
      | .global => False
    | .cacheEvent _ => False
  | .directoryEvent _ => False


/-- Def 2.43: Constraints of the Global Cache Event corresponding to a Cluster Directory Event. -/
structure Event.globalCacheEventOfClusterDir (e_greq e_dir : Event n) where
  reqAtCache : e_greq.isCacheEvent
  dirAtDir : e_dir.isDirectoryEvent
  gReq : e_greq.reqAtCorrespondingGCacheOfCDir n e_dir -- Global Cache Request corresponds to e_dir's cluster
  matchingOp : e_greq.req = ⟨⟨e_dir.req.val.rw, true, .SC⟩, by simp[Request.IsValid']⟩

def Event.isClusterDir (e_dir : Event n) : Prop := match e_dir with
  | .directoryEvent de => match de.pInst with
    | .cluster1 | .cluster2 => True
    | .global => False
  | .cacheEvent _ => False

structure Event.clusterDirEncapCorrespondingGlobalCache (e_dir e_greq : Event n) : Prop where
  encapGlobalCache : e_dir.Encapsulates n e_greq
  gReqOfCDir : e_greq.globalCacheEventOfClusterDir n e_dir

/-- Shim Axiom 15: Cluster Directory Events are translated to Request Events at the corresponding Cache in the Global Protocol. -/
structure Behaviour.clusterDirEncapCorrespondingGlobalCache (b : Behaviour n) (e_dir : Event n) where
  clusterDir : e_dir.isClusterDir
  encapGlobalCache : Event.clusterDirEncapCorrespondingGlobalCache n e_greq e_dir
