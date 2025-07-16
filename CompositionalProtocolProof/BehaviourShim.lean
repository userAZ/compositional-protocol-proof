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
structure Behaviour.globalCacheEventOfClusterDir (b : Behaviour n) (e_greq e_dir : Event n) where
  reqAtCache : e_greq.isCacheEvent
  dirAtDir : e_dir.isDirectoryEvent
  gReq : e_greq.reqAtCorrespondingGCacheOfCDir n e_dir -- Global Cache Request corresponds to e_dir's cluster
  matchingOp : e_greq.req = ⟨⟨e_dir.req.val.rw, true, .SC⟩, by simp[Request.IsValid']⟩
