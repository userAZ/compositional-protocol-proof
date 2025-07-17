import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.Protocol

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

def Protocol.hasCoherentWrite (p : Protocol n) : Prop := ∃ req ∈ p.requests, req.isCoherentWrite
def Protocol.hasCoherentRead (p : Protocol n) : Prop := ∃ req ∈ p.requests, req.isCoherentRead

def Protocol.hasCoherentWriteAndRead (p : Protocol n) : Prop := p.hasCoherentWrite ∧ p.hasCoherentRead

def Protocol.noCoherentWrite (p : Protocol n) : Prop := ∀ req ∈ p.requests, ¬ req.isCoherentWrite
def Protocol.noCoherentRead (p : Protocol n) : Prop := ∀ req ∈ p.requests, ¬ req.isCoherentRead

def Protocol.noCoherentWriteOrRead (p : Protocol n) : Prop := p.noCoherentWrite ∧ p.noCoherentRead

structure Event.isGlobalDowngrade (e : Event n) : Prop where
  isGlobal : e.isGlobalCache
  isDown : e.down

structure Event.isSCWriteGlobalDowngrade (e : Event n) : Prop where
  isGlobalDown : e.isGlobalCache
  isSCWrite : e.isSCWrite

structure Event.isSCReadGlobalDowngrade (e : Event n) : Prop where
  isGlobalDown : e.isGlobalCache
  isSCWrite : e.isSCRead

/-- A cache event is made on state SW or MR -/
def Behaviour.madeOnSWOrMR (b : Behaviour n) (init : InitialSystemState n) (e : Event n) : Prop :=
  b.stateMadeOn n init e = SW ∨ b.stateMadeOn n init e = MR

def Event.atProxy (e : Event n) : Prop := match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy _ => True
    | .cache _ => False
  | .directoryEvent _ => False

/-- A translated event from the shim `e_shim_trans` goes to the Proxy Cache, for the same address,
in the Cluster corresponding to requesting downgrade. -/
structure Event.Shim.globalToClusterCacheEvent (e_gdown e_shim_trans : Event n) : Prop where
  sameAddr : e_gdown.sameAddr n e_shim_trans
  atCorrCluster : e_gdown.correspondingClusterOfGlobalCache n e_shim_trans (Event.protocol n)
  proxyTrans : e_shim_trans.atProxy n

/-- A translated Global SC Write Downgrade contains a SC Write (Get M) -/
structure Event.Shim.bothCoherentWriteReadTranslateWriteFwd (e_gdown e_shim_coh_write : Event n) : Prop where
  atCorrClusterProxy : Event.Shim.globalToClusterCacheEvent n e_gdown e_shim_coh_write
  scWrite : e_shim_coh_write.isSCWrite
  notDown : ¬ e_shim_coh_write.down

/-- A translated Global SC Write Downgrade contains a SC Write Evict (Put M) -/
structure Event.Shim.bothCoherentWriteReadTranslateWriteEvict (e_gdown e_shim_coh_evict : Event n) : Prop where
  atCorrClusterProxy : Event.Shim.globalToClusterCacheEvent n e_gdown e_shim_coh_evict
  scWrite : e_shim_coh_evict.isSCWrite
  down : e_shim_coh_evict.down

/-- A global SC write downgrade encapsulates a Coherent Write `e_w` and Evict `e_v` (`e_w` orderedBefore `e_v`) in the corresponding Cluster's Proxy Cache. -/
structure Behaviour.encapCorrespondingGetSWAndEvict (b : Behaviour n) (p : Protocol n) (e_gdown e_shim_coh_write e_shim_coh_evict : Event n) : Prop where
  cohWrite : Event.Shim.bothCoherentWriteReadTranslateWriteFwd n e_gdown e_shim_coh_write
  encapCoherentWrite : e_gdown.Encapsulates n e_shim_coh_write
  cohEvict : Event.Shim.bothCoherentWriteReadTranslateWriteEvict n e_gdown e_shim_coh_evict
  encapCoherentEvict : e_gdown.Encapsulates n e_shim_coh_evict
  cohWriteBeforeEvict : e_shim_coh_write.OrderedBefore n e_shim_coh_evict

/-- Wrapper for the above. -/
def Behaviour.encapCorrespondingGetSWAndEvictWrapper (b : Behaviour n) (p : Protocol n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_coh_write ∈ b, ∃ e_shim_coh_evict ∈ b, b.encapCorrespondingGetSWAndEvict n p e_gdown e_shim_coh_write e_shim_coh_evict

inductive Behaviour.Shim.Global.bothWriteReadSCWriteDownTranslation (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| gReqOnSWOrMR (gDownOnSWOrMR : b.madeOnSWOrMR n init e_gdown) (scGDownTranslation : b.encapCorrespondingGetSWAndEvictWrapper n p e_gdown)
  : Behaviour.Shim.Global.bothWriteReadSCWriteDownTranslation b init p e_gdown

/-- Helper for (Shim) Axiom 16: translation from a Global SC Write Downgrade to the Cluster,
where the protocol has both a Coherent-Write and Coherent-Read.
Covers `bothCoherentWriteAndRead` case in `inductive Behaviour.Shim.GlobalToCluster` -/
inductive Behaviour.Shim.Global.bothWriteReadSCWriteDown (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| scWriteDown (hwrite_down : e_gdown.isSCWriteGlobalDowngrade) (translation : Behaviour.Shim.Global.bothWriteReadSCWriteDownTranslation n b init p e_gdown)
  : Behaviour.Shim.Global.bothWriteReadSCWriteDown b init p e_gdown
| scReadDown (hread_down : e_gdown.isSCReadGlobalDowngrade) /- [TODO] add translation for SC Read downgrade here -/
  : Behaviour.Shim.Global.bothWriteReadSCWriteDown b init p e_gdown

/- [TODO] add translation for `noCoherentRead` case in `inductive Behaviour.Shim.GlobalToCluster` -/

/-- (Shim) Axiom 16: Downgrade at a Global Cache is translated to a Cluster Directory access -/
inductive Behaviour.Shim.GlobalToCluster (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| bothCoherentWriteAndRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hboth_coherent_wr : p.hasCoherentWriteAndRead n)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
| noCoherentRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hno_coherent_read : p.noCoherentRead n)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
