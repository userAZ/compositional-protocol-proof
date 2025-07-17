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

/-- A directory event `e` is made on state `s` -/
def Behaviour.dirEventMadeOn (b : Behaviour n) (init : InitialSystemState n) (e : Event n) (s : State) : Prop :=
  (b.directoryStateMadeOn n init e).toState = s

def Event.atProxy (e : Event n) : Prop := match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy _ => True
    | .cache _ => False
  | .directoryEvent _ => False

structure Event.Shim.Global.ToCluster.matchingCluster (e_gdown e_shim_trans : Event n) : Prop where
  sameAddr : e_gdown.sameAddr n e_shim_trans
  atCorrCluster : e_gdown.correspondingClusterOfGlobalCache n e_shim_trans (Event.protocol n)

/-- A translated event from the shim `e_shim_trans` goes to the Proxy Cache, for the same address,
in the Cluster corresponding to requesting downgrade. -/
structure Event.Shim.Global.ToCluster.proxyCacheEvent (e_gdown e_shim_trans : Event n) : Prop where
  clusterMatch : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_shim_trans
  atProxy : e_shim_trans.atProxy n

/-- A translated Global Request that contains a Cluster Proxy Cache Event `e_shim` of request  -/
structure Event.Shim.Global.ToCluster.translateProxyEvent (e_gdown e_shim : Event n) (prop : ValidRequest → Prop) (isDown : Prop) : Prop where
  atCorrClusterProxy : Event.Shim.Global.ToCluster.proxyCacheEvent n e_gdown e_shim
  reqTranslation : prop e_shim.req
  downgrade : e_shim.down = isDown
  globalEncap : e_gdown.Encapsulates n e_shim

/-- Global Cache Downgrade Request, encapsulates a Cluster Directory event. -/
structure Event.Shim.Global.ToCluster.translateDirectoryEvent (e_gdown e_shim_trans : Event n) (prop : ValidRequest → Prop) (isDown : Prop) : Prop where
  clusterMatch : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_shim_trans
  atDir : e_shim_trans.isDirectoryEvent n
  reqTranslation : prop e_shim_trans.req
  downgrade : e_shim_trans.down = isDown
  globalEncap : e_gdown.Encapsulates n e_shim_trans

/-
structure Event.vcInvalDummy (e : Event n) : Prop where
  down : e.down
  isDir : e.isDirectoryEvent
  vcWeakRead : e.isNcWeakRead
-/

structure Event.Shim.Global.ToCluster.directoryEventStateCheck (e_gdown e_shim_trans : Event n) : Prop where
  toCluster : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_shim_trans ValidRequest.isNcWeakRead True

/-- A global SC write downgrade encapsulates a Coherent Write `e_w` and Evict `e_v` (`e_w` orderedBefore `e_v`) in the corresponding Cluster's Proxy Cache. -/
structure Behaviour.encapCorrespondingGetSWAndEvict (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown e_dir_state e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict : Event n) : Prop where
  gDownEncapDirState : e_gdown.Encapsulates n e_dir_state
  cohWriteDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_coh_write) true e_shim_coh_write e_dir_shim_coh_write
  stateCheckBeforeAccess : b.ImmediateBottomPredecessor n e_dir_state e_dir_shim_coh_write
  cohWrite : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_write ValidRequest.isSCWrite False
  cohEvict : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_evict ValidRequest.isSCWrite True
  cohWriteImmBeforeEvict : b.ImmediateBottomPredecessor n e_shim_coh_write e_shim_coh_evict

/-- Wrapper for the above. -/
def Behaviour.encapCorrespondingGetSWAndEvictWrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_dir_state ∈ b, ∃ e_shim_coh_write ∈ b, ∃ e_dir_shim_coh_write, ∃ e_shim_coh_evict ∈ b,
    b.encapCorrespondingGetSWAndEvict n init e_gdown e_dir_state e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict

/-- Helper for (Shim) Axiom 16: State a Global Write Fwd Downgrade (for a Cluster with both Coherent Write and Read)
is translated to a Cluster (1) Proxy Cache SC Write, and (2) a Proxy Cache SC Write Evict. -/
structure Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown e_dir_check : Event n) : Prop where
  clusterDir : Event.Shim.Global.ToCluster.directoryEventStateCheck n e_gdown e_dir_check
  gDownOnSWOrMR : b.dirEventMadeOn n init e_dir_check SW ∨ b.dirEventMadeOn n init e_dir_check MR -- consider using a weak downgrade
  scGDownTranslation : b.encapCorrespondingGetSWAndEvictWrapper n init e_gdown

/-- Wrapper for def above. -/
def Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop :=
  ∃ e_dir_check ∈ b, Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation n b init p e_gdown e_dir_check

structure Behaviour.encapCorrespondingGetMR (b : Behaviour n) (p : Protocol n) (e_gdown e_shim_coh_read : Event n) : Prop where
  cohRead : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_read ValidRequest.isSCRead False

/-- Helper for (Shim) Axiom 16: State that a Global Read Fwd Downgrade (for a Cluster with both Coherent Write and Read)
is translated to a Cluster Proxy Cache SC Read. -/
def Behaviour.Shim.Global.bothWriteRead.SCReadDownTranslation (b : Behaviour n) (p : Protocol n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_coh_read ∈ b, b.encapCorrespondingGetMR n p e_gdown e_shim_coh_read

/-- Helper for (Shim) Axiom 16: translation from a Global SC Write Downgrade to the Cluster,
where the protocol has both a Coherent-Write and Coherent-Read.
Covers `bothCoherentWriteAndRead` case in `inductive Behaviour.Shim.GlobalToCluster` -/
inductive Behaviour.Shim.Global.bothWriteReadSCWriteDown (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| scWriteDown (hwrite_down : e_gdown.isSCWriteGlobalDowngrade) (translation : Behaviour.Shim.Global.bothWriteReadSCWriteDownTranslationWrapper n b init p e_gdown)
  : Behaviour.Shim.Global.bothWriteReadSCWriteDown b init p e_gdown
| scReadDown (hread_down : e_gdown.isSCReadGlobalDowngrade) (translation : Behaviour.Shim.Global.bothWriteReadSCReadDownTranslation n b p e_gdown)
  : Behaviour.Shim.Global.bothWriteReadSCWriteDown b init p e_gdown

/- [TODO] add translation for `noCoherentRead` case in `inductive Behaviour.Shim.GlobalToCluster` -/

/-- (Shim) Axiom 16: Downgrade at a Global Cache is translated to a Cluster Directory access -/
inductive Behaviour.Shim.GlobalToCluster (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| bothCoherentWriteAndRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hboth_coherent_wr : p.hasCoherentWriteAndRead n) (downTranslation : Behaviour.Shim.Global.bothWriteRead.Down n b init p e_gdown)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
| noCoherentRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hno_coherent_read : p.noCoherentRead n)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
