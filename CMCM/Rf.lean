import Mathlib

import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompoundPPOs
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization

variable {n : Nat}

/-- Cluster Directory event's Global Request. -/
noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (hcdir_is_dir : e_cdir.isDirectoryEvent n)
  : Event n :=
  match (cmp.shimAxioms.clusterToGlobal b init e_cdir hcdir_is_dir) with
  | .encapGlobalCache _ hgreq_spec_has_perms => hgreq_spec_has_perms.choose
  | .noGlobalCache _ hgreq_spec_no_perms => hgreq_spec_no_perms.choose

noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper {e_creq : Event n}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (hexists_cdir : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hexists_cdir.choose hexists_cdir.choose_spec.right.isDirEvent

lemma Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (hexists_cdir : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir)
  : Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir) ∈ b
  := by
  simp[wrapper, cDir'sGReq]
  cases cmp.shimAxioms.clusterToGlobal b init hexists_cdir.choose hexists_cdir.choose_spec.right.isDirEvent
  . case encapGlobalCache _ hexists_global_access => simp[hexists_global_access.choose_spec]
  . case noGlobalCache _ hexists_global_access => simp[hexists_global_access.choose_spec]

/-- The Cluster Memory Order and Global Memory Order events (or Cluster Linearization Event CLE and Global Linearization Event GLE).
Note these terms are different from the PPO Linearization event of a request event from the PPO ordering proof.
A cluster request `e_creq` has a CLE `e_creq_lin` that linearizes `e_creq` in its cluster's (total or partial) memory order.
`e_creq` also has a GLE `e_creq_gle` that linearizes `e_creq` in the global (total or partial) memory order.
-/
structure CompoundProtocol.globalLinearizationEventOfRequest (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq : Event n) where
  -- The "Cluster Memory Order, CMO"
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  -- The "Global Memory Order, GMO"
  hreq's_global_lin : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init
    (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hreq's_dir_access) e_gdir

def CompoundProtocol.globalLinearizationEventOfRequest.wrapper :=
  ∀ cmp : CompoundProtocol n, ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_creq : Event n,
    CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_creq

/- Definitions to define rf cases for load value axiom. -/

structure Event.Between.noWrite.cond.sameCacheNoInterWrite
  (b : Behaviour n) (init : InitialSystemState n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  notDown : ¬ e_inter.down
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  sameCache : e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r
  interCleNotBetween :
    ∃ e_inter_cle ∈ b, b.dirAccessOfRequest n init e_inter e_inter_cle ∧
    e_inter.OrderedBetween n e_w e_r →
    ¬ (e_inter.isWrite ∧ e_inter_cle.OrderedBetween n e_w_cle e_r_cle)

structure Event.dirWriteDowngradeAtSameCluster (e_inter_down e_inter e_w : Event n) : Prop where
  isWrite : e_inter_down.isWrite
  notDown : ¬ e_inter_down.down
  sameCluster : e_inter_down.sameProtocol n e_w
  isDir : e_inter_down.isDirectoryEvent
  interEncapDown : e_inter.Encapsulates n e_inter_down

structure Event.Between.noWrite.cond.diffCacheNoInterWriteDowngrade
  (b : Behaviour n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  diffCache : e_inter.diffStructure n e_w ∧ e_inter.diffStructure n e_r
  interCleNotBetween :
    ∃ e_inter_down ∈ b,
      Event.dirWriteDowngradeAtSameCluster e_inter_down e_inter e_w →
        ¬ (e_inter_down.OrderedBetween n e_w_cle e_r_cle)

structure Event.dirWriteDowngradeFromDiffCluster (e_inter_down e_inter e_w e_r : Event n) : Prop where
  diffProtocol : e_inter.diffProtocol n e_w ∧ e_inter.diffProtocol n e_r
  downToW : e_inter_down.sameProtocol n e_w
  isWrite : e_inter_down.isWrite
  isDown : e_inter_down.down
  isDir : e_inter_down.isDirectoryEvent
  interEncapDown : e_inter.Encapsulates n e_inter_down

structure Event.Between.noWrite.cond.diffClusterNoInterWriteDowngrade
  (b : Behaviour n) (e_inter e_w e_r e_w_cle e_r_cle : Event n) where
  interCleNotBetween :
    ¬ ∃ e_inter_down ∈ b,
      Event.dirWriteDowngradeFromDiffCluster e_inter_down e_inter e_w e_r ∧
        (e_inter_down.OrderedBetween n e_w_cle e_r_cle)

inductive Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites
  (b : Behaviour n) (init : InitialSystemState n) (e_inter e_w e_r e_w_cle e_r_cle : Event n)
  : Prop
| otherWSameCache
  (no_write_btn_w_r : Event.Between.noWrite.cond.sameCacheNoInterWrite b init e_inter e_w e_r e_w_cle e_r_cle)
| otherWDiffCacheSameCluster
  (no_write_same_cluster_down : Event.Between.noWrite.cond.diffCacheNoInterWriteDowngrade b e_inter e_w e_r e_w_cle e_r_cle)
| otherWDiffCluster
  (no_write_diff_cluster_down : Event.Between.noWrite.cond.diffClusterNoInterWriteDowngrade b e_inter e_w e_r e_w_cle e_r_cle)

/- Begin Defs for WriteRead.EqGleCle.case -/
def Event.Between.noWrite
  (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle: Event n) : Prop :=
  ∀ e_inter ∈ b, e_inter.isClusterCache → e_inter.isWrite → ¬ e_inter.down →
    Event.Between.noWrite.wSameClusterR.case.excludeOtherWrites b init e_inter e_w e_r e_w_cle e_r_cle

  -- ∃ e_inter_cle ∈ b, b.dirAccessOfRequest n init e_inter e_inter_cle ∧
  --   e_inter.OrderedBetween n e_w e_r →
  --   ¬ (e_inter.isWrite ∧ e_inter_cle.OrderedBetween n e_w_cle e_r_cle)

structure Event.Between (e_inter e_w e_r : Event n) : Prop where
  isCache : e_inter.isCacheEvent
  sameProtocol : e_inter.sameProtocol n e_w ∧ e_inter.sameProtocol n e_r
  sameCache : e_inter.sameStructure n e_w ∧ e_inter.sameStructure n e_r
  interBetween : e_inter.OrderedBetween n e_w e_r
  coherentRead : e_r.isCoherent

def Event.Between.noEvict (b : Behaviour n) (e_w e_r : Event n) : Prop :=
  ∀ e_inter ∈ b, e_inter.Between e_w e_r → ¬ (e_inter.isEvictSW)

structure Event.Between.noWriteOrEvict (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  noWrite : Event.Between.noWrite b init e_w e_r e_w_cle e_r_cle
  noEvict : Event.Between.noEvict b e_w e_r

structure Event.writeReadPair (e_w e_r : Event n) : Prop where
  wIsWrite : e_w.isWrite
  wNotDown : ¬ e_w.down
  rIsRead : e_r.isRead
  rNotDown : ¬ e_r.down

/-- `e_w` and `e_r` are in the same cache and `e_w` is ordered before `e_r` and there are no writes or evicts between them.
This can be considered the "base case" of the reads-from or load-value axiom. -/
structure WriteRead.EqGleCle.case (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  wObR : e_w.OrderedBefore n e_r
  writeRead : Event.writeReadPair e_w e_r
  noBetween : Event.Between.noWriteOrEvict b init e_w e_r e_w_cle e_r_cle
/- End Defs for WriteRead.EqGleCle.case -/

/- Begin Defs for WriteRead.wObRCle.case -/

/-- An intervening directory write from a same-cluster cache write.
    The CLE of the intervening write is a directory write between the boundary events. -/
structure Event.Between.sameProtocol.interveningDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  interInB : e_w_inter ∈ b
  isCluster : e_w_inter.isClusterCache
  isWrite : e_w_inter.isWrite
  notDown : ¬ e_w_inter.down
  sameProtocol : e_w_inter.protocol = e_w_le.protocol
  cleDirWrite : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirWrite
  cleNotDown : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirNotDown
  cleBetween : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.OrderedBetween n e_w_le e_r_le

-- diffProtocol.interveningDirWrite, interveningWrite.sameOrDiffCluster, and noDirWrite
-- are defined below after Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper.

/-
structure WriteRead.wObRCle.sameCache.case (b : Behaviour n) (e_w e_r : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  noWriteBetween : Event.Between.noDirWrite b e_w e_r
-/

  /- Begin Defs for WriteRead.wObRCle.diffCache.case case -/

-- `e_r_down` is the downgrade sent from `e_r` to `e_w`'s cache.
structure WriteRead.noEvictBetween.cond (b : Behaviour n) (init : InitialSystemState n) (e_w e_r_down e_w_cle e_r_cle : Event n) : Prop where
  noWriteBtn : Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cle
  noEvictBtn : Event.Between.noEvict b e_w e_r_down
  wObRDown : e_w.OrderedBefore n e_r_down

  -- rGleDowngrade : sorry -- e_r_gle encapsulates a corresponding downgrade to e_w's corresponding global cache

def Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (e_down e_grant : Event n) : Prop :=
  let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  -- yoink from line 269 from BehaviourRelationDefs.lean (used by Axiom 9, Behaviour.coherentWriteDirDowngradeOthers)
  -- fwdPrevOwner : ∃ e_down ∈ b, ∃ e_grant ∈ b, b.downgradeAtPrevOwner n init e_req e_dir e_down e_grant
  b.downgradeAtPrevOwner n init e_r_cle_gcache e_r_gle e_down e_grant

def Event.getProtocol (cmp : CompoundProtocol n) (e : Event n) : Protocol n :=
  match e.protocol with
  | .global => cmp.global
  | .cluster1 => cmp.cluster1
  | .cluster2 => cmp.cluster2

structure Behaviour.gdown.encapProxyAndDir (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  existsRGlobalDown : ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant
  existsRClusterProxy :
    ∃ e_r_proxy ∈ b, e_r_proxy.protocol = e_w.protocol ∧ e_r_proxy.isClusterCache
  existsRClusterDirDown :
    ∃ e_r_cdir_down ∈ b, e_r_cdir_down.isDirectoryEvent ∧ e_r_cdir_down.protocol = e_w.protocol ∧
      hr_c_and_g_lin.hreq's_dir_access.choose.Encapsulates n e_r_cdir_down

structure Behaviour.gdown.encapProxyAndDirAndCDown {cmp : CompoundProtocol n}
  {b : Behaviour n} {init : InitialSystemState n}
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  encapProxyAndDir : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin
  existsRDownAtW :
    ∃ e_r_down ∈ b, e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  -- sorry

/-- An intervening directory write from a different-cluster cache write.
    The chain goes: e_w_inter (diff cluster) → CLE → global cache (ClusterToGlobal shim)
    → GLE → global downgrade → cluster proxy (GlobalToCluster shim) → cluster directory event.
    Following the pattern of `Behaviour.gdown.encapProxyAndDirAndCDown`. -/
structure Event.Between.diffProtocol.interveningDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le e_w_inter : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  interInB : e_w_inter ∈ b
  isCluster : e_w_inter.isClusterCache
  isWrite : e_w_inter.isWrite
  notDown : ¬ e_w_inter.down
  diffProtocol : e_w_inter.protocol ≠ e_w_le.protocol
  -- Global downgrade from e_w_inter's GLE
  existsGlobalDown : ∃ e_gdown ∈ b, ∃ e_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init
      (hknow_dir_access cmp b init e_w_inter) e_gdown e_grant
  -- Cluster proxy at e_w_le's protocol
  existsClusterProxy :
    ∃ e_proxy ∈ b, e_proxy.protocol = e_w_le.protocol ∧ e_proxy.isClusterCache
  -- Cluster directory event at e_w_le's protocol, between the boundary events.
  -- The additional fields (isWrite, down, Encapsulates) capture that this directory event
  -- is a write-downgrade encapsulated by the originating cache write, matching
  -- the structure of DiffClusterCLE.NotBetweenCLEs.constraints.
  existsClusterDirDown :
    ∃ e_cdir_down ∈ b, e_cdir_down.isDirectoryEvent ∧
      e_cdir_down.protocol = e_w_le.protocol ∧
      e_cdir_down.isWrite ∧
      e_cdir_down.down ∧
      e_w_inter.Encapsulates n e_cdir_down ∧
      e_cdir_down.OrderedBetween n e_w_le e_r_le

/-- Complete definition of an intervening write between two linearization events.
    An intervening write is either from the same cluster or a different cluster. -/
inductive Event.Between.interveningWrite.sameOrDiffCluster
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| sameCluster
    (e_w_inter : Event n)
    (h : Event.Between.sameProtocol.interveningDirWrite cmp b init e_w_le e_r_le e_w_inter hknow_dir_access)
    : interveningWrite.sameOrDiffCluster cmp b init e_w_le e_r_le hknow_dir_access
| diffCluster
    (e_w_inter : Event n)
    (h : Event.Between.diffProtocol.interveningDirWrite cmp b init e_w_le e_r_le e_w_inter hknow_dir_access)
    : interveningWrite.sameOrDiffCluster cmp b init e_w_le e_r_le hknow_dir_access

/-- No intervening directory write between two linearization events. -/
def Event.Between.noDirWrite
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_le e_r_le : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop :=
  ¬ Event.Between.interveningWrite.sameOrDiffCluster cmp b init e_w_le e_r_le hknow_dir_access

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
Exists `e_r_down` corresponding to `e_r_cdir_down` at `e_w`'s cache.
-/
structure WriteRead.noEvictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  gdownEncapProxyAndDirAndCDown : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  noEvictBetween :
    WriteRead.noEvictBetween.cond b init
      e_w gdownEncapProxyAndDirAndCDown.existsRDownAtW.choose
        hw_c_and_g_lin.hreq's_dir_access.choose
        gdownEncapProxyAndDirAndCDown.encapProxyAndDir.existsRClusterDirDown.choose

def Event.Between.dirEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∃ e ∈ b, e.OrderedBetween n e₁ e₂ → e.isDirEvict

structure WriteRead.evictBetween.cond
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w_cle e_r_cdir_down : Event n)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  noWriteBtn : Event.Between.noDirWrite cmp b init e_w_cle e_r_cdir_down hknow_dir_access
  evictBtn : Event.Between.dirEvict b e_w_cle e_r_cdir_down
  wObRDown : e_w_cle.OrderedBefore n e_r_cdir_down

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
-/
structure WriteRead.evictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
  encapProxyAndDir : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin
  evictBetween : WriteRead.evictBetween.cond cmp b init (hw_c_and_g_lin.hreq's_dir_access.choose) encapProxyAndDir.existsRClusterDirDown.choose hknow_dir_access

inductive WriteRead.wObRCle.diffCache.wHasPermsAfter.case
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| noEvictBetween
  (w_ob_r_down : WriteRead.noEvictBetween.cond.wrapper cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| evictBetween
  (w_cle_ob_r_cdir_down : WriteRead.evictBetween.cond.wrapper cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

def CompoundProtocol.cleImmediatePredecessor
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  b.ImmediateBottomPredecessor n
    hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose

/-- When the write is coherent and at a different cache from the read,
    either the CLE of e_w immediately precedes the CLE of e_r (so the
    downgrade chain is constructed from CLE immediate predecessor),
    or the more general wHasPermsAfter.case applies (noEvict/evict subcases). -/
inductive WriteRead.wObRCle.diffCache.wCoherent.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| immPred
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| notImmPred
  (hw_has_perms_case : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
    (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
    hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

/-- e_r's proxy directory access (CLE) is ordered after e_w's CLE. -/
def WriteRead.wObRCle.diffCache.rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose

-- Cache write with something?
structure Event.cacheWrite.global (e : Event n) : Prop where
  isCacheWrite : e.isWrite
  isGlobal : e.protocol = .global

def Event.Between.noGlobalCacheWrite (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e₁ e₂ → ¬ Event.cacheWrite.global e

structure WriteRead.wCleAfter.cond (b : Behaviour n) (e_w_cle_gcache e_r_gdown : Event n) : Prop where
  noWriteBtn : Event.Between.noGlobalCacheWrite b e_w_cle_gcache e_r_gdown
  wObRDown : e_w_cle_gcache.OrderedBefore n e_r_gdown

/- (need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_w_cle_gcache` corresponding to `e_w_cle` at `e_w`'s cluster.
-/
def WriteRead.wCleAfter.cond.wrapper {e_w e_r}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  let e_w_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir := hw_c_and_g_lin.hreq's_dir_access)
  ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant ∧
    WriteRead.wCleAfter.cond b e_w_cle_gcache e_r_gdown

inductive WriteRead.wObRCle.diffCache.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
| wHasPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  /- subcases are:
    immPred: e_w_cle is immediate predecessor of e_r_cle (cluster-level downgrade via Axiom 9)
    notImmPred: the general case with noEvict/evict subcases
  -/
  (hw_coherent : e_w.isCoherent)
  -- Use WriteRead.wObRCle.diffCache.wCoherent.case to distinguish immPred vs notImmPred
  (coherent_write : WriteRead.wObRCle.diffCache.wCoherent.case hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| wNoPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  -- TODO STUB: Write has no perms (ex. Non-Coherent Release Write). Treat similar to wCleAfter case
  /- e_r's CLE (proxy directory access) is ordered after e_w's CLE.
     No global downgrade in the sameGle case since e_w and e_r share the same cluster.
  -/
  (hw_no_perms : b.reqMissingPerms n init e_w)
  (hw_nc : e_w.isNonCoherent)
  (hr_cle_after_w_cle : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
| wCleAfter -- `e_w`'s CLE is after `e_w`. (dirAccessOfRequest .after case.)
  /- subcases are:
    (Only one):
      case of vdWB after `e_w`.
    (Not allowed, coherent req is a competing write!):
      case of coherent req after `e_w` (i.e. in RCC-O or L-RCC protocol interfaces).
    -/
  /- e_r's CLE (proxy directory access) is ordered after e_w's CLE.
     No global downgrade in the sameGle case since e_w and e_r share the same cluster.
  -/
  (hr_cle_after_w_cle : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

  /- End Defs for WriteRead.wObRCle.diffCache.case case -/

inductive WriteRead.wObRCle.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  | sameCache
    (sameCache : e_w.struct = e_r.struct)
    (noWriteBetween : Event.Between.noDirWrite cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  | diffCache
    (hdiff_cache : e_w.struct ≠ e_r.struct)
    -- STUB: add inductive (WriteRead.wObRCle.diffCache.case) to define subcases of this case.
    (hdiff_cache_case : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

/- End Defs for WriteRead.wObRCle.case -/

structure WriteRead.wObR.GleOrCle.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop where
    (hw_r_cle_ob : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    -- add inductive (WriteRead.wObRCle.case) to define goal.
    (hwr_cle_ob_case : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)

inductive Behaviour.readsFrom.wEqRGle.cases (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  | wEqRCle
    (hw_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    (hwr_com : WriteRead.EqGleCle.case b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  | wObRCle
    -- NOTE: bundled hypothesis conditions together, for re-use in the wObRGle case below.
    (hwr_gle_or_cle_case : WriteRead.wObR.GleOrCle.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

inductive Behaviour.readsFrom.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  -- {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
  : Prop
  -- `e_w`'s GLE is the same as `e_r`'s GLE
  | wEqRGle
    (hw_r_gle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    -- Use `Behaviour.readsFrom.wEqRGle.cases` to distinguish subcases of this case.
    (hw_eq_r_gle_cases : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  -- `e_w`'s GLE is Ordered Before `e_r`'s GLE
  | wObRGle
    (hw_r_gle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
    -- use inductive to define subcases of this case
    (hw_ob_r_gle_cases : WriteRead.wObR.GleOrCle.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
    : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access

-- Define Constraints where RF should be proven to hold.

/- ========= BEGIN RF Constraints ========= -/

def CompoundProtocol.gleImmediatePredecessor
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop :=
  b.ImmediateBottomPredecessor n
    hw_c_and_g_lin.hreq's_global_lin.choose hr_c_and_g_lin.hreq's_global_lin.choose

structure IntermediateDirEvictOrRead
  (e_cdir_inter e_w_cle e_r_cle : Event n)
  : Prop where
  readOrEvict : e_cdir_inter.isDirRead -- Not a write or write-downgrade.
  sameProtocol : e_cdir_inter.sameProtocol n e_w_cle
  sameStructure : e_cdir_inter.sameStructure n e_w_cle
  betweenWR : e_cdir_inter.OrderedBetween n e_w_cle e_r_cle

structure CLE.WROrdering.evictOrReadBetween
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  wRSameCluster : e_w.sameProtocol n e_r
  interDirEvictOrRead : ∀ e_cdir_inter ∈ b,
    IntermediateDirEvictOrRead e_cdir_inter
      hw_c_and_g_lin.hreq's_dir_access.choose
      hr_c_and_g_lin.hreq's_dir_access.choose
  wObR : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
        hr_c_and_g_lin.hreq's_dir_access.choose

/- Cases of CLE if `e_w` GLE ImmPred `e_r` GLE. Same Cluster case. -/
inductive CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | wImmPredRCle (w_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  | evictOrReadBetweenWAndRCleSameCluster (evict_or_read_btn_w_r_cle :
      CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)

/-- Cases of CLE if GLEs are equal. Same Cluster. -/
inductive CompoundProtocol.gleEq.SameCluster.cleEq.cleOb.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | wEqRCle (w_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  | otherCases (same_as_gle_ob_cases : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

structure ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w : Event n} {e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  rDown : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  wCleImmPredRDown : ∀ e_cdir_inter ∈ b,
     IntermediateDirEvictOrRead e_cdir_inter
      hw_c_and_g_lin.hreq's_dir_access.choose
      rDown.existsRDownAtW.choose
  wObRDown : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
    rDown.existsRDownAtW.choose

structure ReadDowngradeAtWrite.wCleImmPredDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
  {e_w : Event n} {e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop where
  rDown : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin
  wCleImmPredRDown : b.ImmediateBottomPredecessor n
    hw_c_and_g_lin.hreq's_dir_access.choose rDown.existsRDownAtW.choose

/- Cases of CLE if `e_w` GLE ImmPred `e_r` GLE. Different Cluster case. -/
inductive CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  -- TODO: Define def or reuse def of downgrade `e_r_down` from `e_r` to `e_w`'s cluster
  -- Then the cases are either `e_r_down` is an immediate predecessor of `e_w`'s CLE,
  -- or all intermediate directory events between `e_w`'s CLE and `e_r_down` are either evict or read.
  | wCleImmPredDown (w_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
  | evictOrReadBetweenWAndRDown (w_cle_imm_pred_down : ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown hw_c_and_g_lin hr_c_and_g_lin)

inductive CompoundProtocol.gleOB.Cluster.SameOrDiff.cleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
    (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
    (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : Prop
  | sameCluster (same_cluster : e_w.sameProtocol n e_r)
    (same_cluster_cases : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  | diffCluster (diff_cluster : ¬ e_w.sameProtocol n e_r)
    (diff_cluster_cases : CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

-- inductive cases on the relationship between the GLEs and CLEs
inductive CompoundProtocol.gleOrdering.Cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  | sameGle
    (same_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    (cle_cases : CompoundProtocol.gleEq.SameCluster.cleEq.cleOb.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  | wImmPredRGle
    (w_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
    (cle_cases : CompoundProtocol.gleOB.Cluster.SameOrDiff.cleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)

/- ========== END RF Constraints ========== -/
