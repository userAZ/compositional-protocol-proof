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
  (e_creq : Event n) (hcreq_cluster : e_creq.isClusterCache) (hndown : ¬ e_creq.down) where
  -- The "Cluster Memory Order, CMO"
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  -- The "Global Memory Order, GMO"
  hreq's_global_lin : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init
    (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hreq's_dir_access) e_gdir

def CompoundProtocol.globalLinearizationEventOfRequest.wrapper :=
  ∀ cmp : CompoundProtocol n, ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_creq : Event n, ∀ hcreq_cluster : e_creq.isClusterCache, ∀ hndown : ¬ e_creq.down,
    CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_creq hcreq_cluster hndown

/- Definitions to define rf cases for load value axiom. -/

/- Begin Defs for WriteRead.EqGleCle.case -/
def Event.Between.noWrite
  (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle: Event n) : Prop :=
  ∀ e_inter ∈ b, ∃ e_inter_cle ∈ b, b.dirAccessOfRequest n init e_inter e_inter_cle ∧
    e_inter.OrderedBetween n e_w e_r →
    ¬ (e_inter.isWrite ∧ e_inter_cle.OrderedBetween n e_w_cle e_r_cle)

def Event.Between.noEvict (b : Behaviour n) (e_w e_r : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e_w e_r → ¬ (e.isEvict ∧ e.isCoherent)

structure Event.Between.noWriteOrEvict (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  noWrite : Event.Between.noWrite b init e_w e_r e_w_cle e_r_cle
  noEvict : Event.Between.noEvict b e_w e_r

/-- `e_w` and `e_r` are in the same cache and `e_w` is ordered before `e_r` and there are no writes or evicts between them.
This can be considered the "base case" of the reads-from or load-value axiom. -/
structure WriteRead.EqGleCle.case (b : Behaviour n) (init : InitialSystemState n) (e_w e_r e_w_cle e_r_cle : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  wObR : e_w.OrderedBefore n e_r
  noBetween : Event.Between.noWriteOrEvict b init e_w e_r e_w_cle e_r_cle
/- End Defs for WriteRead.EqGleCle.case -/

/- Begin Defs for WriteRead.wObRCle.case -/
def Event.Between.noDirWrite (b : Behaviour n) (e_w e_r : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e_w e_r → ¬ e.isDirWrite

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
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
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
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop where
  existsRGlobalDown : ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant
  existsRClusterProxy :
    ∃ e_r_proxy ∈ b, e_r_proxy.protocol = e_w.protocol ∧ e_r_proxy.isClusterCache
  existsRClusterDirDown :
    ∃ e_r_cdir_down ∈ b, e_r_cdir_down.isDirectoryEvent ∧ e_r_cdir_down.protocol = e_w.protocol

structure Behaviour.gdown.encapProxyAndDirAndCDown (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_w : Event n)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop where
  encapProxyAndDir : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin
  existsRDownAtW :
    ∃ e_r_down ∈ b, e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  -- sorry

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
Exists `e_r_down` corresponding to `e_r_cdir_down` at `e_w`'s cache.
-/
structure WriteRead.noEvictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop where
  gdownEncapProxyAndDirAndCDown : Behaviour.gdown.encapProxyAndDirAndCDown cmp b init e_w hr_c_and_g_lin
  noEvictBetween :
    WriteRead.noEvictBetween.cond b init
      e_w gdownEncapProxyAndDirAndCDown.existsRDownAtW.choose
        hw_c_and_g_lin.hreq's_dir_access.choose
        gdownEncapProxyAndDirAndCDown.encapProxyAndDir.existsRClusterDirDown.choose

def Event.Between.dirEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∃ e ∈ b, e.OrderedBetween n e₁ e₂ → e.isDirEvict

structure WriteRead.evictBetween.cond (b : Behaviour n) (e_w_cle e_r_cdir_down : Event n) : Prop where
  noWriteBtn : Event.Between.noDirWrite b e_w_cle e_r_cdir_down
  evictBtn : Event.Between.dirEvict b e_w_cle e_r_cdir_down
  wObRDown : e_w_cle.OrderedBefore n e_r_cdir_down

/- (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
-/
structure WriteRead.evictBetween.cond.wrapper
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop where
  encapProxyAndDir : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin
  evictBetween : WriteRead.evictBetween.cond b (hw_c_and_g_lin.hreq's_dir_access.choose) encapProxyAndDir.existsRClusterDirDown.choose

inductive WriteRead.wObRCle.diffCache.wHasPermsAfter.case
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w_cle e_r_cdir_down : Event n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
| noEvictBetween
  (w_ob_r_down : WriteRead.noEvictBetween.cond.wrapper cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin
| evictBetween
  (w_cle_ob_r_cdir_down : WriteRead.evictBetween.cond.wrapper cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init e_w_cle e_r_cdir_down hw_c_and_g_lin hr_c_and_g_lin

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
def WriteRead.wCleAfter.cond.wrapper {e_w hw_cluster hw_not_down e_r hr_cluster r_not_down}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop :=
  let e_w_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init (hexists_cdir := hw_c_and_g_lin.hreq's_dir_access)
  ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant ∧
    WriteRead.wCleAfter.cond b e_w_cle_gcache e_r_gdown

inductive WriteRead.wObRCle.diffCache.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
| wHasPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  /- subcases are:
    if no evict, then e_r downgrade is after e_w;
    if evict, then e_r's CLE is after e_w's CLE, with an evict in between.
  -/
  (hw_nc : e_w.isCoherent)
  -- Use WriteRead.wObRCle.diffCache.wHasPermsAfter.cases
  (coherent_write : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose) hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
| wNoPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  -- TODO STUB: Write has no perms (ex. Non-Coherent Release Write). Treat similar to wCleAfter case
  /- Must add constraint that `e_w`'s CLE's corresponding global cache access `e_w_cle_gcache`
  is ordered before `e_r`'s downgrade `e_r_gdown`
  -- and there is no global cache write between `e_w_cle_gcache` and `e_r_gdown`.
  -/
  (hw_no_perms : b.reqMissingPerms n init e_w)
  (hw_nc : e_w.isNonCoherent)
  (hw_gcache_ob_r_gdown : WriteRead.wCleAfter.cond.wrapper cmp b init hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
| wCleAfter -- `e_w`'s CLE is after `e_w`. (dirAccessOfRequest .after case.)
  /- subcases are:
    (Only one):
      case of vdWB after `e_w`.
    (Not allowed, coherent req is a competing write!):
      case of coherent req after `e_w` (i.e. in RCC-O or L-RCC protocol interfaces).
    -/
  (hw_ob_r_no_writes_btn : WriteRead.wCleAfter.cond.wrapper cmp b init hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin

  /- End Defs for WriteRead.wObRCle.diffCache.case case -/

inductive WriteRead.wObRCle.case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
  | sameCache
    (sameCache : e_w.struct = e_r.struct)
    (noWriteBetween : Event.Between.noDirWrite b e_w e_r)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
  | diffCache
    (hdiff_cache : e_w.struct ≠ e_r.struct)
    -- STUB: add inductive (WriteRead.wObRCle.diffCache.case) to define subcases of this case.
    (hdiff_cache_case : WriteRead.wObRCle.diffCache.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin)
    : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin

/- End Defs for WriteRead.wObRCle.case -/

structure WriteRead.wObR.GleOrCle.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop where
    (hw_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    -- add inductive (WriteRead.wObRCle.case) to define goal.
    (hwr_cle_ob_case : WriteRead.wObRCle.case hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin)

inductive Behaviour.readsFrom.wEqRGle.cases (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
  | wEqRCle
    (hw_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    (hwr_com : WriteRead.EqGleCle.case b init e_w e_r hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin
  | wObRCle
    -- NOTE: bundled hypothesis conditions together, for re-use in the wObRGle case below.
    (hwr_gle_or_cle_case : WriteRead.wObR.GleOrCle.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin

inductive Behaviour.readsFrom.cases
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {r_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
  -- `e_w`'s GLE is the same as `e_r`'s GLE
  | wEqRGle
    (hw_r_gle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    -- Use `Behaviour.readsFrom.wEqRGle.cases` to distinguish subcases of this case.
    (hw_eq_r_gle_cases : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin)
    : Behaviour.readsFrom.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
  -- `e_w`'s GLE is Ordered Before `e_r`'s GLE
  | wObRGle
    (hw_r_gle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
    -- use inductive to define subcases of this case
    (hw_ob_r_gle_cases : WriteRead.wObR.GleOrCle.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin)
    : Behaviour.readsFrom.cases hw_is_write r_is_read hw_c_and_g_lin hr_c_and_g_lin
