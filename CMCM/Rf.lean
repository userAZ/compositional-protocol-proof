import Mathlib

import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompoundPPOs
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization

variable {n : Nat}

/-- Cluster Directory event's Global Request. -/
noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n) (hcdir_is_dir : e_cdir.isDirectoryEvent n) : Event n :=
  match (cmp.shimAxioms.clusterToGlobal b init e_cdir hcdir_is_dir) with
  | .encapGlobalCache _ hgreq_spec_has_perms => hgreq_spec_has_perms.choose
  | .noGlobalCache _ hgreq_spec_no_perms => hgreq_spec_no_perms.choose

noncomputable def Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper {e_creq : Event n}
  (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (hexists_cdir : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hexists_cdir.choose hexists_cdir.choose_spec.right.isDirEvent

/-- The Cluster Memory Order and Global Memory Order events (or Cluster Linearization Event CLE and Global Linearization Event GLE).
Note these terms are different from the PPO Linearization event of a request event from the PPO ordering proof.
A cluster request `e_creq` has a CLE `e_creq_lin` that linearizes `e_creq` in its cluster's (total or partial) memory order.
`e_creq` also has a GLE `e_creq_gle` that linearizes `e_creq` in the global (total or partial) memory order.
-/
structure CompoundProtocol.globalLinearizationEventOfRequest (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq : Event n) (hcreq_cluster : e_creq.isClusterCache) (hndown : ¬ e_creq.down) : Prop where
  -- The "Cluster Memory Order, CMO"
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  -- The "Global Memory Order, GMO"
  hreq's_global_lin : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init
    (Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hreq's_dir_access) e_gdir

/- Definitions to define rf cases for load value axiom. -/

/- Begin Defs for WriteRead.EqGleCle.case -/
def Event.Between.noWrite (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e₁ e₂ → ¬ e.isWrite

def Event.Between.noEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e₁ e₂ → ¬ e.isEvict

structure Event.Between.noWriteOrEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop where
  noWrite : Event.Between.noWrite b e₁ e₂
  noEvict : Event.Between.noEvict b e₁ e₂

structure WriteRead.EqGleCle.case (b : Behaviour n) (e_w e_r : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  wObR : e_w.OrderedBefore n e_r
  noBetween : Event.Between.noWriteOrEvict b e_w e_r
/- End Defs for WriteRead.EqGleCle.case -/

/- Begin Defs for WriteRead.wObRCle.case -/
def Event.Between.noDirWrite (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∀ e ∈ b, e.OrderedBetween n e₁ e₂ → ¬ e.isDirWrite

/-
structure WriteRead.wObRCle.sameCache.case (b : Behaviour n) (e_w e_r : Event n) : Prop where
  sameCache : e_w.struct = e_r.struct
  noWriteBetween : Event.Between.noDirWrite b e_w e_r
-/

  /- Begin Defs for WriteRead.wObRCle.diffCache.case case -/

-- `e_r_down` is the downgrade sent from `e_r` to `e_w`'s cache.
structure WriteRead.noEvictBetween (b : Behaviour n) (e_w e_r_down : Event n) : Prop where
  noWriteBtn : Event.Between.noWrite b e_w e_r_down
  noEvictBtn : Event.Between.noEvict b e_w e_r_down
  wObRDown : e_w.OrderedBefore n e_r_down

  -- rGleDowngrade : sorry -- e_r_gle encapsulates a corresponding downgrade to e_w's corresponding global cache

-- STUB:
/- -- TODO: (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
Exists `e_r_down` corresponding to `e_r_cdir_down` at `e_w`'s cache.
-/
structure WriteRead.noEvictBetween.wrapper

def Event.Between.dirEvict (b : Behaviour n) (e₁ e₂ : Event n) : Prop :=
  ∃ e ∈ b, e.OrderedBetween n e₁ e₂ → e.isDirEvict

structure WriteRead.evictBetween (b : Behaviour n) (e_w_cle e_r_cdir_down : Event n) : Prop where
  noWriteBtn : Event.Between.noDirWrite b e_w_cle e_r_cdir_down
  evictBtn : Event.Between.dirEvict b e_w_cle e_r_cdir_down
  wObRDown : e_w_cle.OrderedBefore n e_r_cdir_down

-- STUB:
/- -- TODO: (will need to use existing "corresponding event" defs across files)
Use exists to say there exists `e_r_gdown` that `e_r_gle` encaps a corresponding `e_r_gdown`.
Exists `e_r_proxy` corresponding to `e_r_gdown` at `e_w`'s cluster.
Exists `e_r_cdir_down` corresponding to `e_r_proxy` at `e_w`'s directory.
-/
structure WriteRead.evictBetween.wrapper

inductive WriteRead.wObRCle.diffCache.wHasPermsAfter.case (b : Behaviour n) (e_w e_r : Event n) : Prop
| noEvictBetween

  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case b e_w e_r
| evictBetween
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case b e_w e_r

inductive WriteRead.wObRCle.diffCache.case (b : Behaviour n) (e_w e_r : Event n) : Prop
| wHasPermsAfter -- `e_w`'s CLE is before or encap by `e_w`. (dirAccessOfRequest .before or .encap cases.)
  /- subcases are:
    if no evict, then e_r downgrade is after e_w;
    if evict, then e_r's CLE is after e_w's CLE, with an evict in between.
  -/
  -- STUB: Use WriteRead.wObRCle.diffCache.wHasPermsAfter.cases
  : WriteRead.wObRCle.diffCache.case b e_w e_r
| wCleAfter -- `e_w`'s CLE is after `e_w`. (dirAccessOfRequest .after case.)
  /- subcases are:
    (Only one):
      case of vdWB after `e_w`.
    (Not allowed, coherent req is a competing write!):
      case of coherent req after `e_w` (i.e. in RCC-O or L-RCC protocol interfaces).
    -/
  : WriteRead.wObRCle.diffCache.case b e_w e_r

  /- End Defs for WriteRead.wObRCle.diffCache.case case -/

inductive WriteRead.wObRCle.case (b : Behaviour n) (e_w e_r : Event n) : Prop
  | sameCache
    (sameCache : e_w.struct = e_r.struct)
    (noWriteBetween : Event.Between.noDirWrite b e_w e_r)
    : WriteRead.wObRCle.case b e_w e_r
  | diffCache
    (hdiff_cache : e_w.struct ≠ e_r.struct)
    -- STUB: add inductive (WriteRead.wObRCle.diffCache.case) to define subcases of this case.
    : WriteRead.wObRCle.case b e_w e_r

/- End Defs for WriteRead.wObRCle.case -/

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
    (hwr_com : WriteRead.EqGleCle.case b e_w e_r)
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin
  | wObRCle
    (hw_r_cle_eq : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose)
    (hwr_same_cluster : e_w.protocol = e_r.protocol)
    -- STUB: add inductive (WriteRead.wObRCle.case) to define goal.
    : Behaviour.readsFrom.wEqRGle.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin

inductive Behaviour.readsFrom.cases (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hw_is_write : e_w.isWrite) (r_is_read : e_r.isRead)
  (hw_not_down : ¬ e_w.down) (r_not_down : ¬ e_r.down)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w hw_cluster hw_not_down)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r hr_cluster r_not_down)
  : Prop
  -- `e_w`'s GLE is the same as `e_r`'s GLE
  | wEqRGle
    (hw_r_gle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
    -- STUB: Use `Behaviour.readsFrom.wEqRGle.cases` to distinguish subcases of this case.
    : Behaviour.readsFrom.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin
  -- `e_w`'s GLE is Ordered Before `e_r`'s GLE
  | wObRGle
    (hw_r_gle_ob : hw_c_and_g_lin.hreq's_global_lin.choose.OrderedBefore n hr_c_and_g_lin.hreq's_global_lin.choose)
    -- STUB: add inductive to define subcases of this case
    : Behaviour.readsFrom.cases cmp b init e_w e_r hw_cluster hr_cluster hw_is_write r_is_read hw_not_down r_not_down hw_c_and_g_lin hr_c_and_g_lin
