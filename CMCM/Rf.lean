import Mathlib

import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompoundPPOs
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourShim
import CompositionalProtocolProof.CompositionalProof.CompoundLinearization

variable (n : Nat)

open Classical in
def Behaviour.Shim.ClusterToGlobal.hasPerms.linearizationEvent
  (shimAxioms : ShimAxioms n) (b : Behaviour n) (init : InitialSystemState n)
  (e_cdir e_glin : Event n) (hcdir_is_dir : e_cdir.isDirectoryEvent n) : Prop :=
    let e_cdir_shim := shimAxioms.clusterToGlobal b init e_cdir hcdir_is_dir
    Behaviour.Shim.ClusterToGlobal.hasPerms.globalDirectoryEvent n b init e_cdir e_glin e_cdir_shim

-- A directory linearization event has a corresponding event in the global protocol
inductive CompoundProtocol.clusterDirGlobalLin (shimAxioms : ShimAxioms n) (b : Behaviour n) (init : InitialSystemState n) (e_cdir e_glin : Event n)
  (hcdir_is_dir : e_cdir.isDirectoryEvent n) : Prop
| previousGlobalCacheGotPerms
  (has_gcache_perms : e_cdir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_cdir).state)
  /- -- TODO: use a helper def to state that e_cdir encapsulates a e_gcache event (with perms).
  Then e_glin is the linearization event corresponding to e_gcache's predecessor that obtained permissions.
  -/
  (cdir_with_perms_global_lin : Behaviour.Shim.ClusterToGlobal.hasPerms.linearizationEvent n shimAxioms b init e_cdir e_glin hcdir_is_dir)
  : CompoundProtocol.clusterDirGlobalLin shimAxioms b init e_cdir e_glin hcdir_is_dir
| getGlobalCachePerms
  (no_gcache_perms : ¬ e_cdir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_cdir).state)
  (cdir_request_gcache : Behaviour.Shim.ClusterToGlobal.noPerms.linearizationEvent n shimAxioms b init e_cdir e_glin)
  : CompoundProtocol.clusterDirGlobalLin shimAxioms b init e_cdir e_glin hcdir_is_dir

-- TODO: this needs to be re-written to so the global_dir (GDE) is either encapsulated (already represented) or
-- corresponds to the prior global cache event `e_pred_gcache` that got permissions (not yet represented).
-- Implement a def for "globalDirEventOfRequest" that captures both cases (GDE is either encapsulated, or the prior global cache event that got perms).
-- Remember to use existing defs like
-- "Behaviour.Shim.ClusterToGlobal" for both cases, to get to handling both cases. (the inductive constructor cases are these two cases)
-- "dirAccessOfRequest" for the second case (use on latest e_gdir corresponding to ClusterLE cdir)
-- In the second case, remember the global protocol uses coherent read and writes, to get `e_pred_gcache`'s directory event (GDE).
-- But please be thorough in re-using existing defs and lemmas, to make the proof easier.
def Behaviour.Shim.ClusterToGlobal.globalCacheAccessWithDir
  (b : Behaviour n) (init : InitialSystemState n) (e_cdir : Event n)
  (hshim : Behaviour.Shim.ClusterToGlobal n b init e_cdir) (e_gdir : Event n) : Prop :=
  match hshim with
  | .encapGlobalCache _ _ =>
    ∃ e_gcache ∈ b,
      Event.clusterDirEncapCorrespondingGlobalCache n b e_cdir e_gcache ∧
      b.dirAccessOfRequest n init e_gcache e_gdir
  | .noGlobalCache _ _ =>
    ∃ e_gcache ∈ b,
      Event.clusterDirEncapsulatesGlobalCacheWithPerms n b init e_cdir e_gcache ∧
      b.dirAccessOfRequest n init e_gcache e_gdir

/-
inductive CompoundProtocol.globalDirEventOfClusterDir (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_cdir e_gdir : Event n) : Prop
| viaShim
  (hcdir_is_dir : e_cdir.isDirectoryEvent n)
  (hshim : Behaviour.Shim.ClusterToGlobal n b init e_cdir)
  (haccess : Behaviour.Shim.ClusterToGlobal.globalCacheAccessWithDir n b init e_cdir hshim e_gdir)
  : CompoundProtocol.globalDirEventOfClusterDir cmp b init e_cdir e_gdir
-/

structure CompoundProtocol.globalLinearizationEventOfRequest (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq : Event n) (hcreq_cluster : e_creq.isClusterCache) : Prop where
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  -- It's the hreq's_global_dir below that needs to be re-written as per the above TODO.
  hreq's_global_lin : ∃ e_gdir ∈ b,
    Behaviour.Shim.ClusterToGlobal.globalCacheAccessWithDir n b init hreq's_dir_access.choose
    (cmp.shimAxioms.clusterToGlobal b init hreq's_dir_access.choose hreq's_dir_access.choose_spec.right.isDirEvent)
    e_gdir

-- Try to see if this TODO is provable...

/-- Common structure: GLE ordering (write's GLE immediately before read's GLE) -/
structure Behaviour.readsFrom.gleImmediatelyBefore (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  hw_gle : CompoundProtocol.globalLinearizationEventOfRequest n cmp b init e_w hw_cluster
  hr_gle : CompoundProtocol.globalLinearizationEventOfRequest n cmp b init e_r hr_cluster
  gle_ordered : hw_gle.hreq's_global_lin.choose.OrderedBefore n hr_gle.hreq's_global_lin.choose
  gle_no_intermediate : ∀ e_inter ∈ b, ∀ (h_inter_cluster : e_inter.isClusterCache),
    ∀ (hinter_gle : CompoundProtocol.globalLinearizationEventOfRequest n cmp b init e_inter h_inter_cluster),
    ¬ (hw_gle.hreq's_global_lin.choose.OrderedBefore n hinter_gle.hreq's_global_lin.choose ∧
       hinter_gle.hreq's_global_lin.choose.OrderedBefore n hr_gle.hreq's_global_lin.choose)

/- is it possible to prove that if there's a cluster directory event `e_cdir`,
then there must be a cluster cache request event `e_creq` that encapsulates `e_cdir` and corresponds to `e_cdir`? -/

/-
NOTES:
- Let the `e_w` gle orderedBefore `e_r` gle be a precondition for rf of `e_w` and `e_r`.
(rule out `e_r` gle before `e_w` gle, and intermediate writes that break the rf relation)
-
-/


/-- Helper: downgrade immediately after write at the same cache -/
structure Behaviour.readsFrom.downgradeAfterLatestWrite (b : Behaviour n)
  (e_w e_r : Event n) : Prop where
  downgradeExistsAfter : ∃ e_down ∈ b, e_r.Encapsulates n e_down ∧ e_down.down ∧ e_down.cid = e_w.cid ∧ e_w.OrderedBefore n e_down
    -- ∀ e_inter ∈ b, e_inter.cid = e_w.cid →
    -- ¬ (e_inter.isWrite ∧ e_inter.OrderedBetween n e_w e_down)

/-- Case 1: Write with coherent permissions (has predecessor that got perms) -/
structure Behaviour.readsFrom.writeWithCoherentPred (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  w_not_down : ¬ e_w.down
  r_is_read : e_r.isRead
  r_not_down : ¬ e_r.down
  w_has_perms : b.reqHasPerms n init e_w
  w_has_pred : b.reqHasPermsSoDirPred n init e_w
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade : Behaviour.readsFrom.downgradeAfterLatestWrite n b e_w e_r

/-- Case 2: Write without permissions -/
structure Behaviour.readsFrom.writeNoPerms (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  w_not_down : ¬ e_w.down
  r_is_read : e_r.isRead
  r_not_down : ¬ e_r.down
  w_no_perms : b.reqMissingPerms n init e_w
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade_to_gcache :
    ∃ e_gcache ∈ b, (gle_ordering.hw_gle.hreq's_dir_access.choose).clusterDirEncapCorrespondingGlobalCache n b e_gcache ∧
      Behaviour.readsFrom.downgradeAfterLatestWrite n b e_gcache e_r

-- TODO: udpated to cover the "`e_w` has a ClusterLE" ordered after itself.
/-- Case 2: Write without permissions -/
structure Behaviour.readsFrom.writeNoPerms (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  w_not_down : ¬ e_w.down
  r_is_read : e_r.isRead
  r_not_down : ¬ e_r.down
  w_no_perms : b.reqMissingPerms n init e_w
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade_to_gcache : ∃ e_down ∈ b, e_r.Encapsulates n e_down ∧ e_down.down ∧
    e_down.protocol = .global ∧ e_down.isGlobalCache ∧
    ∃ e_gcache ∈ b, (gle_ordering.hw_gle.hreq's_dir_access.choose).clusterDirEncapCorrespondingGlobalCache n b e_gcache ∧
      e_gcache.OrderedBefore n e_down

/-- The Rf (reads-from) relation between a write request and a read request.
    The write's GLE must be immediately before the read's GLE (no intermediate GLE). -/
inductive Behaviour.readsFrom.diffCluster (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hdiff_cluster : e_w.protocol ≠ e_r.protocol) : Prop
| writeWithCoherentPerms
  (h : Behaviour.readsFrom.writeWithCoherentPred n cmp b init e_w e_r hw_cluster hr_cluster)
  : Behaviour.readsFrom.diffCluster cmp b init e_w e_r hw_cluster hr_cluster hdiff_cluster
| writeNoCoherentPerms
  (h : Behaviour.readsFrom.writeNoPerms n cmp b init e_w e_r hw_cluster hr_cluster)
  : Behaviour.readsFrom.diffCluster cmp b init e_w e_r hw_cluster hr_cluster hdiff_cluster

inductive Behaviour.readsFrom.sameCluster (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache)
  (hsame_cluster : e_w.protocol = e_r.protocol) : Prop
|

/- -- TODO (Attempted above.):
Define the rf relation between a write request `e_w` and a read request `e_r`:
assume the "globalLinearizationEventOfRequest" (GLE) of the write request `e_w_gle` is immediately before
the GLE of the read request `e_r_gle` (there is no intermediate GLE between them).
Define cases for the rf relation:
1. If `e_w`
  has coherent permissions (hits in cache, there's a predecessor req that gets perms for `e_w_gle`),
  then there exists a downgrade event `e_down` encapsulated by `e_r` (and `e_r_gle`) to `e_w`.
  This `e_down` is after `e_w` (and there is no other write event between `e_w` and `e_down`, at `e_w`'s cache)
2. If `e_w` has no coherent permissions, then there exists a downgrade event `e_down` encapsulated by `e_r` (and `e_r_gle`) to `e_w`'s global cache permissions.
  This `e_down` is after `e_w` (and there is no other write event between `e_w` and `e_down`, at `e_w`'s cache).
  Moreover, there exists a global cache event `e_gcache` that corresponds to the directory event that either gets global permissions from the global directory
  to `e_w`,
  or is just a global cache access request (already has permissions).
-/

/-
Cases to think about in the proof below.
1. If if `e_w` and `e_r` are in the same cluster.
-/

-- theorem Behaviour.readFrom_holds
--   : Behaviour.readsFrom  := by
--   sorry
