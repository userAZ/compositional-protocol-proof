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

structure Event.isClusterCache (e_dir : Event n) : Prop where
  dirAtDir : e_dir.isCacheEvent
  dirCluster : e_dir.protocol = .cluster1 ∨ e_dir.protocol = .cluster2

structure CompoundProtocol.globalLinearizationEventOfRequest (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_creq : Event n) (hcreq_cluster : e_creq.isClusterCache) : Prop where
  hreq's_dir_access : ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e_creq e_cdir
  hreq's_global_lin: ∃ e_gdir ∈ b, CompoundProtocol.clusterDirGlobalLin n cmp.shimAxioms b init hreq's_dir_access.choose e_gdir (Behaviour.dirAccessOfRequest.isDirEvent n hreq's_dir_access.choose_spec.right)

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

/-- Helper: downgrade immediately after write at the same cache -/
structure Behaviour.readsFrom.downgradeImmediatelyAfterWrite (b : Behaviour n)
  (e_w e_r : Event n) : Prop where
  down_exists : ∃ e_down ∈ b, e_r.Encapsulates n e_down ∧ e_down.down ∧ e_down.cid = e_w.cid
  down_immediately_after : ∃ e_down ∈ b, e_r.Encapsulates n e_down ∧ e_w.OrderedBefore n e_down ∧
    ∀ e_inter ∈ b, e_inter.cid = e_w.cid →
    ¬ (e_w.OrderedBefore n e_inter ∧ e_inter.OrderedBefore n e_down)

/-- Case 1: Write with coherent permissions (has predecessor that got perms) -/
structure Behaviour.readsFrom.writeWithCoherentPred (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  r_is_read : e_r.isRead
  w_has_perms : b.reqHasPerms n init e_w
  w_has_pred : b.reqHasPermsSoDirPred n init e_w
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade : Behaviour.readsFrom.downgradeImmediatelyAfterWrite n b e_w e_r

/-- Case 2: Coherent write request -/
structure Behaviour.readsFrom.coherentWriteRequest (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  r_is_read : e_r.isRead
  w_is_coherent : e_w.isCoherent
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade : Behaviour.readsFrom.downgradeImmediatelyAfterWrite n b e_w e_r

/-- Case 3: Non-coherent write without permissions -/
structure Behaviour.readsFrom.nonCoherentWrite (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop where
  w_is_write : e_w.isWrite
  r_is_read : e_r.isRead
  w_non_coherent : ¬ e_w.isCoherent
  w_no_perms : b.reqMissingPerms n init e_w
  gle_ordering : Behaviour.readsFrom.gleImmediatelyBefore n cmp b init e_w e_r hw_cluster hr_cluster
  downgrade_to_gcache : ∃ e_down ∈ b, e_r.Encapsulates n e_down ∧ e_down.down ∧
    e_down.protocol = .global ∧ e_down.isGlobalCache

/-- The Rf (reads-from) relation between a write request and a read request.
    The write's GLE must be immediately before the read's GLE (no intermediate GLE). -/
inductive Behaviour.readsFrom (shimAxioms : ShimAxioms n) (cmp : CompoundProtocol n) (b : Behaviour n)
  (init : InitialSystemState n) (e_w e_r : Event n)
  (hw_cluster : e_w.isClusterCache) (hr_cluster : e_r.isClusterCache) : Prop
| writeWithCoherentPerms
  (h : Behaviour.readsFrom.writeWithCoherentPred n cmp b init e_w e_r hw_cluster hr_cluster)
  : Behaviour.readsFrom shimAxioms cmp b init e_w e_r hw_cluster hr_cluster
| coherentWriteRequestNoPerms
  (h : Behaviour.readsFrom.coherentWriteRequest n cmp b init e_w e_r hw_cluster hr_cluster)
  : Behaviour.readsFrom shimAxioms cmp b init e_w e_r hw_cluster hr_cluster
| nonCoherentWriteNoPerms
  (h : Behaviour.readsFrom.nonCoherentWrite n cmp b init e_w e_r hw_cluster hr_cluster)
  : Behaviour.readsFrom shimAxioms cmp b init e_w e_r hw_cluster hr_cluster

/- -- TODO (Attempted above.):
Define the rf relation between a write request `e_w` and a read request `e_r`:
assume the "globalLinearizationEventOfRequest" (GLE) of the write request `e_w_gle` is immediately before
the GLE of the read request `e_r_gle` (there is no intermediate GLE between them).
Define cases for the rf relation:
1. If `e_w_gle`
  has coherent permissions (hits in cache, there's a predecessor req that gets perms for `e_w_gle`),
  then there exists a downgrade event `e_down` encapsulated by `e_r` (and `e_r_gle`) to `e_w`.
  This `e_down` is immediately after `e_w` (there is no intermediate cache event between `e_w` and `e_down`, at `e_w`'s cache)
2. If `e_w_gle`'s stateAfter is coherent (`e_w_gle` is a coherent request!) the there must exist a downgrade `e_down`
  that satisfies the same conditions as above. (`e_r` downgrades `e_w`'s coherent permissions)
3. If `e_w_gle` is a non-coherent request, and does not have coherent permissions then `e_r`
  encapsulates a downgrade `e_down` to `e_w`'s global cache permissions.
-/

/-! # Global Linearization Event (GLE) and Rf (Reads-From) Definitions

This file defines:
1. The Global Linearization Event (GLE) of a request
2. The Rf (reads-from) relation between write and read requests
3. A theorem proving the Rf relation holds

## Global Linearization Event (GLE)

The GLE is the global directory access event corresponding to a request `e_req`.
It relates `e_req` to the global directory linearization event that linearizes it globally.

The definition follows the linearization hierarchy:
- First get the request's linearization event (cache or directory)
- If it linearizes in cache: trace back to the preceding cluster directory that obtained permissions,
  then find that directory's global linearization event
- If it linearizes in cluster directory: find that directory's global linearization event
  - If the cluster directory has global cache permissions: the GLE comes from the global cache's linearization
  - If not: the cluster directory encapsulates a global cache request whose linearization is the GLE
- Similarly for global protocol events (cache vs directory linearization)

-/

/- The Global Linearization Event (GLE) of a request `e_req`.
This follows the compound linearization infrastructure to trace through the hierarchy:
request → cluster linearization → compound linearization → cluster directory → global linearization → GLE

We build up from cmp.compoundLinearizationEvent which gives us the compound linearization event.
If it's a clusterCacheLin, we trace back to the predecessor directory that got permissions.
If it's a clusterDirLin, we extract the directory and handle the clusterDirectoryLinearizationEvent cases:
  - If gcache already has perms: GLE is the predecessor directory that gave gcache perms
  - If gcache doesn't have perms: GLE is the encapsulated global directory access
-/
