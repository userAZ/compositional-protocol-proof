import CMCM.Rf
import CMCM.RfProofDefs
import CompositionalProtocolProof.CompositionalMCM

/-!
# Herd CMCM Definitions

Define the Herd axiomatic representation of the Compositional Memory Consistency Model (CMCM):
  `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`

The relations are defined on protocol `Event n`, using a 3-level hierarchy
from `globalLinearizationEventOfRequest`.

## Ordering hierarchy

The global ordering is a 3-level lexicographic order (highest to lowest):
1. **GLE** (global directory): `hreq's_global_lin.choose`
2. **CLE** (cluster directory): `hreq's_dir_access.choose`
3. **Cache event**: the request event itself (`e₁.OrderedBefore e₂`)

GCR is redundant: CLE determines GCR (functionally) which determines GLE.
Two events are ordered at the highest level where they differ.
The RF definition demonstrates the GLE/CLE split with `wEqRGle`/`wObRGle`.
-/

variable {n : Nat}

namespace Herd

/-! ## Hierarchical ordering on (GLE, CLE, cache) tuples -/

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- The GLE (global directory event) of a request's linearization. -/
noncomputable def gle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_global_lin.choose

/-- The GCR (global cache request) of a request's linearization.
    Retained for the `cle_eq_implies_gle_eq` chain; not used in hierarchicallyOrdered. -/
noncomputable def gcr
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init h.hreq's_dir_access

/-- The CLE (cluster directory event) of a request's linearization. -/
noncomputable def cle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_dir_access.choose

/-! ## Edge definitions -/

/-- PPOi: Preserved Program Order (intra-cache).
    Two events on the same cache forming a PPO pair, with e₁ ordered before e₂.
    CLE ordering is DERIVED in the proof (from dir_ordered + dirAccessOfRequest
    for same-addr, CompoundLinearizationOrder for diff-addr). -/
structure PPOi (e₁ e₂ : Event n) : Prop where
  ppo : e₁.isPPOPair n e₂
  orderedBefore : e₁.OrderedBefore n e₂
  sameProtocol : e₁.sameProtocol n e₂
  sameCid : e₁.sameCid n e₂
  sameCid' : e₁.cid = e₂.cid
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  cache₁ : e₁.isCacheEvent
  cache₂ : e₂.isCacheEvent
  in_b₁ : e₁ ∈ b
  in_b₂ : e₂ ∈ b

/-- rfe: Reads-from external (different cache).
    A write e₁ that is read by e₂, at the same address, from different caches.
    "External" means different cache (struct), not necessarily different cluster. -/
structure rfe (e₁ e₂ : Event n) : Prop where
  write : e₁.isWrite
  read : e₂.isRead
  sameAddr : e₁.addr = e₂.addr
  diffCache : e₁.struct ≠ e₂.struct
  w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  r_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  readsFrom : Behaviour.readsFrom.cases write read w_lin r_lin hknow_dir_access

/-- CO communication ordering: describes HOW e_w2 overwrites e_w1.
    Organized by communication level (like RF's `readsFrom.cases` but for writes).
    Each constructor describes the specific communication mechanism.
    Parameterized by both events, their write evidence, and linearizations (like RF). -/
inductive co.ordering
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
    (w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop
  /-- Same cache: direct cache ordering. Both writes at the same cache,
      serialized by the cache. Evidence: e₁ OB e₂ + same CLE. -/
  | sameCache
    (same_cle : w₁_lin.hreq's_dir_access.choose = w₂_lin.hreq's_dir_access.choose)
    (cache_ob : e₁.OrderedBefore n e₂)
  /-- Same cluster, different cache: cluster directory serializes the writes.
      The second write's request triggers a downgrade at the first write's cache.
      Evidence: CLE ordering from SameCluster.cleOb.cleOrdering.Cases
      (carries wImmPredRCle or evictOrReadBetween with downgrade chain). -/
  | sameClusDiffCache
    (same_protocol : e₁.sameProtocol n e₂)
    (cle_ordering : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases w₁_lin w₂_lin)
  /-- Different cluster: cross-cluster downgrade chain.
      The second write's request propagates through global directory to trigger
      a downgrade at the first write's cluster.
      Evidence: DifferentCluster.cleOB.cleOrdering.Cases
      (carries wCleImmPredDown or evictOrReadBetweenWAndRDown with wObRDown + encapDirRelation). -/
  | diffClus
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (cle_ordering : CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases w₁_lin w₂_lin)

/-- co: Coherence order.
    Two writes to the same address, where w₂ overwrites w₁.
    Communication evidence describes HOW the overwrite happens (same cache,
    same cluster diff cache, or diff cluster), using the same downgrade chain
    structures as RF. -/
structure co (e₁ e₂ : Event n) : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  comm : co.ordering w₁_lin w₂_lin

/-- fr: From-reads (rf⁻¹ ; co⁺).
    A read e₁ reads from some write e_w, and e₂ is a write reachable from e_w
    by a transitive chain of co steps.

    The rf⁻¹ part carries the full `readsFrom.cases` structure (communication
    events, noBetween conditions, same/diff cache cases). The co part is a
    transitive chain of co steps, each carrying its own communication pattern.

    The hierarchy ordering between e₁ and e₂ is DERIVED from composing the
    rf communication (how e₁ met e_w) with the co communication (how e₂
    overwrote e_w), using rf's noBetween to establish the composition. -/
structure fr (e₁ e₂ : Event n) : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  e₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  e₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- rf⁻¹ ; co⁺ decomposition: e₁ reads from e_w at some communication level
      (full readsFrom.cases structure + NoInterveningWrites), and e₂ overwrites e_w via co⁺.
      CLE ordering is DERIVED in the proof from rf + co + NoInterveningWrites composition. -/
  comm : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    NoInterveningWrites e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    Relation.TransGen (@co n compound b init) e_w e₂

end Herd
