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

/-- PPOi: Preserved Program Order (intra-cluster).
    Two events on the same cache forming a PPO pair, with e₁ ordered before e₂.
    Both events must be in the behaviour. -/
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
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- CLE ordering for PPOi: the directory ordering of CLEs follows the cache ordering.
      Either CLE₁.oEnd < CLE₂.oEnd or same CLE with e₁ OB e₂.
      Derived from dir_ordered + dirAccessOfRequest case analysis (9-case). -/
  cle_advance :
    let e₁_lin := hknow_dir_access compound b init e₁
    let e₂_lin := hknow_dir_access compound b init e₂
    (e₁_lin.hreq's_dir_access.choose.oEnd < e₂_lin.hreq's_dir_access.choose.oEnd) ∨
    (e₁_lin.hreq's_dir_access.choose.oEnd = e₂_lin.hreq's_dir_access.choose.oEnd ∧
     Event.oEnd n e₁ < Event.oEnd n e₂)

/-- rfe: Reads-from external.
    A write e₁ that is read by e₂, at the same address, from different clusters. -/
structure rfe (e₁ e₂ : Event n) : Prop where
  write : e₁.isWrite
  read : e₂.isRead
  sameAddr : e₁.addr = e₂.addr
  diffProtocol : e₁.diffProtocol n e₂
  w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  r_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  readsFrom : Behaviour.readsFrom.cases write read w_lin r_lin hknow_dir_access
  /-- CLE ordering for rfe: writer's CLE before reader's CLE. -/
  cle_advance :
    (w_lin.hreq's_dir_access.choose.oEnd < r_lin.hreq's_dir_access.choose.oEnd) ∨
    (w_lin.hreq's_dir_access.choose.oEnd = r_lin.hreq's_dir_access.choose.oEnd ∧
     Event.oEnd n e₁ < Event.oEnd n e₂)

/-- CO same-GLE sub-cases (Prop-valued, mirroring `readsFrom.wEqRGle.cases`).
    When both writes share a GLE, ordering comes from CLE or cache level. -/
inductive co.sameGle.cases
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
    (w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop
  /-- Same CLE: ordering at cache level (mirrors RF's `EqGleCle.case.wObR`). -/
  | sameCle
    (cle_eq : w₁_lin.hreq's_dir_access.choose = w₂_lin.hreq's_dir_access.choose)
    (cache_ob : e₁.OrderedBefore n e₂)
  /-- Different CLE: ordering from CLE sub-cases (reuses RF's `SameCluster.cleOb.cleOrdering.Cases`). -/
  | diffCle
    (cle_ordering : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases w₁_lin w₂_lin)

/-- CO communication pattern cases (Prop-valued, mirroring `readsFrom.cases`).
    Two writes to the same address, with w₂ overwriting w₁ through the protocol
    hierarchy. Reuses RF's Prop-valued sub-types where possible. -/
inductive co.cases
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
    (w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop
  /-- Same GLE with CLE sub-cases (mirrors `readsFrom.cases.wEqRGle`). -/
  | sameGle
    (gle_eq : w₁_lin.hreq's_global_lin.choose = w₂_lin.hreq's_global_lin.choose)
    (cle_cases : co.sameGle.cases w₁_lin w₂_lin)
  /-- GLE₁ strictly before GLE₂, with CLE sub-cases (mirrors `readsFrom.cases.wObRGle`).
      Reuses RF's `gleOB.Cluster.SameOrDiff.cleOrdering.Cases` (Prop, no isRead dependency). -/
  | wObRGle
    (gle_ob : w₁_lin.hreq's_global_lin.choose.OrderedBefore n w₂_lin.hreq's_global_lin.choose)
    (cle_cases : CompoundProtocol.gleOB.Cluster.SameOrDiff.cleOrdering.Cases w₁_lin w₂_lin)

/-- co: Coherence order.
    Two writes to the same address, where w₂ overwrites w₁. Communication pattern
    captured by `co.cases` (Prop-valued, mirroring `readsFrom.cases` structure). -/
structure co (e₁ e₂ : Event n) : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  ordering : co.cases w₁_lin w₂_lin

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
      (full readsFrom.cases structure + NoInterveningWrites), and e₂ overwrites e_w via co⁺. -/
  comm : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    NoInterveningWrites e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    Relation.TransGen (@co n compound b init) e_w e₂
  /-- CLE ordering for fr: derived from rf⁻¹;co⁺ composition + noBetween.
      The read's CLE is before or equal to the write's CLE (in the directory ordering). -/
  cle_advance :
    (e₁_lin.hreq's_dir_access.choose.oEnd < e₂_lin.hreq's_dir_access.choose.oEnd) ∨
    (e₁_lin.hreq's_dir_access.choose.oEnd = e₂_lin.hreq's_dir_access.choose.oEnd ∧
     Event.oEnd n e₁ < Event.oEnd n e₂)

end Herd
