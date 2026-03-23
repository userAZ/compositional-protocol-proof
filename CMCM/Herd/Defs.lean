import CMCM.Rf
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

/-- Hierarchical ordering: GLE₁ strictly before GLE₂. -/
def gleOrderedBefore
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  (gle h₁).OrderedBefore n (gle h₂)

/-- The (GLE, CLE, cache) 3-level lexicographic order. Two events are hierarchically
    ordered at the highest level where they differ:
    1. GLE₁ strictly before GLE₂, OR
    2. Same GLE, CLE₁ strictly before CLE₂, OR
    3. Same GLE and CLE, cache event e₁ strictly before e₂.

    GCR is redundant (CLE → GCR → GLE is functionally determined).
    This is the ranking function for the Herd CMCM acyclicity proof. -/
def hierarchicallyOrdered
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  gleOrderedBefore h₁ h₂ ∨
  (gle h₁ = gle h₂ ∧
    ((cle h₁).OrderedBefore n (cle h₂) ∨
      (cle h₁ = cle h₂ ∧ e₁.OrderedBefore n e₂)))

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
  ordering : co.cases w₁_lin w₂_lin

/-- fr: From-reads (rf⁻¹ ; co⁺).
    A read e₁ reads from some write e_w, and e₂ is reachable from e_w by a
    transitive chain of co steps.

    Carries BOTH:
    - `witness`: the rf⁻¹ ; co⁺ decomposition (protocol-level justification)
    - `ordering`: direct `co.cases` between e₁ and e₂ (hierarchy ordering)

    The direct ordering is needed because composing rf hierarchy(e_w, e₁) + co hierarchy(e_w, e₂)
    does not automatically give hierarchy(e₁, e₂) — the rf witness's "no intermediate write"
    condition is what forces e₁ before e₂ in the hierarchy. -/
structure fr (e₁ e₂ : Event n) : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  e₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  e₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- Intermediate write e_w that e₁ reads from, with co⁺(e_w, e₂). -/
  witness : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    Relation.TransGen (@co n compound b init) e_w e₂
  /-- Direct ordering between e₁ and e₂ (same case structure as co). -/
  ordering : co.cases e₁_lin e₂_lin

end Herd
