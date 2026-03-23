import CMCM.Rf
import CompositionalProtocolProof.CompositionalMCM

/-!
# Herd CMCM Definitions

Define the Herd axiomatic representation of the Compositional Memory Consistency Model (CMCM):
  `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`

The relations are defined on protocol `Event n`, using a 4-level hierarchy
from `globalLinearizationEventOfRequest`.

## Ordering hierarchy

The global ordering is a 4-level lexicographic order (highest to lowest):
1. **GLE** (global directory): `hreq's_global_lin.choose`
2. **GCR** (global cache request): `cDir'sGReq.wrapper` corresponding to the CLE
3. **CLE** (cluster directory): `hreq's_dir_access.choose`
4. **Cache event**: the request event itself (`e₁.OrderedBefore e₂`)

Two events are ordered at the highest level where they differ. When GLE, GCR, and CLE
are all equal (e.g., events sharing a predecessor's CLE), the cache event ordering breaks
the tie. The RF definition demonstrates the GLE/CLE split with `wEqRGle`/`wObRGle`.
-/

variable {n : Nat}

namespace Herd

/-! ## Hierarchical ordering on (GLE, GCR, CLE, cache) tuples -/

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- The GLE (global directory event) of a request's linearization. -/
noncomputable def gle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_global_lin.choose

/-- The GCR (global cache request) of a request's linearization. -/
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

/-- The (GLE, GCR, CLE, cache) 4-level lexicographic order. Two events are hierarchically
    ordered at the highest level where they differ:
    1. GLE₁ strictly before GLE₂, OR
    2. Same GLE, GCR₁ strictly before GCR₂, OR
    3. Same GLE and GCR, CLE₁ strictly before CLE₂, OR
    4. Same GLE, GCR, and CLE, cache event e₁ strictly before e₂.

    This is the ranking function for the Herd CMCM acyclicity proof. -/
def hierarchicallyOrdered
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  gleOrderedBefore h₁ h₂ ∨
  (gle h₁ = gle h₂ ∧
    ((gcr h₁).OrderedBefore n (gcr h₂) ∨
      (gcr h₁ = gcr h₂ ∧
        ((cle h₁).OrderedBefore n (cle h₂) ∨
          (cle h₁ = cle h₂ ∧ e₁.OrderedBefore n e₂)))))

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

/-- co: Coherence order.
    Two writes to the same address, where w₂ overwrites w₁. Mirrors the RF theorem
    structure: the communication pattern between w₁ and w₂ is captured by
    `gleOrdering.Cases` — w₂ downgrades w₁'s ownership through the same protocol
    mechanisms as the RF theorem (downgrade chain through GLE/CLE hierarchy).

    `gleOrdering.Cases` provides either:
    - `sameGle`: same GLE, with CLE sub-cases (same CLE, CLE ordering, or downgrade at writer)
    - `wObRGle`: GLE₁ strictly before GLE₂, with same/diff cluster CLE sub-cases

    Wrapped in `Nonempty` since `gleOrdering.Cases` lives in `Type` (not `Prop`). -/
structure co (e₁ e₂ : Event n) : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  ordering : Nonempty (CompoundProtocol.gleOrdering.Cases w₁_lin w₂_lin)

/-- fr: From-reads (rf⁻¹ ; co).
    A read e₁ reads from some write e_w, and e₂ is a write that is co-after e_w.
    The intermediate write e_w is existentially witnessed:
    - `readsFrom`: captures the rf(e_w, e₁) communication pattern via `readsFrom.cases`
    - `co_ordering`: captures the co(e_w, e₂) communication pattern via `gleOrdering.Cases`

    This decomposition into rf⁻¹ and co reflects the protocol communication:
    - rf: e₁ reads e_w's data (downgrade chain from e₁ to e_w)
    - co: e₂ overwrites e_w (downgrade chain from e₂ to e_w) -/
structure fr (e₁ e₂ : Event n) : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  e₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  e₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- Intermediate write e_w that e₁ reads from, with co(e_w, e₂).
      Existentially quantified since `Event n` and `gleOrdering.Cases` are not `Prop`. -/
  witness : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin e₁_lin hknow_dir_access ∧
    Nonempty (CompoundProtocol.gleOrdering.Cases e_w_lin e₂_lin)

end Herd
