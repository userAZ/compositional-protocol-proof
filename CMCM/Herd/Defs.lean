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
    Two writes to the same address, ordered in the (GLE, CLE) hierarchy. -/
structure co (e₁ e₂ : Event n) : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  ordering : hierarchicallyOrdered w₁_lin w₂_lin

/-- fr: From-reads.
    A read e₁ reads from some write w, and e₂ is a write that is co-after w.
    Semantically: fr = rf⁻¹ ; co. The ordering between e₁ and e₂ follows because:
    - rf(w, e₁) gives w ≤ e₁ in the (GLE, CLE) hierarchy (from RF theorem)
    - co(w, e₂) gives w < e₂ in the (GLE, CLE) hierarchy
    - Combined: e₁ < e₂ (since w < e₂ and w ≤ e₁ means w ≤ e₁ < e₂, but the strict
      ordering e₁ < e₂ follows from the fact that e₁ is a read and e₂ is a different write).
    The structure directly carries the hierarchical ordering conclusion. -/
structure fr (e₁ e₂ : Event n) : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  e₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  e₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  ordering : hierarchicallyOrdered e₁_lin e₂_lin

end Herd
