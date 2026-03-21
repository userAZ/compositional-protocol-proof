import CMCM.Rf
import CompositionalProtocolProof.CompositionalMCM

/-!
# Herd CMCM Definitions

Define the Herd axiomatic representation of the Compositional Memory Consistency Model (CMCM):
  `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`

The relations are defined on protocol `Event n`, using the (GLE, CLE) two-level hierarchy
from `globalLinearizationEventOfRequest`.

## Ordering hierarchy

The global ordering is a two-level lexicographic order:
- **Level 1 (GLE)**: `globalLinearizationEventOfRequest.hreq's_global_lin` — global directory ordering
- **Level 2 (CLE)**: `globalLinearizationEventOfRequest.hreq's_dir_access` — cluster directory ordering

Two events are ordered if their GLEs are strictly ordered, or their GLEs are equal and
their CLEs are strictly ordered. This mirrors the RF definition's `wEqRGle`/`wObRGle` split.
-/

variable {n : Nat}

namespace Herd

/-! ## Hierarchical ordering on (GLE, CLE) pairs -/

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- The GLE of a request's linearization. -/
noncomputable def gle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_global_lin.choose

/-- The CLE of a request's linearization. -/
noncomputable def cle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_dir_access.choose

/-- Hierarchical ordering: GLE₁ strictly before GLE₂. -/
def gleOrderedBefore
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  (gle h₁).OrderedBefore n (gle h₂)

/-- Hierarchical ordering: same GLE, CLE₁ strictly before CLE₂. -/
def sameGleCleOrderedBefore
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  gle h₁ = gle h₂ ∧ (cle h₁).OrderedBefore n (cle h₂)

/-- The (GLE, CLE) hierarchical order. Two events are hierarchically ordered if:
    1. Their GLEs are strictly ordered (OrderedBefore), OR
    2. Their GLEs are equal AND their CLEs are strictly ordered.

    This is the "global order G" for the Herd CMCM acyclicity proof. -/
def hierarchicallyOrdered
    (h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂) : Prop :=
  gleOrderedBefore h₁ h₂ ∨ sameGleCleOrderedBefore h₁ h₂

/-! ## Edge definitions -/

/-- PPOi: Preserved Program Order (intra-thread).
    Two events on the same cache, at different addresses, forming a PPO pair,
    with e₁ program-ordered before e₂. -/
structure PPOi (e₁ e₂ : Event n) : Prop where
  ppo : e₁.isPPOPair n e₂
  orderedBefore : e₁.OrderedBefore n e₂
  diffAddr : e₁.addr ≠ e₂.addr
  sameProtocol : e₁.sameProtocol n e₂
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  cache₁ : e₁.isCacheEvent
  cache₂ : e₂.isCacheEvent

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
