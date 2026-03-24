import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Architecture

`hierarchicallyOrdered` (in Relations.lean) = PPOi ∪ com with communication evidence.
This IS the relation — no intermediate ranking function.

The PartialOrder is built from PPOi ∪ com:
- **PPOi** ⊆ lt: CompoundMCM gives compound linearization ordering
- **COM** ⊆ lt: RF/CO/FR communication evidence gives ordering

Acyclicity follows from `CMCM.suffices_inclusion`: PPOi ∪ com ⊆ PartialOrder.lt.

## Proof obligations

For each edge type, show it's contained in the PartialOrder's strict order:
- **PPOi**: CompoundLinearizationOrder (from CompoundMCM) embeds into the PartialOrder
- **rfe**: readsFrom.cases gives ordering (GLE from wObRGle, CLE/cache from wEqRGle)
- **co**: co.cases gives ordering
- **fr**: rf⁻¹;co composition gives ordering
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## The PartialOrder on events

The PartialOrder captures the protocol's coherence ordering. Its strict order (lt)
contains both PPOi (via CompoundLinearizationOrder) and com (via communication evidence).

Construction: PPOi ∪ com is acyclic (the CMCM theorem). The transitive closure of
an acyclic relation gives a strict partial order. Adding reflexivity gives ≤. -/

/-- The PartialOrder on events induced by the protocol's coherence ordering.
    Built from PPOi (CompoundMCM) and com (RF/CO/FR communication).
    Its lt contains PPOi ∪ com. -/
noncomputable def eventPartialOrder
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : PartialOrder (Event n) := sorry

/-! ## PPOi ⊆ PartialOrder.lt -/

/-- PPOi edges are contained in the PartialOrder's strict order.
    Uses CompoundMCM's `enforce_compound_consistency` for different-address pairs
    and protocol reasoning for same-address pairs. -/
theorem ppoi_lt
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : @PPOi n b e₁ e₂)
    : @LT.lt _ (eventPartialOrder hknow).toLT e₁ e₂ := by
  sorry

/-! ## COM ⊆ PartialOrder.lt -/

/-- rfe edges are contained in the PartialOrder's strict order.
    From readsFrom.cases: wObRGle gives GLE ordering (cross-cluster downgrade). -/
theorem rfe_lt
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : @Herd.rfe n compound b init e₁ e₂)
    : @LT.lt _ (eventPartialOrder hknow).toLT e₁ e₂ := by
  sorry

/-- co edges are contained in the PartialOrder's strict order.
    From co.cases: communication at GLE/CLE/cache level. -/
theorem co_lt
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : @Herd.co n compound b init e₁ e₂)
    : @LT.lt _ (eventPartialOrder hknow).toLT e₁ e₂ := by
  sorry

/-- fr edges are contained in the PartialOrder's strict order.
    From rf⁻¹;co composition: communication through intermediate write e_w. -/
theorem fr_lt
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : @Herd.fr n compound b init e₁ e₂)
    : @LT.lt _ (eventPartialOrder hknow).toLT e₁ e₂ := by
  sorry

/-- All com edges are contained in the PartialOrder's strict order. -/
theorem com_lt
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h : com compound b init e₁ e₂)
    : @LT.lt _ (eventPartialOrder hknow).toLT e₁ e₂ := by
  cases h with
  | rfe h => exact rfe_lt hknow h
  | co h => exact co_lt hknow h
  | fr h => exact fr_lt hknow h

/-! ## Main theorems -/

/-- The CMCM theorem: `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

    PPOi ∪ com ⊆ PartialOrder.lt, and PartialOrder.lt is acyclic.
    PPOi ordering comes from CompoundMCM (compound linearization events).
    COM ordering comes from RF/CO/FR communication evidence (downgrades at common levels). -/
theorem cmcm_acyclic
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  letI := eventPartialOrder hknow
  exact CMCM.suffices_inclusion (@PPOi n b) (com compound b init)
    (fun _ _ h => ppoi_lt hknow h)
    (fun _ _ h => com_lt hknow h)

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' hknow

end Herd
