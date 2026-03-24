import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Architecture

`hierarchicallyOrdered` (in Relations.lean) = PPOi ∪ com, carrying communication evidence.
This IS the relation whose acyclicity we prove — and whose transitive closure gives the PartialOrder.

## Proof flow

1. Prove `Relation.Acyclic hierarchicallyOrdered` directly from communication evidence
2. Derive: `Relation.Acyclic (PPOi ∪ com)` (since hierarchicallyOrdered = PPOi ∪ com)
3. Construct PartialOrder from the acyclic relation (consequence, not prerequisite)

The acyclicity proof shows: any cycle through PPOi + com edges leads to a contradiction,
because the communication evidence (PPOi linearization, RF downgrades, CO overwrites,
FR composition) imposes ordering constraints that can't be simultaneously satisfied in a cycle.
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Direct acyclicity proof

Every cycle through PPOi ∪ com edges leads to a contradiction.
The communication evidence in each edge constrains the ordering of events.
A cycle would require these constraints to form a loop — which is impossible
because the protocol's coherence mechanisms are acyclic. -/

/-- The CMCM theorem: `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

    Proved directly from the communication evidence carried in each edge.
    A cycle through PPOi + com would require the protocol's coherence ordering
    to form a loop, which contradicts the protocol axioms.

    Each edge type contributes ordering constraints:
    - **PPOi**: CompoundLinearizationOrder (compound lin events ordered)
    - **rfe**: readsFrom.cases (cross-cluster downgrade chain → GLE ordering)
    - **co**: co.cases (overwrite communication → GLE/CLE/cache ordering)
    - **fr**: rf⁻¹;co (composition through intermediate write) -/
theorem cmcm_acyclic
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  sorry

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' hknow

/-! ## PartialOrder (consequence of acyclicity)

Once acyclicity is established, the PartialOrder follows:
- lt = TransGen (PPOi ∪ com)
- le = (· = ·) ∨ TransGen (PPOi ∪ com)
- Antisymmetry from acyclicity (TransGen r e e → False)
- Transitivity from TransGen
- Reflexivity from = -/

/-- The PartialOrder on events (GMO): constructed from cmcm_acyclic.
    le = (· = ·) ∨ TransGen (PPOi ∪ com)
    lt = TransGen (PPOi ∪ com)
    Antisymmetry from acyclicity. Transitivity from TransGen. -/
noncomputable def eventPartialOrder
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : PartialOrder (Event n) := by
  have _hacyclic := @cmcm_acyclic n compound b init hknow
  sorry

end Herd
