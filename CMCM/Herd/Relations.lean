import CMCM.Herd.Defs
import CMCM.Herd.RelationCycles
import Mathlib

/-!
# Herd CMCM Relations

Define the `com` union (PPOi ∪ rfe ∪ fr ∪ co), acyclicity, and the CMCM theorem statement.

Uses `Relation.TransGen` from Mathlib for transitive closure.
-/

variable {n : Nat}

namespace Herd

/-! ## Union of CMCM relations -/

/-- The communication relation: rfe ∪ fr ∪ co.
    Defined over protocol events, parameterized by the compound protocol. -/
inductive com (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n)
    (e₁ e₂ : Event n) : Prop where
  | rfe : @Herd.rfe n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | fr : @Herd.fr n cmp b init e₁ e₂ → com cmp b init e₁ e₂
  | co : @Herd.co n cmp b init e₁ e₂ → com cmp b init e₁ e₂

/-- Extract globalLinearizationEventOfRequest for e₁ from any COM edge. -/
noncomputable def com.lin₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} : com cmp b init e₁ e₂ →
    CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁
  | .rfe h => h.w_cmpLin
  | .co h => h.w₁_cmpLin
  | .fr h => h.e₁_cmpLin

/-- Extract globalLinearizationEventOfRequest for e₂ from any COM edge. -/
noncomputable def com.lin₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} : com cmp b init e₁ e₂ →
    CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂
  | .rfe h => h.r_cmpLin
  | .co h => h.w₂_cmpLin
  | .fr h => h.e₂_cmpLin

/-- The compoundLin event for e₁ from any COM edge. -/
noncomputable def com.cmpLin₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} (h : com cmp b init e₁ e₂) : Event n :=
  h.lin₁.compoundLin

/-- The compoundLin event for e₂ from any COM edge. -/
noncomputable def com.cmpLin₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} (h : com cmp b init e₁ e₂) : Event n :=
  h.lin₂.compoundLin

/-- The CLE (cluster linearization event) for e₁, extracted from cmpLin₁'s evidence. -/
noncomputable def com.cle₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} (h : com cmp b init e₁ e₂) : Event n :=
  h.lin₁.cle

/-- The CLE for e₂, extracted from cmpLin₂'s evidence. -/
noncomputable def com.cle₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n} (h : com cmp b init e₁ e₂) : Event n :=
  h.lin₂.cle

/-- The hierarchical ordering: PPOi ∪ com, carrying communication evidence.

    Each constructor carries the full edge structure (PPOi or com), which
    contains the specific protocol events (linearization events, downgrades,
    e_r_cdir_down, etc.) that establish the ordering.

    Acyclicity is proven by extracting OB/Encapsulation chains from consecutive
    edges in any cycle. These chains compose (via Trans instances on OB/EncapsulatedBy)
    into a temporal loop, contradicting OB irreflexivity. -/
inductive hierarchicallyOrdered
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e₁ e₂ : Event n) : Prop where
  /-- PPOi: local cache ordering (e₁ OB e₂ on same cache, PPO pair) -/
  | ppoi (h : @PPOi n b e₁ e₂)
  /-- COM: communication ordering (rfe/co/fr with downgrade/communication evidence) -/
  | com (h : com cmp b init e₁ e₂)

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
