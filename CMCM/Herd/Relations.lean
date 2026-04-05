import CMCM.Herd.Defs
import CMCM.Herd.RelationCycles
import Mathlib

/-!
# Herd CMCM Relations

Define the `com` union (PPOi ∪ rfe ∪ fr ∪ co), acyclicity, and the CMCM theorem statement.

All relations are parameterized by linearization evidence (`lin₁ lin₂`),
making compoundLin the primary concept. From `lin`:
- `lin.compoundLin` = the compoundLin event
- `lin.cle` = the CLE (cluster linearization event)
- `lin.gle` = the GLE (global linearization event)

Uses `Relation.TransGen` from Mathlib for transitive closure.
-/

variable {n : Nat}

namespace Herd

/-! ## Union of CMCM relations -/

/-- The communication relation: rfe ∪ fr ∪ co.
    Parameterized by linearization evidence (provides compoundLin/CLE/GLE). -/
inductive com {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop where
  | rfe : Herd.rfe lin₁ lin₂ → com lin₁ lin₂
  | fr : Herd.fr lin₁ lin₂ → com lin₁ lin₂
  | co : Herd.co lin₁ lin₂ → com lin₁ lin₂

/-- The compoundLin event for e₁. -/
noncomputable def com.cmpLin₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₁.compoundLin

/-- The compoundLin event for e₂. -/
noncomputable def com.cmpLin₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₂.compoundLin

/-- CLE for e₁. -/
noncomputable def com.cle₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₁.cle

/-- CLE for e₂. -/
noncomputable def com.cle₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₂.cle

/-- GLE for e₁. -/
noncomputable def com.gle₁ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₁.gle

/-- GLE for e₂. -/
noncomputable def com.gle₂ {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂}
    (_ : com lin₁ lin₂) : Event n := lin₂.gle

/-! ## Generic acyclicity definitions -/

/-- A relation is cyclic if there exists an element reachable from itself
    via the transitive closure. -/
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x


theorem cyclic_eq_neg_acyclic {rel : α → α → Prop}
    : cyclic rel = ¬ Relation.Acyclic rel := by
  simp [cyclic, Relation.Acyclic]


end Herd
