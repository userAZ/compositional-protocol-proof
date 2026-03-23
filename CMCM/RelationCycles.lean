import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder

variable {α : Type _}

@[simp] def Relation.Union (r₁ r₂ : α → α → Prop) := λ x y ↦ r₁ x y ∨ r₂ x y

abbrev Relation.Acyclic (r : α → α → Prop) := ∀a : α, ¬ Relation.TransGen r a a

theorem partial_oder_acyclic [inst : PartialOrder α] : Relation.Acyclic inst.lt  := by
  intro a h
  suffices ∀ b, Relation.TransGen inst.lt a b → a < b by
    exact lt_irrefl a (this a h)
  intro b hab
  induction hab with
  | single h => exact h
  | tail _ hbc ih => exact lt_trans ih hbc

--local notation:50 r₁ " ∪ " r₂ => Relation.Union r₁ r₂
instance : Union (α → α → Prop) where
  union := Relation.Union

instance : HasSubset (α → α → Prop) where
  Subset := λ r₁ r₂ => ∀ x y, r₁ x y → r₂ x y

-- Helper: TransGen r₁ ∪ TransGen r₂ ⊆ TransGen (r₁ ∪ r₂)
theorem transgen_union_supset (r₁ r₂ : α → α → Prop) :
  Relation.TransGen r₁ ∪ Relation.TransGen r₂ ⊆ Relation.TransGen (r₁ ∪ r₂) := by
  intro x y h
  simp [Union.union] at h ⊢
  cases h with
  | inl h => apply Relation.TransGen.mono _ h; intro a b hab; left; exact hab
  | inr h => apply Relation.TransGen.mono _ h; intro a b hab; right; exact hab


theorem transgen_subset {r₁ r₂ : α → α → Prop} :
  r₁ ⊆ r₂ → Relation.TransGen r₁ ⊆ Relation.TransGen r₂ := by
  intro h x y hxy
  exact Relation.TransGen.mono h hxy

theorem union_symm (r₁ r₂ : α → α → Prop) : r₁ ∪ r₂ = r₂ ∪ r₁ := by
  ext x y
  simp [Union.union]; grind


theorem union_acyclic_in_partial_order {r₁ r₂ : α → α → Prop}
  [inst : PartialOrder α] (hunion : r₁ ∪ r₂ ⊆ inst.lt) : Relation.Acyclic (r₁ ∪ r₂) := by
  intro a hrefl
  have htr := transgen_subset hunion a a hrefl
  have lt_trans : Transitive inst.lt := by exact transitive_of_trans LT.lt
  rw [Relation.transGen_eq_self lt_trans] at htr
  grind


theorem CMCM.suffices_inclusion (ppo com : α → α → Prop) [inst : PartialOrder α]
   (hppo : ppo ⊆ inst.lt) (hcom : com ⊆ inst.lt) : Relation.Acyclic (ppo ∪ com) := by
  apply union_acyclic_in_partial_order
  intro x y hunion
  cases hunion
  · case inl hppoxy => exact hppo x y hppoxy
  · case inr hcomxy => exact hcom x y hcomxy
