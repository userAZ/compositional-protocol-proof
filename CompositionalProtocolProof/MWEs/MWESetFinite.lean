import Mathlib
import Canonical

def Nat.greater (m : Nat) : Type := {n : Nat // n > m}

structure Nats where
  ns : Set Nat
  finite : Finite ns

-- Using a Subtype produces problems.
noncomputable def T (s : Nats) (m : Nat) : Finset (Nat.greater m) :=
  {x : Nat.greater m | x.val ∈ (Set.Finite.toFinset s.finite)} -- failed to synthesize Fintype m.greater

-- Works without Subtype
def S (s : Finset Nat) : Finset Nat := {x ∈ s | x > 10}

/-
lemma Subtype.equiv_fin_impl_equiv_fin' {α} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : {x | p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x | q x} ≃ Fin m) :=
by
  use Nat.card {x | q x}
  have p_finite : Finite {x | p x} := Finite.of_equiv _ f.symm
  have q_finite : Finite {x | q x} := Finite.Set.subset {x | p x} himpl
  rw [← Nat.card_eq_of_equiv_fin f]
  exact ⟨Nat.card_mono p_finite himpl, ⟨Finite.equivFin {x | q x}⟩⟩

lemma Subtype.equiv_fin_impl_equiv_fin' {α} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : {x // p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x // q x} ≃ Fin m) := by
  have h := Cardinal.mk_subtype_mono himpl
  use Nat.card {x // q x}
  have p_finite : Finite {x | p x} := Finite.of_equiv _ f.symm
  have q_finite : Finite {x | q x} := Finite.Set.subset {x | p x} himpl
  rw [← Nat.card_eq_of_equiv_fin f]
  exact ⟨Nat.card_mono p_finite himpl, ⟨Finite.equivFin {x | q x}⟩⟩
-/

lemma Subtype.equiv_fin_impl_equiv_fin'' {α : Type*} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : {x // p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x // q x} ≃ Fin m) :=
by
  have := Cardinal.mk_subtype_mono himpl
  rw [Cardinal.le_def] at this
  obtain ⟨map, map_inj⟩ := this
  have finite_p : Finite { x // p x } := Finite.of_equiv _ f.symm
  have finite_q : Finite { x // q x } := Finite.of_injective map map_inj
  rw [← Nat.card_eq_of_equiv_fin f]
  exact ⟨
    Nat.card {x // q x},
    Nat.card_le_card_of_injective map map_inj,
    ⟨Finite.equivFin {x // q x}⟩
  ⟩
-- -/
