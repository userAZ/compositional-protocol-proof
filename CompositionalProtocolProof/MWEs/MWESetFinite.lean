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

lemma Subtype.equiv_fin_impl_equiv_fin' {α} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : {x // p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x // q x} ≃ Fin m) := by
    /- Reasoning: The number of elements satisfying p is finite.
    If q x → p x, then the restriction q is at least as strong as p, if not stronger.
    So there should be as many or fewer elements in subtype {x // q x}.
    But how to write this in lean? -/
    sorry
