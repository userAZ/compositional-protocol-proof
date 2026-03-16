import Mathlib
import Mathlib.Order.Defs.PartialOrder

example {n₁ n₂ : Nat} (hn₁_lt_n₂ : n₁ < n₂) (hn₂_lt_n₁ : n₂ < n₁) (hne : n₁ ≠ n₂) : False := by
  absurd hn₁_lt_n₂
  simp
  rw[Nat.le_iff_lt_or_eq]
  apply Or.intro_left
  exact hn₂_lt_n₁
  -- apply Nat.lt_of_le_of_ne (n:=n₁) (m:=n₂)
  simp[Nat.lt_of_le_of_ne, hne]
  aesop <Nat.lt_of_le_of_ne>
/-
  induction n₁ with
  | zero =>
    induction n₂ with
    | zero => cases hn₁_lt_n₂
    | succ n₂' ih => cases hn₂_lt_n₁
  | succ n₁' ih₁ =>
    induction n₂ with
    | zero => cases hn₁_lt_n₂
    | succ n₂' ih₂ =>
      simp_all only [imp_false, not_lt, add_lt_add_iff_right, forall_const, isEmpty_Prop, not_le, IsEmpty.forall_iff]
      decide
      sorry
-/
