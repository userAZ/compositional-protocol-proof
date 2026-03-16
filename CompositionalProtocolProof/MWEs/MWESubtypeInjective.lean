import Mathlib

example

def SubTen : Type := {n : Nat // n < 10}

instance SubTen.instGetValInjective : Function.Injective (λ n : SubTen => n.val) := by
  simp[Function.Injective]
  intro n m hn_val_eq_m
  sorry
