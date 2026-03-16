import Mathlib


example (l : List Nat) : ∀ i j : Fin l.length, i ≤ j ↔ l[i] ≤ l[j] := by
  induction l using List.reverseRecOn with
  | nil => sorry
  | append_singleton l e ih => sorry
