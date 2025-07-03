import Mathlib

-- structure NatBool where
--   n : Nat
--   b : Bool

-- def NatBool.true (n : NatBool) : Prop := n.b
-- def List.allTrue (l : List NatBool) := ∀ n ∈ l, n.true

def List.leM (l : List Nat) (m : Nat) := ∀ n ∈ l, n < m

def List.upToN (l : List Nat) (hle_m : l.leM m) (n' : Nat) :=
  ∀ n ∈ (l.take ((l.idxOf n'))), n ≤ m

example (l : List Nat) (m : Nat) (hle_m : l.leM m) (hl_sorted : l.Sorted Nat.le) : sorry := by
  induction h_list : l with
  | nil =>
    sorry
  | cons h tail ih =>
    /- Here, I know from `h_list` that `h` and `tail` are in list `l`, but the induction hypothesis `ih` is unusable.
    `l = tail` is not a workable form. -/
    sorry
