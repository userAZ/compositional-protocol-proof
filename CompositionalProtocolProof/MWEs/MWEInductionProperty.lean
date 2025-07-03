import Mathlib

-- structure NatBool where
--   n : Nat
--   b : Bool

-- def NatBool.true (n : NatBool) : Prop := n.b
-- def List.allTrue (l : List NatBool) := ∀ n ∈ l, n.true

def List.leM (l : List Nat) (m : Nat) := ∀ n ∈ l, n < m

/- Can make the goal harder with this: ∧ (l.upToN n).all (· < n).
Would need to add this: (hle_m : l.leM m) to the premise on the left of the goal. -/

def List.upToN (l : List Nat) (n : Nat) :=
  l.take ((l.idxOf n))

example (l : List Nat) (n m : Nat) (hl_sorted : l.Sorted Nat.le) : (l.upToN n).Sorted Nat.le := by
  let up_to_n := l.upToN n
  induction l with
  | nil =>
    constructor
  | cons h tail ih =>
    /- Here, I know from `h_list` that `h` and `tail` are in list `l`, but the induction hypothesis `ih` is unusable.
    `l = tail` is not a workable form. -/
    sorry
