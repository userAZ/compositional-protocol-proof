import Mathlib
-- import CompositionalProtocolProof.MWEs.MWEGetSubtypeProp

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

example (l : List Nat) (n : Nat) (hl_sorted : l.Sorted Nat.le) : (l.upToN n).Sorted Nat.le := by
  let up_to_n := l.upToN n
  have h_up_to_sorted : up_to_n.Sorted Nat.le := by
    subst up_to_n
    simp [List.upToN]
    sorry
  induction l with
  | nil =>
    simp[List.upToN]
    -- simp[List.idxOf_]
    -- sorry
  | cons h tail ih =>
    -- exact h_up_to_sorted

    simp[List.upToN, List.idxOf_cons,]
    by_cases h == n
    . case pos h_take_head =>
      simp[h_take_head]
    . case neg h_not_head =>
      simp only [h_not_head, cond_false]
      simp only [List.idxOf_]
      -- simp?[h_not_head]

    apply ih
    /- Here, I know from `h_list` that `h` and `tail` are in list `l`, but the induction hypothesis `ih` is unusable.
    `l = tail` is not a workable form. -/
    -- subst up_to_n
    -- exact h_up_to_sorted
    exact ih
    -- sorry

example (l : List Nat) (n m : Nat) (hle_m : l.leM m) : (l.upToN n).leM m := by
  let up_to_n := l.upToN n
  have hl_up_to_le_m : (l.upToN n).leM m := by
    -- simp[List.upToN, List.leM]
    sorry
  induction l with
  | nil => simp[List.upToN, List.leM]
  | cons h tail ih =>
    exact hl_up_to_le_m
    sorry

example (l : List Nat) (n m : Nat) (hl_sorted : l.Sorted Nat.le) :
  (l.upToN n).Sorted Nat.le := by
  let up_to_n := l.upToN n
  induction l.attach with
  | nil =>
    simp[List.upToN]
    simp[List.Sorted.]
    sorry

    -- simp [List.attach] at hl
    -- rw [hl]
    -- constructor
  | cons hd tail ih =>
    exact ih
    have ⟨hd,hd_in_l⟩ := hd
    have ⟨t,htail_in_l⟩ := tail
    /- Here, I know from `h_list` that `h` and `tail` are in list `l`, but the induction hypothesis `ih` is unusable.
    `l = tail` is not a workable form. -/
    sorry
