import Mathlib

structure Nat.intermediate (n_intermediate n_predecessor n_successor : Nat) : Prop where
  predecessor : n_predecessor < n_intermediate
  successor : n_intermediate < n_successor

structure Nat.intermediateSatisfyingProp (n n_predecessor n_successor : Nat) (p : Nat → Prop) : Prop where
  intermediate : n.intermediate n_predecessor n_successor
  satisfyProp : p n

def Finset.noIntermediateSatisfyingProp (s : Finset Nat) (n_predecessor n_successor : Nat) (p : Nat → Prop) : Prop :=
  ∀ n ∈ s, ¬ n.intermediateSatisfyingProp n_predecessor n_successor p

structure Finset.immediateSuccessorSatisfyingProp' (s : Finset Nat) (n_predecessor n_successor : Nat) (p : Nat → Prop) where
  isSuccessor : n_predecessor < n_successor
  noIntermediate : s.noIntermediateSatisfyingProp n_predecessor n_successor p
  predInSet : n_predecessor ∈ s
  succInSet : n_successor ∈ s

structure Finset.immediateSuccessorSatisfyingProp (s : Finset Nat) (n_predecessor n_successor : Nat) (p : Nat → Prop) where
  immediateSuccessor : s.immediateSuccessorSatisfyingProp' n_predecessor n_successor p
  satisfyProp : p n_successor

def Nat.isOdd (n : Nat) : Prop := n % 2 = 1

lemma Finset.immediate_successor_is_given_successor_satisfying_prop_or_predecessor_of_given_successor
  (s : Finset Nat) (n n_predecessor n_successor : Nat) (hsucc_odd : n_successor.isOdd)
  (hn_in_s : n ∈ s) (hpred_in_s : n_predecessor ∈ s) (hsucc_in_s : n_successor ∈ s)
  (hn_immediate : s.immediateSuccessorSatisfyingProp n_predecessor n Nat.isOdd)
  : n = n_successor ∨ n < n_successor := by
  by_cases hno_intermediate : ∀ n' ∈ s, n'.intermediate n_predecessor n_successor → ¬n'.isOdd
  . case pos => sorry
  . case neg => -- I'm specifically trying to prove the `neg` case, but need to prove termination.
    simp at hno_intermediate
    obtain ⟨x, hxs, hx_intermediate, hx_odd⟩ := hno_intermediate
    case intro.intro.intro =>
    have hshrinking : {m ∈ s | n_predecessor < m ∧ m < x} ⊂ {m ∈ s | n_predecessor < m ∧ m < n_successor} := by
      simp only [ssubset_iff,
        -- mem_filter, not_and, not_lt
        ]
      use x
      apply And.intro
      . case h.left => simp
      . case h.right =>
        apply Finset.insert_subset
        . case ha =>
          simp[hxs, hx_intermediate.predecessor, hx_intermediate.successor]
        . case hs =>
          simp[Finset.subset_iff]
          intro y hys hpred_lt_y hy_lt_x
          simp[hys, hpred_lt_y]
          calc y < x := hy_lt_x
            _ < n_successor := hx_intermediate.successor
    have hshrinking' := Finset.card_lt_card hshrinking
    have hn_is_x_or_n_lt_x : n = x ∨ n < x := by
      apply Finset.immediate_successor_is_given_successor_satisfying_prop_or_predecessor_of_given_successor
      . case hsucc_odd => exact hx_odd
      . case hn_in_s => exact hn_in_s
      . case hpred_in_s => exact hpred_in_s
      . case hsucc_in_s => exact hxs
      . case hn_immediate => exact hn_immediate

    apply Or.intro_right
    cases hn_is_x_or_n_lt_x
    . case inl hn_eq_x => simp[hn_eq_x, hx_intermediate.successor]
    . case inr hn_lt_x =>
      calc n < x := hn_lt_x
        x < n_successor := hx_intermediate.successor
-- The subset of Naturals in `s` we consider shrinks; We "drop" at least n_successor.
termination_by sizeOf ({m ∈ s | n_predecessor < m ∧ m < n_successor} : Finset Nat).card
