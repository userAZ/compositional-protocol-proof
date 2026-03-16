import Mathlib

def List.isOrdered {α} (l : List α) (r : α → α → Prop) : Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

instance : DecidableRel Nat.le := by
  simp [DecidableRel]; intro n m; infer_instance

instance : IsTotal Nat Nat.le := by
  constructor; intro n m; simp
  exact Nat.le_or_le n m

instance : IsTrans Nat Nat.le := by
  constructor; intro a b c; simp
  exact Nat.le_trans

lemma Nat.idx_lt_iff_r_elem (l : List Nat) : let sorted_list := (l.insertionSort Nat.le); sorted_list.isOrdered Nat.le := by
  intro l_sorted
  simp [List.isOrdered]
  intro i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    apply List.Sorted.rel_get_of_le
    . case h =>
      subst l_sorted
      exact l.sorted_insertionSort Nat.le
    . case hab =>
      simp
      apply Fin.le_of_lt
      simp[hi_lt_j]
  . case mpr =>
    intro hordered_get
    by_contra hneg_i_lt_j
    simp at hneg_i_lt_j
    have hgetj_le_geti := List.Sorted.rel_get_of_le (l.sorted_insertionSort Nat.le) hneg_i_lt_j
    subst l_sorted
    simp at hgetj_le_geti
    absurd hordered_get
    simp
    have hj_lt_i_or_j_eq_i := Nat.lt_or_eq_of_le hgetj_le_geti
    cases hj_lt_i_or_j_eq_i
    . case inl hj_lt_i => exact hj_lt_i
    . case inr hj_eq_i =>
      absurd hj_eq_i
      sorry
