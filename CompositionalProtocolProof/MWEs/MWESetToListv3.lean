import Mathlib

/- List is sorted, and totally ordered. -/
def List.isOrdered {α} (l : List α) (r : α → α → Prop) : Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

instance : DecidableRel Nat.lt := by
  unfold Nat.lt
  simp[Nat.succ_eq_add_one, Nat.le_eq]
  infer_instance

lemma list_is_ordered (l : List Nat) :
  let l_sorted := l.insertionSort Nat.lt
  l_sorted.isOrdered Nat.lt := by
  intro l_sorted
  unfold List.isOrdered
  intro i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    /- What is the best way to handle `sorted_list` here? -/
    simp[l_sorted]
    simp[List.insertionSort]
    sorry
  . case mpr =>
    sorry
