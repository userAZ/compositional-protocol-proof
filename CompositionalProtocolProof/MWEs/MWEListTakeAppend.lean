import Mathlib

lemma List.take_idxOf_append_eq_list {α} [DecidableEq α] (n : α) (l : List α) (hnodup : (l ++ [n]).Nodup) : List.take (List.idxOf n (l ++ [n])) (l ++ [n]) = l := by
  have hn_not_in_l : n ∉ l := by
    simp[List.nodup_append] at hnodup
    exact hnodup.right
  simp[List.idxOf_append_of_notMem hn_not_in_l]
