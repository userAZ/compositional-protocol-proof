import Mathlib

lemma List.take_mem_append_eq_take {α} [DecidableEq α] (n m : α) (l : List α) (hn_in_head : n ∈ l)
  : List.take (List.idxOf n l) l = List.take (List.idxOf n (l ++ [m])) (l ++ [m]) := by
  rw[List.idxOf_append_of_mem hn_in_head]
  rw[List.take_append_eq_append_take]
  have hidxn_lt_len : (List.idxOf n l) < l.length := List.idxOf_lt_length hn_in_head
  have hidxn_le_len := Nat.le_of_lt hidxn_lt_len
  have hidxn_sub_len_eq_zero := Nat.sub_eq_zero_iff_le.mpr hidxn_le_len
  rw[hidxn_sub_len_eq_zero]
  simp
