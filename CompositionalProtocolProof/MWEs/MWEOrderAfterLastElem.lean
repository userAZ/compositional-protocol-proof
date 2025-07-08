import Mathlib

lemma List.ordered_mem_impl_ordered_idx {α} [DecidableEq α] {l_head l_tail : List α} {n m : α}
  (l : List α) (hlist : l = l_head ++ l_tail)
  (hn_in_head : n ∈ l_head) (hm_in_tail : m ∈ l_tail) (hl_nodup : l.Nodup) : idxOf n l < idxOf m l  := by
  rw[hlist]
  rw[List.idxOf_append_of_mem]
  have hm_not_in_head : m ∉ l_head := by
    simp[List.Nodup] at hl_nodup
    intro hm_in_head
    rw[hlist] at hl_nodup
    have test := List.nodup_append.mp hl_nodup
    have test1 := test.right.right
    simp[List.Disjoint] at test1
    apply (test1 hm_in_head)
    exact hm_in_tail
  . rw[List.idxOf_append_of_notMem hm_not_in_head]
    have hidx_n_lt_length := List.idxOf_lt_length hn_in_head
    have hidx_n_lt_length_plus_idx_m := Nat.lt_add_left (idxOf m l_tail) hidx_n_lt_length
    rw[Nat.add_comm] at hidx_n_lt_length_plus_idx_m
    exact hidx_n_lt_length_plus_idx_m
  . exact hn_in_head



-- theorem List.idxOf_append_of_mem
--

example {l_head last} (l : List Nat) (hsorted : l.Sorted Nat.lt) (hlist : l = l_head ++ [last])
  (hl_nodup : l.Nodup) (n : Nat) (hn_in_l : n ∈ l) (hlast_lt_n : last < n)
  : False := by
  have hlast_in_l : last ∈ l := by simp [hlist]
  simp[List.Sorted] at hsorted
  -- simp[List.pairwise_iff Nat.lt l] at hsorted
  -- simp[List.pairwise_iff_forall_sublist] at hsorted
  simp[List.pairwise_iff_getElem] at hsorted

  have hspare_n_in_l := hn_in_l

  rw[hlist] at hn_in_l
  simp[List.mem_append] at hn_in_l
  have hn_ne_last : n ≠ last := by
    rw[Nat.ne_iff_lt_or_gt]
    simp[hlast_lt_n]
  have hn_in_head := Or.resolve_right hn_in_l hn_ne_last

  have hlast_in_tail : last ∈ [last] := by simp

  have hlast_in_l : last ∈ l := by simp[hlast_in_tail, hlist]
  have hlast_lt_len : List.idxOf last l < l.length := List.idxOf_lt_length_iff.mpr hlast_in_l

  have hn_lt_len : List.idxOf n l < l.length := List.idxOf_lt_length_iff.mpr hspare_n_in_l

  have hidx_n_lt_last : List.idxOf n l < List.idxOf last l :=
    List.ordered_mem_impl_ordered_idx l hlist hn_in_head hlast_in_tail hl_nodup

  have hn_lt_last := hsorted (List.idxOf n l) (List.idxOf last l) hn_lt_len hlast_lt_len hidx_n_lt_last
  simp[List.getElem_idxOf] at hn_lt_last
  absurd hlast_lt_n
  simp[Nat.le_iff_lt_or_eq, hn_lt_last]
