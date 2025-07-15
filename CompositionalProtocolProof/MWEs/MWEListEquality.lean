import Mathlib

def List.upTo (l : List Nat) (n : Nat) : List Nat := take (idxOf n l) l

structure List.immediatePredecessor (l : List Nat) (n m : Nat) : Prop where
  nInL : n ∈ l
  mInL : m ∈ l
  predecessor : n < m
  noIntermediate : ∀ p ∈ l, ¬ (n < p ∧ p < m)

lemma List.idxOf_n_one_lt_idxOf_m_impl_intermediate (l : List Nat) (n m : Nat) (hsorted : l.Sorted Nat.lt) (hnodup : l.Nodup)
  (hn_imm_pred_m : l.immediatePredecessor n m) (hidxn_one_lt_idxm : idxOf n l + 1 < idxOf m l)
  : ∃ p ∈ l, n < p ∧ p < m := by
  have hn_lt_len : idxOf n l < l.length := List.idxOf_lt_length hn_imm_pred_m.nInL
  have hm_lt_len : idxOf m l < l.length := List.idxOf_lt_length hn_imm_pred_m.mInL
  by_contra hinter
  simp at hinter
  have helem : ∃ e ∈ l, (idxOf e l = idxOf n l + 1) := by
    by_contra hexists_elem
    simp at hexists_elem
    let helem := l[idxOf n l + 1]
    have helem_in_l : helem ∈ l := by simp[helem]
    have helem_not_idxn_one := hexists_elem helem helem_in_l
    simp[helem,] at helem_not_idxn_one
    rw[List.idxOf_getElem] at helem_not_idxn_one
    apply helem_not_idxn_one
    rfl
    . case H => exact hnodup
  have hidxn_lt_idxelem : idxOf n l < idxOf helem.choose l := by
    simp[helem.choose_spec]
  have hidxelem_lt_idxm : idxOf helem.choose l < idxOf m l := by
    simp[helem.choose_spec, hidxn_one_lt_idxm]
  have hn_lt_elem : n < helem.choose := by
    simp[List.Sorted] at hsorted
    simp[List.pairwise_iff_getElem] at hsorted
    have helem_lt_len : idxOf helem.choose l < l.length := List.idxOf_lt_length helem.choose_spec.left
    have horder := hsorted (idxOf n l) (idxOf helem.choose l) hn_lt_len helem_lt_len hidxn_lt_idxelem
    simp[List.idxOf_getElem,] at horder
    exact horder
  have helem_lt_m : helem.choose < m := by
    simp[List.Sorted] at hsorted
    simp[List.pairwise_iff_getElem] at hsorted
    have helem_lt_len : idxOf helem.choose l < l.length := List.idxOf_lt_length helem.choose_spec.left
    have horder := hsorted (idxOf helem.choose l) (idxOf m l) helem_lt_len hm_lt_len hidxelem_lt_idxm
    simp[List.idxOf_getElem,] at horder
    exact horder
  have hcontra := hinter helem.choose helem.choose_spec.left hn_lt_elem
  absurd hcontra
  simp[helem_lt_m]


lemma List.contradiction_of_idxOf_imm_pred_eq_idxOf (l : List Nat) (n m : Nat)
  (hn_imm_pred_m : l.immediatePredecessor n m) (hm_eq_n : idxOf m l = idxOf n l) : False := by
  have hn_lt_len : idxOf n l < l.length := List.idxOf_lt_length hn_imm_pred_m.nInL
  have hm_lt_len : idxOf m l < l.length := List.idxOf_lt_length hn_imm_pred_m.mInL
  have hgetelem_eq : l[idxOf m l] = l[idxOf n l] := by simp[hm_eq_n]
  have heq : m = n := by
    simp[List.idxOf_getElem] at hgetelem_eq ; exact hgetelem_eq
  absurd heq
  simp[Nat.eq_iff_le_and_ge, hn_imm_pred_m.predecessor]

lemma List.idxOf_imm_pred_immediatePredecessor_one_eq_idxOf (l : List Nat) (n m : Nat) (hsorted : l.Sorted Nat.lt) (hnodup : l.Nodup)
  (hn_imm_pred_m : l.immediatePredecessor n m) : idxOf m l = idxOf n l + 1 := by
  simp[List.Sorted] at hsorted
  have hn_lt_len : idxOf n l < l.length := List.idxOf_lt_length hn_imm_pred_m.nInL
  have hm_lt_len : idxOf m l < l.length := List.idxOf_lt_length hn_imm_pred_m.mInL

  have hidxn_lt_idxm : idxOf n l < idxOf m l := by
    by_contra hnot_n_lt_m
    simp[Nat.le_iff_lt_or_eq] at hnot_n_lt_m
    cases hnot_n_lt_m
    . case inl hm_lt_n =>
      simp[List.pairwise_iff_getElem] at hsorted
      have hm_lt_n := hsorted (idxOf m l) (idxOf n l) hm_lt_len hn_lt_len hm_lt_n
      simp[List.idxOf_getElem] at hm_lt_n
      absurd hm_lt_n
      simp[Nat.le_iff_lt_or_eq, Or.intro_left, hn_imm_pred_m.predecessor]
    . case inr hm_eq_n =>
      apply List.contradiction_of_idxOf_imm_pred_eq_idxOf
      . case hn_imm_pred_m => exact hn_imm_pred_m
      . case hm_eq_n => exact hm_eq_n

  by_contra hnot_imm_pred
  have hm_lt_n_or := Nat.ne_iff_lt_or_gt.mp hnot_imm_pred
  cases hm_lt_n_or
  . case inl hm_lt_n_one =>
    have h_m_le_n : idxOf m l ≤ idxOf n l := by
      rw[Nat.add_comm] at hm_lt_n_one
      simp[Nat.lt_one_add_iff] at hm_lt_n_one
      exact hm_lt_n_one
    have h_m_lt_n : idxOf m l < idxOf n l := by
      simp[Nat.le_iff_lt_or_eq] at h_m_le_n
      cases h_m_le_n
      . case inl hidxm_lt_idxn => exact hidxm_lt_idxn
      . case inr hidxm_eq_idxn =>
        exfalso
        apply List.contradiction_of_idxOf_imm_pred_eq_idxOf
        . case hn_imm_pred_m => exact hn_imm_pred_m
        . case hm_eq_n => exact hidxm_eq_idxn
    have hm_lt_n_getelem := List.pairwise_iff_getElem.mp hsorted (idxOf m l) (idxOf n l) hm_lt_len hn_lt_len h_m_lt_n
    simp[List.get_idxOf] at hm_lt_n_getelem
    absurd hm_lt_n_getelem
    simp[Nat.le_iff_lt_or_eq, hn_imm_pred_m.predecessor]
  . case inr hidxn_one_lt_idxm =>
    have hintermediate := List.idxOf_n_one_lt_idxOf_m_impl_intermediate l n m hsorted hnodup hn_imm_pred_m hidxn_one_lt_idxm
    absurd hintermediate
    simp
    intro x hx_in_l hn_lt_x
    have hnot_intermediate := hn_imm_pred_m.noIntermediate x hx_in_l
    simp [not_and] at hnot_intermediate
    apply hnot_intermediate
    exact hn_lt_x

lemma List.upTo_immediatePredecessor_eq (l : List Nat) (n m : Nat) (hsorted : l.Sorted Nat.lt) (hnodup : l.Nodup)
  (hn_imm_pred_m : l.immediatePredecessor n m) : l.upTo m = l.upTo n ++ [n] := by
  simp[upTo]

  apply Eq.symm
  have hidxm_eq_idxn_one : idxOf m l = idxOf n l + 1 := List.idxOf_imm_pred_immediatePredecessor_one_eq_idxOf l n m hsorted hnodup hn_imm_pred_m
  rw[hidxm_eq_idxn_one]
  have hn_lt_len : idxOf n l < l.length := List.idxOf_lt_length hn_imm_pred_m.nInL
  have hn : [l[idxOf n l]] = [n] := by simp[List.idxOf_getElem hnodup (idxOf n l) hn_lt_len]
  rw[← hn]

  apply List.take_append_getElem hn_lt_len
