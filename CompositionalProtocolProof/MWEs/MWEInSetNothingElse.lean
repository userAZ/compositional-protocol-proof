import Mathlib

structure Set.ImmediatePredecessor (ns : Set Nat) (n m : Nat) where
  nInNs : n ∈ ns
  mInNs : m ∈ ns
  predecessor : n < m
  immediate : ∀ n' ∈ ns, ¬ (n < n' ∧ n' < m)

lemma Set.ImmediatePredecessor' (ns : Set Nat) (n m : Nat)
  : ns.ImmediatePredecessor n m = (Set.ImmediatePredecessor ns · m) n := by
  simp

example (ns : Set Nat) (n m : Nat) (hn_in_ns : n ∈ ns) (hm_in_ns : m ∈ ns)
  (hn_m_one : m = n + 1)
  : {n' ∈ ns | (ns.ImmediatePredecessor · m) n'} = {n} := by
  have hn_sat_p : (ns.ImmediatePredecessor · m) n := by
    simp
    constructor
    . case nInNs => exact hn_in_ns
    . case mInNs => exact hm_in_ns
    . case predecessor => simp[hn_m_one]
    . case immediate =>
      intro n' hn'_in_nes hn'_btn_n_m
      obtain ⟨hn_lt_n', hn'_lt_m⟩ := hn'_btn_n_m
      absurd hn'_lt_m
      simp[hn_m_one]
      rw [Nat.add_comm]
      rw[Nat.one_add_le_iff]
      exact hn_lt_n'

  apply Set.ext
  intro x
  apply Iff.intro
  . case h.mp =>
    intro hx_in_imm_preds
    simp at hx_in_imm_preds
    obtain ⟨hx_in_ns, h_x_imm_pred_m⟩ := hx_in_imm_preds
    simp at hn_sat_p
    have hx_eq_n : x = n := by
      have hn_imm := hn_sat_p.immediate
      have hx_imm := h_x_imm_pred_m.immediate
      have hx_not_between := hn_imm x hx_in_ns
      by_contra hx_ne_n
      apply hx_not_between
      apply And.intro
      . case left =>
        by_contra hn_ge_x
        simp at hn_ge_x
        rw[Nat.le_iff_lt_or_eq] at hn_ge_x
        simp[hx_ne_n] at hn_ge_x
        have hn_not_between := h_x_imm_pred_m.immediate n hn_in_ns
        apply hn_not_between
        apply And.intro
        . case left => exact hn_ge_x
        . case right => exact hn_sat_p.predecessor
      . case right => exact h_x_imm_pred_m.predecessor
    exact hx_eq_n
  . case h.mpr =>
    intro hx_in_n
    simp only [Set.mem_setOf_eq]
    apply And.intro
    all_goals simp at hx_in_n
    . case left =>
      simp[hx_in_n]
      exact hn_in_ns
    . case right =>
      simp[hx_in_n, hn_sat_p]

example (ns : Set Nat) (n m : Nat) (hn_in_ns : n ∈ ns) (hm_in_ns : m ∈ ns)
  (hn_m_one : m = n + 1)
  (hns : {n ∈ ns | n < 6}) : ns.ImmediatePredecessor n m := by
  constructor
  . case nInNs => exact hn_in_ns
  . case mInNs => exact hm_in_ns
  . case predecessor => simp[hn_m_one]
  . case immediate =>
    intro n' hn'_in_ns
    intro hn'_btn_n_m
    -- simp only[not_and_or]
    sorry
