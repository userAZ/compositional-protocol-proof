import Mathlib

def Nat.greater (n₁ n₂ : Nat) : Prop := n₁ + 1 = n₂

structure Set.hasBiggerNat : Prop where
  biggerNat : ∀ s : Set Nat, ∀ n ∈ s, ∃ n_succ ∈ s, n.greater n_succ

example (s : Set Nat) (n : Nat) (hn_in_s : n ∈ s) (hbigger : Set.hasBiggerNat) : ∃ n_bigger ∈ s, n_bigger > n := by
  apply Exists.intro
  apply And.intro
  case w =>
    have hexists_n_succ := hbigger.biggerNat s n hn_in_s
    have n_succ := hexists_n_succ.choose
    exact n_succ
  case h.left =>
    simp
    have hexists_n_succ := hbigger.biggerNat s n hn_in_s
    have hsucc_in_s := hexists_n_succ.choose_spec.left
    apply hsucc_in_s
  case h.right =>
    simp
    have hexists_n_succ := hbigger.biggerNat s n hn_in_s
    have hn_greater_succ := hexists_n_succ.choose_spec.right
    simp
    unfold Nat.greater at hn_greater_succ
    rw[← hn_greater_succ]
    simp
