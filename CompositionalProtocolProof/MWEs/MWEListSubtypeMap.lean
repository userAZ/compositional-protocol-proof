import Mathlib

lemma List.idxOf_subtype_eq_idxOf_subtype_val {β : Type} {p : β → Prop} [DecidableEq β] [DecidableEq {x : β // p x}]
  (l : List {x : β // p x}) (n : {x : β // p x}) : idxOf n l = idxOf n.val (l.map (·.val)) := by
  induction l with
  | nil => simp
  | cons head rest ih =>
    simp only [List.idxOf_cons]
    by_cases hhead_is_n : head == n
    . case pos =>
      have hval_eq : head.val = n.val := by
        simp at hhead_is_n
        simp[hhead_is_n]
      simp[hhead_is_n, hval_eq]
    . case neg =>
      have hval_neq : ¬ head.val == n.val := by
        simp at hhead_is_n
        simp[hhead_is_n,]
      simp only [map_cons, idxOf_cons, ]
      simp only [hval_neq, hhead_is_n, cond_false]
      simp only [ih]

def N : Type := {n : Nat // n < 10}
deriving DecidableEq

lemma List.test' (e : N) (l : List N) : idxOf e l = idxOf e.val (l.map (·.val)) := by
  have h := idxOf_subtype_eq_idxOf_subtype_val l e
  exact h

example (l : List N) (n : N) : List.idxOf n l = List.idxOf n.val (l.map (·.val)) := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp?
    simp?[List.idxOf_cons]
    by_cases h : head == n
    . case pos =>
      have hval_eq : head.val = n.val := by
        rw[← Subtype.eq_iff]
        simp[] at h
        simp[h]
      simp[h]
      simp[hval_eq]
    . case neg =>
      have hval_eq : ¬ head.val == n.val := by
        simp
        rw[← Subtype.eq_iff]
        simp[] at h
        simp[h]
      simp[h]
      simp[hval_eq]
      simp[ih]

def N.getVal (n : N) := n.val
def Nat.id (n : Nat) := n

lemma N.get_val : ∀ (x : Nat) (h : Nat.lt_ten x), N.getVal ⟨x, h⟩ = x.id := by
  intro x hx_lt_ten
  simp[getVal, Nat.id]

example (l : List N) (n : N) : List.idxOf n l = List.idxOf n.val (l.map (N.getVal)) := by
  by_cases hn_in_l : n ∈ l
  . case pos =>
    rw[List.map_subtype N.get_val]
  sorry
