import Mathlib

#eval List.idxOf 2 [1,2,3]
#eval List.indexesOf 2 [1,2,3]

lemma List.in_tail_not_head (e m head : Nat) (l_tail : List Nat)
  (hsorted : Sorted Nat.le (head :: l_tail))
  (he_in_l : e ∈ take (idxOf m (head :: l_tail)) (head :: l_tail))
  (he_is_head : ¬e = head)
  : e ∈ take (idxOf m l_tail) l_tail := by
  -- simp_all[]
  have h := List.mem_of_mem_take he_in_l
  have h1 := mem_cons.mp h
  have h2 := Or.resolve_left h1 he_is_head
  -- rw[mem_cons] at he_in_l
  -- apply List.mem_of_mem_take
  -- apply List.mem_take_iff_getElem.mpr
  rw[List.take_cons] at he_in_l
  rw[List.idxOf_cons] at he_in_l
  simp at he_in_l

  -- rw[beq_iff_eq (a:=head) (b:=m)] at he_in_l

  sorry

lemma List.mem_fn_list (l : List Nat) (hsorted : l.Sorted Nat.le) (m : Nat) :
  ∀ e ∈ (l.take ((l.idxOf m))), e ∈ l := by
  induction l with
  | nil =>
    simp
  | cons head l_tail ih =>
    simp[ih]
    intro e he_in_l
    by_cases he_is_head : e = head
    . case pos =>
      apply Or.intro_left
      exact he_is_head
    . case neg =>
      apply Or.intro_right
      apply ih
      . case h.hsorted =>
        apply hsorted.tail
      . case h.a =>
        have ihh := ih hsorted.tail
        have h := ihh
        /- With `he_is_head`, `e` isn't `head`,
        so we should be able to remove `head` from `he_in_l` -/
        sorry

def NatSubTen := {n : Nat // n < 10}

def List.getNats (l : List NatSubTen) : List Nat := l.map (·.val)

lemma List.getNats.lt_ten (l : List NatSubTen) :
  ∀ n ∈ l.getNats, n < 10 := by
  intro n hn_in_l
  simp[List.getNats] at hn_in_l

  obtain ⟨w, h⟩ := hn_in_l
  obtain ⟨left, right⟩ := h
  subst right
  exact w.prop
