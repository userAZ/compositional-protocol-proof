import Mathlib

def List.upTo (ns : List Nat) (n : Nat) : List Nat := take (idxOf n ns) ns

def Nat.op (n m : Nat) := n + m

def List.accumulate (ns : List Nat) (base : Nat) : Nat := match ns with
  | [] => base
  | n :: ns => ns.accumulate (n.op base)

example (l : List Nat) (hsorted : l.Sorted (Nat.le)) (n base : Nat)
  : (l.upTo n ++ [n]).accumulate base = n.op ( (l.upTo n).accumulate base ) := by
  unfold List.accumulate
  induction l generalizing base with
  | nil => simp[List.upTo, List.accumulate,]
  | cons head tail ih =>
    have ih_pre : List.Sorted Nat.le tail := by
      simp[List.sorted_cons] at hsorted
      exact hsorted.right
    have ih_post := ih ih_pre
    simp[List.upTo]
    simp[List.idxOf_cons]
    by_cases hhead : head == n
    . case pos =>
      simp[hhead]
      simp[List.accumulate]
    . case neg =>
      simp[hhead]
      unfold List.accumulate
      rw[← List.upTo.eq_def]
      apply ih_post
