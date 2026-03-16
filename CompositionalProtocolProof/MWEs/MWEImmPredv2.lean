import Mathlib

structure FinNats where
  ns : Set Nat
  finite : Finite ns
  ordered : ∀ n₁ ∈ ns, ∀ n₂ ∈ ns, n₁ < n₂ ∨ n₂ < n₁

structure Nat.orderedBetween (n_between n₁ n₂ : Nat) where
  pred : n₁ < n_between
  succ : n_between < n₂

noncomputable def FinNats.toFinset (fn : FinNats) : Finset Nat := Set.Finite.toFinset fn.finite
noncomputable def FinNats.toList (fn : FinNats) : List Nat := fn.toFinset.toList

def FinNats.noIntermediatePredecessor (fn : FinNats) (n₁ n₂ : Nat) : Prop :=
  ∀ n ∈ fn.ns, ¬ n.orderedBetween n₁ n₂

def FinNats.listNoIntermediatePredecessor (fn : FinNats) (n₁ n₂ : Nat) : Prop :=
  let l := fn.toList
  (l.idxOf n₁) + 1 = l.idxOf n₂

def FinNats.immediatePredecessor (fn : FinNats) (n₁ n₂ : Nat) : Prop :=
  fn.noIntermediatePredecessor n₁ n₂ ∨ fn.listNoIntermediatePredecessor n₁ n₂

lemma sorted_immediate_predecessor_in_list
  (fn : FinNats) (l : List Nat)
  (hl_of_fin_nats : l = fn.toList) (hl_sorted : l.Sorted Nat.lt) (hl_nempty : ¬ l.isEmpty)
  (n : Nat) (hl_up_to_n_nempty : l.take (l.idxOf n) ≠ [])
  : fn.noIntermediatePredecessor ((l.take (l.idxOf n)).getLast hl_up_to_n_nempty) n := by

  sorry
