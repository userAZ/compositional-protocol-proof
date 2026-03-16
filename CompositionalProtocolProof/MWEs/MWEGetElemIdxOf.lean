import Mathlib

structure NewNat where
  n : Nat
deriving BEq, DecidableEq

example (l : List Nat) (n : Nat) (hn_in_l : List.idxOf n l < l.length) (hget : l[List.idxOf n l] = n) : sorry := by
  rw[List.getElem_idxOf hn_in_l] at hget
  sorry

example (l : List NewNat) (n : NewNat) (hn_in_l : List.idxOf n l < l.length) (hget : l[List.idxOf n l] = n) : sorry := by
  rw[List.getElem_idxOf hn_in_l] at hget -- Error: rw can't find instance of getElem_indxOf
  sorry

example (l : List NewNat) (n : NewNat) (hn_in_l : List.idxOf n l < l.length) (hget : l[List.idxOf n l] = n) : sorry := by
  rw[List.getElem_idxOf (a:=n) (l:=l) hn_in_l] at hget -- Error: Mismatch, uses `instBEqNewNat`, but expects `instBEqOfDecidableEq`
  sorry
