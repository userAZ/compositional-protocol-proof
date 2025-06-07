import Mathlib

abbrev SetNat := Set Nat

def empty_or_unique (sn : SetNat) := sn = ∅ ∨ sn.unique

def GetNat (sn : SetNat) (h_e_or_u : empty_or_unique sn) : Option Nat :=
  if sn = ∅ then
    none
  else
    -- Here, I want to use h_e_or_u to get the unique nat out of sn. How do I do this?
    sorry
