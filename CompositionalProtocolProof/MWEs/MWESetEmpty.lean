import Mathlib

abbrev SetNat := Set Nat

def Set.isSingleton {α : Type} (s : Set α) : Prop := ∃ e, s = {e}

def empty_or_singleton (sn : SetNat) : Prop := sn = ∅ ∨ sn.isSingleton

/- Either return none or the single element from a set -/
open scoped Classical in
noncomputable def GetNat (sn : SetNat) (h_e_or_s : empty_or_singleton sn) : Option Nat :=
  by classical exact
  if h : sn = ∅ then -- How do I state this case without a `failed to synthesize` message?
    none
  else
    -- Here, I want to use h_e_or_s to get the unique nat out of sn. How do I do this?
    (h_e_or_s.resolve_left h).choose
