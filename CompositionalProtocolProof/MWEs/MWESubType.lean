import Mathlib

abbrev SmallNat := {n : Nat // n < 5}

def test : SmallNat → String
| sn =>
  if h : sn.val < 5 then
    ""
  else
    let t := sn.prop
    by
    contradiction

abbrev SmallSet : Set Nat := {0} --{0, 1, 2}

abbrev SpecNat := {n : Nat // n ∈ SmallSet}

def test0 : SpecNat → String
| sn =>
  if h : sn.val = 0 then
    ""
  else
    by
    let t := sn.prop
    unfold SpecNat at sn
    unfold SmallSet at sn
    contradiction
