import Mathlib

structure Nat.NotTen (n : Nat) : Prop where
  greater : n > 10
  less : n < 10

def SpecificType : Type := {n : Nat // n.NotTen}

def SpecificType.toNat : SpecificType → Nat
| ⟨⟨n, false⟩,_⟩ => n
| ⟨⟨n, true⟩,_⟩ => n

def SpecificType.fn (s : SpecificType) : Nat :=
  match s with
  | ⟨⟨11, true⟩,_⟩ => 11
  | ⟨⟨n, true⟩,_⟩ => n
