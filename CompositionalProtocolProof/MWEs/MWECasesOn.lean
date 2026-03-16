-- import Mathlib

structure AType where
  n : Nat
  b : Bool

def AType.Big : AType → Prop
| a => a.n > 10 ∧ a.b
def AType.NotBig : AType → Prop
| a => a.n < 10 ∧ a.b

structure AType.NotTen (a : AType) : Prop where
  big : a.Big
  notBig : a.NotBig

def SpecificType : Type := {a : AType // a.NotTen}

-- Error: unsupported `AType.NotTen.casesOn` application during code generation
def SpecificType.toNat : SpecificType → Nat
| ⟨⟨n, true⟩,{big,notBig}⟩ => n

-- Error: unsupported `AType.NotTen.casesOn` application during code generation
def SpecificType.fn (s : SpecificType) : Nat :=
  match s with
  | ⟨⟨11, true⟩,_⟩ => 11
  | ⟨⟨n, true⟩,_⟩ => n

example (s : SpecificType) : s.fn ≠ 10 := by
  match s with
  | ⟨⟨9,false⟩,{big, notBig}⟩ => sorry
  | ⟨⟨10,true⟩,{big, notBig}⟩ => sorry
