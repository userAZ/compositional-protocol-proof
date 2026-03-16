import Mathlib

structure NatBool where
  n : Nat
  b : Bool

def type := Finset NatBool

def ex0 : Finset NatBool := {⟨0,false⟩}

variable (n : Nat)

def ex2 : Array NatBool := Array.mk [⟨0,false⟩]
def ex3 : ex2.size = 1 := by simp [ex2]
def ex1 : Vector NatBool 1 := Vector.mk ex2 ex3

#check ex0[0]
