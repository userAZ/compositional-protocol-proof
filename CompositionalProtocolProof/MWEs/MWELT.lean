import Mathlib

inductive Example
| ex1 : Example
| ex2 : Example
deriving DecidableEq

def Example.nat : Example → Nat
| e => match e with
  | .ex1 => 0
  | .ex2 => 1

def Example.lt : Example → Example → Prop
| ex₁, ex₂ => ex₁.nat < ex₂.nat

instance Example.instLT : (LT Example) := {lt := Example.lt}

instance Example.instDecidableLt (ex₁ ex₂ : Example) : (Decidable (ex₁ < ex₂)) :=
  inferInstanceAs (Decidable (ex₁.nat < ex₂.nat))

-- #check Example.ex1 < Example.ex2
-- #eval  Example.ex1 < Example.ex2
-- #eval  Example.ex1 = Example.ex2

------------------------------------------------------------------
