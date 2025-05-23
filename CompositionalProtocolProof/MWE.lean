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

set_option diagnostics true

instance Example.instDecidableLt (ex₁ ex₂ : Example) : (Decidable (ex₁ < ex₂)) :=
  inferInstanceAs (Decidable (ex₁.nat < ex₂.nat))

-- #check Example.ex1 < Example.ex2
-- #eval  Example.ex1 < Example.ex2
-- #eval  Example.ex1 = Example.ex2

------------------------------------------------------------------

structure Ex where
  n : Nat
  b : Bool

def Ex.lt : Ex → Ex → Prop
| ex₁, ex₂ => ex₁.n ≤ ex₂.n ∧ ex₁.b ≤ ex₂.b ∧ (ex₁.n ≠ ex₂.n ∨ ex₂.b ≠ ex₂.b)

instance Ex.instLT : (LT Ex) := {lt := Ex.lt}

-- instance Ex.instDecidableLt (ex₁ ex₂ : Ex) : (Decidable (ex₁ < ex₂)) :=
--   inferInstanceAs (Decidable (ex₁ < ex₂))

instance Ex.instDecidableLt (ex₁ ex₂ : Ex) : (DecidableLT Ex)
-- | ⟨n₁,b₁⟩, ⟨n₂,b₂⟩ => -- n₁ ≤ n₂ ∧ b₁ ≤ b₂ ∧ (n₁ ≠ n₂ ∨ b₁ ≠ b₂)
| ⟨n₁,true⟩, ⟨n₂,false⟩ => -- n₁ ≤ n₂ ∧ b₁ ≤ b₂ ∧ (n₁ ≠ n₂ ∨ b₁ ≠ b₂)
  isFalse <| by
