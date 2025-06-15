import Mathlib

variable (n : Nat)

inductive FinNat
| fn : Fin n → FinNat
| none : FinNat

structure UseFinNat where
  haveFn : FinNat n -- Is there a way to say just use a specified `n`, so I don't need to provide an `n` each time?

-- Same as above, can I specify a specific `n`, and avoid having to pass an `n` each time?
def UseFinNatDef : FinNat n → FinNat n → FinNat n
| n₁, n₂ => sorry
