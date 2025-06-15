import Mathlib

variable (n : Nat)

structure FinNat where
  fn : Fin n

structure UseFinNat where
  haveFn : FinNat n -- Is there a way to say just use a specified `n`, so I don't need to provide an `n` each time?

-- Same as above, can I specify a specific `n`, and avoid having to pass an `n` each time?
def UseUseFinNat : FinNat n → FinNat n → FinNat n
| n₁, n₂ => ⟨ n₁.fn + n₂.fn ⟩
