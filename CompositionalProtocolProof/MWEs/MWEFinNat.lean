import Mathlib

variable (n : Nat)

inductive FinNat'
| fn : Fin n → FinNat'
| none : FinNat'

set_option quotPrecheck false in
notation "FinNat" => FinNat' n

inductive NewFinNat'
| fnfn : FinNat → NewFinNat'

set_option quotPrecheck false in
notation "NewFinNat" => NewFinNat' n

-- Every type that uses FinNat needs a new notation added.
abbrev FinSetFN' := Finset NewFinNat -- lean accepts this
-- abbrev FinSetFN'' := Finset NewFinNat' -- lean requires a Nat
