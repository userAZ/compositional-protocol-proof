import Mathlib

namespace MWE

inductive Nats
| order : Nat → Nat → Nats
| one : Nat → Nats

abbrev SetNats := Set Nats

def Nats.before : Nats → Nat → Prop
| ns, n =>
  match ns with
  | order _ n₂ => n = n₂
  | one _ => false

/- How does one express this in lean? -/
def SetNats.before (x : SetNats) (n : Nat) : {y : SetNats // ∀ m ∈ y, m.before n ∧ m ∈ x} :=
⟨
  {nats ∈ x | nats.before n},
  by
    simp
    intro m m_in_x m_before_n
    apply And.intro
    case left => exact m_before_n
    case right => exact m_in_x
⟩
