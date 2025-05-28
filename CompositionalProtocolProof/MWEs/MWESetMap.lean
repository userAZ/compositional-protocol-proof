import Mathlib

namespace MWE

abbrev Nat.toString : Nat → String
| n => s!"{n}"

/- Map from Nats to Strings -/
abbrev NatsToStringsList : List Nat → List String
| ns => ns.map Nat.toString

/- How do we map from Nat to String Sets -/
abbrev NatsToStrings : Set Nat → Set String
| ns => ns.image Nat.toString

def states := [0, 1]

theorem statesNoDups : List.Nodup states := by
  unfold List.Nodup
  simp
  unfold states
  simp

abbrev AllowableStates := Multiset Nat
def t : AllowableStates := states
abbrev States : Finset Nat := ⟨t, by
  unfold Multiset.Nodup
  unfold Quot.liftOn
  unfold List.Nodup
  simp
  unfold t
  unfold states
  simp
  ⟩

#check States
#eval States

theorem test : 1 ∈ States := by
  simp
  unfold t
  unfold states
  simp

def s1 : Set Nat := {0,1}
def s2 : Set Nat := {0}
#check {0,1} \ {1}
