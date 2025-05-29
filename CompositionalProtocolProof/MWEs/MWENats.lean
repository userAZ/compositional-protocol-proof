import Mathlib

namespace MWE

inductive Nats
| two : Nat → Nat → Nats
| one : Nat → Nats

abbrev SetNats := Set Nats

def Nats.getNats : Nats → Set Nat
| .two n₁ n₂ => {n₁, n₂}
| .one n => {n}

def SetNats.SetNat : SetNats → Set Nat
| sns => sns.image Nats.getNats
