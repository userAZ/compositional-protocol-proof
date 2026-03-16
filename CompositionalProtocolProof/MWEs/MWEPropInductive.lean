import Mathlib

inductive Example (n : Nat) : Prop
| example1 (ge_ten : n ≥ 10) : Example n
| example2 (lt_ten : n < 10) : Example n

def Example.isCase1 (n : Nat) (ex : Example n) : Prop :=
  -- Error: recursor 'Example.casesOn' can only eliminate into Prop
  match ex with
  | Example.example1 _ => True
  | Example.example2 _ => False
