import Mathlib

inductive Example (ns : Set Nat)
| example1 (have_even : ∃ n ∈ ns, Even n) : Example ns
| example2 (have_odd  : ∃ n ∈ ns, Odd  n) : Example ns

def Example.isCase1 (ns : Set Nat) (ex : Example ns) : Prop :=
  match ex with
  -- Error: type mismatch, `example1 exist_n` has type Example ?m.472, but is expected to have type `Type : Type 1`
  | Example.example1 exist_even => True
  | Example.example2 exist_odd  => False

/-
def Nat.inNsEven (ns : Set Nat) : Prop := ∃ n ∈ ns, Even n
def Nat.inNsOdd  (ns : Set Nat) : Prop := ∃ n ∈ ns, Odd  n
-/

inductive ExampleV2 (n : Nat)
| example1 (ge_ten : n ≥ 10) : ExampleV2 n
| example2 (lt_ten : n < 10) : ExampleV2 n

def ExampleV2.isCase1 (ns : Set Nat) (ex : Example ns) : Prop :=
  match Example ns with
  -- Error: type mismatch, `example1 exist_n` has type Example ?m.472, but is expected to have type `Type : Type 1`
  | ExampleV2.example1 _ => True
  | ExampleV2.example2 _ => False
