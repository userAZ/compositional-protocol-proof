import Mathlib

inductive Nat.OddEven (n : Nat) : Prop
| isOdd : n % 2 = 1 → Nat.OddEven n
| isEven : n % 2 = 0 → Nat.OddEven n

lemma Nat.is_odd_or_even (n : Nat) : Nat.OddEven n := by
  cases n
  case zero =>
    -- How do I choose a case of `Nat.OddEvent` such as `isEven`?
    sorry
  case succ n' =>
    sorry
