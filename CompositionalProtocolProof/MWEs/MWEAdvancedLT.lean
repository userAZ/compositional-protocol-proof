import Mathlib

structure Ex where
  n : Nat
  b : Bool

def Ex.lt : Ex → Ex → Prop
-- | ex₁, ex₂ => ex₁.n ≤ ex₂.n ∧ ex₁.b ≤ ex₂.b ∧ ex₁ ≠ ex₂ --(ex₁.n ≠ ex₂.n ∨ ex₂.b ≠ ex₂.b)
| ex₁, ex₂ => (ex₁.n < ex₂.n ∨ ex₁.n = ex₂.n) ∧ (ex₁.b < ex₂.b ∨ ex₁.b = ex₂.b) ∧ ex₁ ≠ ex₂ --(ex₁.n ≠ ex₂.n ∨ ex₂.b ≠ ex₂.b)

instance Ex.instLT : (LT Ex) := {lt := Ex.lt}

-- instance Ex.instDecidableLt (ex₁ ex₂ : Ex) : (Decidable (ex₁ < ex₂)) :=
--   inferInstanceAs (Decidable (ex₁ < ex₂))

instance Ex.instDecidableLt (_ _ : Ex) : (DecidableLT Ex)
| ⟨n₁,true⟩, ⟨n₂,false⟩ => -- n₁ ≤ n₂ ∧ b₁ ≤ b₂ ∧ (n₁ ≠ n₂ ∨ b₁ ≠ b₂)
  isFalse <| by
  simp[LT.lt]
  simp[Ex.lt] -- Lean complains about too many recusions if merging simp[LT.lt, Ex.lt]
| ⟨n₁, false⟩, ⟨n₂, false⟩ | ⟨n₁,true⟩, ⟨n₂,true⟩ =>
  if h : n₁ < n₂ then isTrue <| by
    simp[LT.lt]
    simp[Ex.lt]
    apply And.intro
    case left =>
      simp[h] -- Q: How to make this work with Ex.lt with ex₁.n ≤ ex₂.n, instead of ex₁.n < ex₂.n ∨ ex₁.n = ex₁.n?
    case right =>
      intro h₁
      -- contradiction
      aesop -- Q: How to do this without aesop?
  else if n₁ = n₂ then isFalse <| by
    simp[LT.lt]
    simp[Ex.lt]
    intro h₁
    cases h₁
    case inl h₂ =>
      contradiction
    case inr h₂ =>
      apply h₂
  else isFalse <| by
    simp[LT.lt]
    simp[Ex.lt]
    intro h₁
    cases h₁
    case inl h₂ =>
      contradiction
    case inr h₂ =>
      apply h₂
| ⟨n₁,false⟩, ⟨n₂,true⟩ =>
  if h : n₁ < n₂ then isTrue <| by
    simp[LT.lt]
    simp[Ex.lt]
    apply Or.inl
    apply h
  else if h₁ : n₁ = n₂ then isTrue <| by
    simp[LT.lt]
    simp[Ex.lt]
    aesop
  else isFalse <| by
    simp[LT.lt]
    simp[Ex.lt]
    simp[h,h₁]
    aesop
