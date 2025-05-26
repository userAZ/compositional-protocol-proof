import Mathlib

namespace MWE

structure Ex where
  n : Nat
  b : Bool
deriving DecidableEq

abbrev Ex.lt : Ex → Ex → Prop
| ex₁, ex₂ => (ex₁.n ≤ ex₂.n) ∧ (ex₁.b ≤ ex₂.b) ∧ ex₁ ≠ ex₂

instance Ex.instLT : (LT Ex) := {lt := Ex.lt}

instance Ex.instDecidableRel : DecidableRel Ex.lt := inferInstance

instance Ex.instDecidableLT : DecidableLT Ex := Ex.instDecidableRel
/-
instance Ex.instDecidableLt (_ _ : Ex) : (DecidableLT Ex)
| ⟨n₁,true⟩, ⟨n₂,false⟩ =>
  isFalse <| by
  simp[LT.lt]
  simp[Ex.lt] -- Lean complains about too many recusions if merged (simp[LT.lt, Ex.lt])
| ⟨n₁, false⟩, ⟨n₂, false⟩ | ⟨n₁,true⟩, ⟨n₂,true⟩ =>
  if h : n₁ < n₂ then isTrue <| by
    simp[LT.lt]
    simp[Ex.lt]
    apply And.intro
    case left =>
      simp[h] -- Q: How to make this work with Ex.lt with ex₁.n ≤ ex₂.n, instead of ex₁.n < ex₂.n ∨ ex₁.n = ex₁.n?
    case right =>
      intro h₁
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
-/

def t0 : Ex := ⟨0,false⟩
def t1 : Ex := ⟨0,true⟩
-- DecidableLT Ex doesn't work?
#eval t0 < t1
-- Need to use Decidable (ex₁ < ex₂) instead of DecidableLT Ex?
instance (ex₁ ex₂ : Ex) : (Decidable (ex₁ < ex₂)) :=
  inferInstanceAs (Decidable (ex₁ < ex₂)) -- failed to synthesize Decidable (ex₁ < ex₂)

-- instance Ex.instDecidableLt (ex₁ ex₂ : Ex) : (Decidable (ex₁ < ex₂)) :=
--   inferInstanceAs (Decidable (ex₁ < ex₂))

def Ex.le : Ex → Ex → Prop
| ex₁, ex₂ => ex₁.n ≤ ex₂.n ∧ ex₁.b ≤ ex₂.b

instance Ex.instLE : (LE Ex) := {le := Ex.le}

instance Ex.instDecidableLE (ex₁ ex₂ : Ex) : (Decidable (ex₁ ≤ ex₂)) :=
  inferInstanceAs (Decidable (ex₁ ≤ ex₂))
