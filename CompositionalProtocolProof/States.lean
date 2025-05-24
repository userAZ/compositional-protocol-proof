import CompositionalProtocolProof.Common
import Mathlib.Order.Category.PartOrd

/--
ReadWritePermissions.
State with access permissions may have either write and read permissions, or only read permissions.
-/

inductive ReadWritePermissions
| wr : ReadWritePermissions -- Both Write and Read permissions
| r : ReadWritePermissions -- Read permissions
deriving DecidableEq

def ReadWritePermissions.nat (rw : ReadWritePermissions) : Nat :=
  match rw with
  | .wr => 1
  | .r => 0

def ReadWritePermissions.lt : ReadWritePermissions → ReadWritePermissions → Prop
-- | rw₁, rw₂ => rw₁ = .r ∧ rw₂ = .wr
| rw₁, rw₂ => rw₁.nat < rw₂.nat

instance ReadWritePermissions.instLT : (LT ReadWritePermissions) := {lt := ReadWritePermissions.lt}

instance ReadWritePermissions.instDecidableLt (rw₁ rw₂ : ReadWritePermissions) : (Decidable (rw₁ < rw₂)) :=
  inferInstanceAs (Decidable (rw₁.nat < rw₂.nat))

def ReadWritePermissions.le : ReadWritePermissions → ReadWritePermissions → Prop
| rw₁, rw₂ => rw₁ < rw₂ ∨ rw₁ = rw₂

instance ReadWritePermissions.instLE : (LE ReadWritePermissions) := {le := ReadWritePermissions.le}

instance ReadWritePermissions.instDecidableLe (rw₁ rw₂ : ReadWritePermissions) : (Decidable (rw₁ ≤ rw₂)) :=
  inferInstanceAs (Decidable (rw₁.nat < rw₂.nat ∨ rw₁ = rw₂))

/--
Permissions.
A structure's state may have WR, R, or no permissions
-/
def Permissions := Option ReadWritePermissions
deriving DecidableEq

def Permissions.nat : Permissions → Nat
| none => 0
| some rw => rw.nat + 1

def Permissions.lt : Permissions → Permissions → Prop
| p₁, p₂ => p₁.nat < p₂.nat
  /- How to make Permissions accept the definition below for instDecidableLt? -/
  -- match p₁, p₂ with
  -- | none, none => false
  -- | some _, none => false
  -- | none, some _ => true
  -- | some rw₁, some rw₂ => rw₁ < rw₂

instance Permissions.instLT : (LT Permissions) := {lt := Permissions.lt}

instance Permissions.instDecidableLt (p₁ p₂ : Permissions) : (Decidable (p₁ < p₂)) :=
  inferInstanceAs (Decidable (p₁.nat < p₂.nat))

def Permissions.le : Permissions → Permissions → Prop
| p₁, p₂ => p₁.nat < p₂.nat ∨ p₁ = p₂
  /- How to make Permissions accept the definition below for instDecidableLt? -/
  -- match p₁, p₂ with
  -- | none, none => false
  -- | some _, none => false
  -- | none, some _ => true
  -- | some rw₁, some rw₂ => rw₁ < rw₂

instance Permissions.instLE : (LE Permissions) := {le := Permissions.le}

instance Permissions.instDecidableLe (_ _ : Permissions) : (DecidableLE Permissions) --(Decidable (p₁ ≤ p₂)) :=
  -- inferInstanceAs (Decidable (p₁.nat < p₂.nat ∨ p₁ = p₂))
| none, none => isTrue <| by
  simp[LE.le]; simp[le]
| some rw, none => isFalse <| by
  simp[LE.le]; simp[le]; simp[Permissions.nat]
| none, some rw => isTrue <| by
  simp[LE.le]; simp[le]; simp[Permissions.nat]
| some rw₁, some rw₂ =>
  if h : rw₁ < rw₂ then isTrue <| by
    simp[LE.le]; simp[le]; simp[Permissions.nat]
    apply Or.intro_left
    simp[LT.lt] at h
    simp[ReadWritePermissions.lt] at h
    exact h
  else if h₁ : rw₁ = rw₂ then isTrue <| by
    simp[LE.le]; simp[le]; simp[Permissions.nat];
    apply Or.intro_right
    simp[h₁]
  else isFalse <| by
    simp[LE.le]; simp[le]; simp[Permissions.nat];
    -- simp[ReadWritePermissions.lt] at h
    -- simp[Nat.ge_of_not_lt] at h
    apply And.intro
    case left =>
      simp[LT.lt] at h; simp[ReadWritePermissions.lt] at h
      exact h
    case right =>
      intro rw₁_eq_rw₂
      apply h₁
      rw[Option.some_inj] at rw₁_eq_rw₂
      exact rw₁_eq_rw₂

structure State where
  p : Permissions
  c : Coherent

def State.lt : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c ∧ (s₁ ≠ s₂) --(s₁.p ≠ s₂.p ∨ s₁.c ≠ s₁.c)

instance State.instLT : (LT State) := {lt := State.lt}

theorem Permissions.p₁_lt_p₂_imp_p₁_ne_p₂ (p₁ p₂ : Permissions) : p₁ < p₂ → p₁ ≠ p₂ := by
  intro h
  cases p₁
  . cases p₂
    . simp[h]
      contradiction
    . simp
  case some rw₁ =>
    cases p₂
    . simp
    case some rw₂ =>
    . intro h₁
      rw[Option.some_inj] at h₁
      rw[h₁] at h
      simp[LT.lt] at h
      simp[Permissions.lt] at h

theorem Permissions.p₁_lt_p₂_imp_p₁_le_p₂_and_p₁_ne_p₂ (p₁ p₂ : Permissions) : p₁ < p₂ → p₁ ≤ p₂ ∧ p₁ ≠ p₂ := by
  simp[LE.le]; simp[Permissions.le]
  intro h
  apply And.intro
  . apply Or.intro_left
    exact h
  . apply Permissions.p₁_lt_p₂_imp_p₁_ne_p₂
    exact h

instance State.instDecidableLt (_ _ : State) : (DecidableLT State)
| ⟨p₁, true⟩, ⟨p₂, false⟩ => isFalse <| by
  simp[LT.lt]
  simp[State.lt]
| ⟨p₁, false⟩, ⟨p₂, false⟩ | ⟨p₁, true⟩, ⟨p₂, true⟩ =>
  if h₁ : p₁ < p₂ then isTrue <| by
    simp[LT.lt]; simp[State.lt]
    apply Permissions.p₁_lt_p₂_imp_p₁_le_p₂_and_p₁_ne_p₂
    exact h₁
  else if h₂ : p₁ = p₂ then isFalse <| by
    simp[LT.lt]; simp[State.lt];
    simp[h₂]
  else isFalse <| by
    simp[LT.lt]; simp[State.lt];
    intro h₃
    simp[h₂]
    cases h₃
    case inl h₄ =>
      simp[LT.lt] at h₁
      rw[Permissions.lt] at h₁
      apply h₁
      exact h₄
    case inr h₄ =>
      apply h₂
      exact h₄
| ⟨p₁, false⟩, ⟨p₂, true⟩ =>
  if h₁ : p₁ < p₂ then isTrue <| by
    simp[LT.lt]; simp[State.lt];
    simp[LE.le]; simp[Permissions.le];
    apply Or.intro_left
    simp[LT.lt] at h₁; simp[Permissions.lt] at h₁
    exact h₁
  else if h₂ : p₁ = p₂ then isTrue <| by
    simp[LT.lt]; simp[State.lt];
    simp[LE.le]; simp[Permissions.le]
    apply Or.intro_right
    exact h₂
  else isFalse <| by
    simp[LT.lt]; simp[State.lt];
    simp[LE.le]; simp[Permissions.le];
    apply And.intro
    . simp[LT.lt] at h₁
      simp[Permissions.lt] at h₁
      exact h₁
    . exact h₂

abbrev SW : State := ⟨some .wr, true⟩
abbrev MR : State := ⟨some .r , true⟩
abbrev Vd : State := ⟨some .wr, false⟩
abbrev Vc : State := ⟨some .r , false⟩
abbrev I  : State := ⟨none    , false⟩

inductive CacheId
| proxy : ℕ → CacheId
| cache : ℕ → CacheId

abbrev StateSW := {s : State // s = SW}
abbrev StateMR := {s : State // s = MR}
abbrev StateVd := {s : State // s = Vd}
abbrev StateVc := {s : State // s = Vc}
abbrev StateI  := {s : State // s = I}

abbrev Owner := CacheId
abbrev Sharers := List CacheId

inductive DirectoryState
| SW : StateSW → Owner → DirectoryState
| MR : StateMR → Sharers → DirectoryState
| Vd : StateVd → DirectoryState
| Vc : StateVc → DirectoryState
| I  : StateI  → DirectoryState
