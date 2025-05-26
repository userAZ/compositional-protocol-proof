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

/-
def ReadWritePermissions.nat (rw : ReadWritePermissions) : Nat :=
  match rw with
  | .wr => 1
  | .r => 0
-/

abbrev ReadWritePermissions.lt : ReadWritePermissions → ReadWritePermissions → Prop
| rw₁, rw₂ => rw₁ = .r ∧ rw₂ = .wr
-- | rw₁, rw₂ => rw₁.nat < rw₂.nat

instance ReadWritePermissions.instLT : (LT ReadWritePermissions) := {lt := ReadWritePermissions.lt}

instance ReadWritePermissions.instDecidableLtRel : DecidableRel ReadWritePermissions.lt := inferInstance

instance ReadWritePermissions.instDecidableLt : DecidableLT ReadWritePermissions := ReadWritePermissions.instDecidableLtRel

/-
#eval ReadWritePermissions.wr < ReadWritePermissions.r -- false
#eval ReadWritePermissions.r < ReadWritePermissions.wr -- true
#eval ReadWritePermissions.wr < ReadWritePermissions.wr -- false
#eval ReadWritePermissions.r < ReadWritePermissions.r -- false
-/

abbrev ReadWritePermissions.le : ReadWritePermissions → ReadWritePermissions → Prop
| rw₁, rw₂ => rw₁ < rw₂ ∨ rw₁ = rw₂

instance ReadWritePermissions.instLE : (LE ReadWritePermissions) := {le := ReadWritePermissions.le}

instance ReadWritePermissions.instDecidableLeRel : DecidableRel ReadWritePermissions.le := inferInstance

instance ReadWritePermissions.instDecidableLe : DecidableLE ReadWritePermissions := ReadWritePermissions.instDecidableLeRel

/--
Permissions.
A structure's state may have WR, R, or no permissions
-/
abbrev Permissions := Option ReadWritePermissions
-- deriving DecidableEq

def p1 : Permissions := some .r
def p2 : Permissions := some .wr
-- #check p1 < p2
-- #eval p1 = p2
-- #eval p1 < p2
/-
def Permissions.nat : Permissions → Nat
| none => 0
| some rw => rw.nat + 1
-/

abbrev Permissions.lt : Permissions → Permissions → Prop
-- | p₁, p₂ => p₁.nat < p₂.nat
| p₁, p₂ => --p₁.nat < p₂.nat
  p₁ < p₂
  -- match p₁, p₂ with
  -- | none, none => false
  -- | some _, none => false
  -- | none, some _ => true
  -- | some rw₁, some rw₂ => rw₁ < rw₂

instance Permissions.instLT : (LT Permissions) := {lt := Permissions.lt}

-- instance Permissions.instDecidableRel : DecidableRel Permissions.lt := inferInstance

instance Permissions.instDecidableLt (p₁ p₂ : Permissions) : Decidable (p₁ < p₂) := by
  dsimp [· < ·]
  unfold Permissions.lt
  dsimp [· < ·]
  unfold Option.lt
  unfold ReadWritePermissions.lt
  simp
  match p₁, p₂ with
  | none, none =>
    infer_instance
  | some rw₁, none =>
    infer_instance
  | none, some rw₂ =>
    infer_instance
  | some rw₁, some rw₂ =>
    infer_instance

-- #eval p1 < p2

abbrev Permissions.le : Permissions → Permissions → Prop
| p₁, p₂ => p₁ ≤ p₂

instance Permissions.instLE : (LE Permissions) := {le := Permissions.le}

instance Permissions.instDecidableLe (p₁ p₂ : Permissions) : Decidable (p₁ ≤ p₂)  := by
  dsimp [· ≤ ·]
  unfold Permissions.le
  dsimp [· ≤ ·]
  unfold Option.le
  unfold ReadWritePermissions.le
  simp
  match p₁, p₂ with
  | none, none =>
    infer_instance
  | some rw₁, none =>
    infer_instance
  | none, some rw₂ =>
    infer_instance
  | some rw₁, some rw₂ =>
    infer_instance

structure State where
  p : Permissions
  c : Coherent

abbrev SW : State := ⟨some .wr, true⟩
abbrev MR : State := ⟨some .r , true⟩
abbrev Vd : State := ⟨some .wr, false⟩
abbrev Vc : State := ⟨some .r , false⟩
abbrev I  : State := ⟨none    , false⟩

abbrev StateSW := {s : State // s = SW}
abbrev StateMR := {s : State // s = MR}
abbrev StateVd := {s : State // s = Vd}
abbrev StateVc := {s : State // s = Vc}
abbrev StateI  := {s : State // s = I}

abbrev State.lt : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c ∧ (s₁ ≠ s₂)

instance State.instLT : (LT State) := {lt := State.lt}

instance State.instDecidableLt (s₁ s₂ : State) : Decidable (s₁ < s₂) := by
  dsimp [· < ·]
  unfold State.lt
  dsimp
  match s₁, s₂ with
  | ⟨p₁, false⟩, ⟨p₂, true⟩ =>
    simp
    apply Permissions.instDecidableLe
  | ⟨p₁, false⟩, ⟨p₂, false⟩ | ⟨p₁, true⟩, ⟨p₂, true⟩ =>
    simp
    infer_instance
  | ⟨p₁, true⟩, ⟨p₂, false⟩ =>
    simp
    infer_instance

-- #eval I < Vc

-- instance (s₁ s₂ : State) : Decidable (s₁ < s₂) :=
--   inferInstanceAs (Decidable ((s₁.lt s₂) = true))

def State.le : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c

instance State.instLE : (LE State) := {le := State.le}


/- TODO: re-write instDecidableLe
instance State.instDecidableLe (_ _ : State) : (DecidableLE State)
| ⟨p₁, true⟩, ⟨p₂, false⟩ => isFalse <| by
  simp[LE.le]; simp[State.le]
| ⟨p₁, false⟩, ⟨p₂, false⟩ | ⟨p₁, true⟩, ⟨p₂, true⟩ |⟨p₁, false⟩, ⟨p₂, true⟩ =>
  if h₁ : p₁ < p₂ then isTrue <| by
    simp[LE.le]; simp[State.le]
    simp[LE.le]; simp[Permissions.le];
    apply Or.intro_left
    simp[LT.lt] at h₁; simp[Permissions.lt] at h₁
    exact h₁
  else if h₂ : p₁ = p₂ then isTrue <| by
    simp[LE.le]; simp[State.le]
    simp[LE.le]; simp[Permissions.le];
    apply Or.intro_right
    exact h₂
  else isFalse <| by
    simp[LE.le]; simp[State.le]
    simp[LE.le]; simp[Permissions.le];
    apply And.intro
    . simp[LT.lt] at h₁
      simp[Permissions.lt] at h₁
      exact h₁
    . exact h₂
-/

inductive CacheId
| proxy : ℕ → CacheId
| cache : ℕ → CacheId

abbrev Owner := CacheId
abbrev Sharers := List CacheId

inductive DirectoryState
| SW : StateSW → Owner → DirectoryState
| MR : StateMR → Sharers → DirectoryState
| Vd : StateVd → DirectoryState
| Vc : StateVc → DirectoryState
| I  : StateI  → DirectoryState
