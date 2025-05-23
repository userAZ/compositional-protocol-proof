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
| p₁, p₂ => p₁.nat ≤ p₂.nat
  /- How to make Permissions accept the definition below for instDecidableLt? -/
  -- match p₁, p₂ with
  -- | none, none => false
  -- | some _, none => false
  -- | none, some _ => true
  -- | some rw₁, some rw₂ => rw₁ < rw₂

instance Permissions.instLE : (LE Permissions) := {le := Permissions.le}

instance Permissions.instDecidableLe (p₁ p₂ : Permissions) : (Decidable (p₁ ≤ p₂)) :=
  inferInstanceAs (Decidable (p₁.nat ≤ p₂.nat))

structure State where
  p : Permissions
  c : Coherent

def State.lt : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c ∧ (s₁.p ≠ s₂.p ∨ s₁.c ≠ s₁.c)

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
