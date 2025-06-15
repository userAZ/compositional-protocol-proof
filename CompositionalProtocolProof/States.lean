import CompositionalProtocolProof.Common
import Mathlib.Order.Category.PartOrd
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Basic

/--
ReadWritePermissions.
State with access permissions may have either write and read permissions, or only read permissions.
-/
inductive ReadWritePermissions
| wr : ReadWritePermissions -- Both Write and Read permissions
| r : ReadWritePermissions -- Read permissions
deriving DecidableEq

abbrev ReadWritePermissions.lt : ReadWritePermissions → ReadWritePermissions → Prop
| rw₁, rw₂ => rw₁ = .r ∧ rw₂ = .wr

instance ReadWritePermissions.instLT : (LT ReadWritePermissions) := {lt := ReadWritePermissions.lt}

instance ReadWritePermissions.instDecidableLtRel : DecidableRel ReadWritePermissions.lt := inferInstance

instance ReadWritePermissions.instDecidableLt : DecidableLT ReadWritePermissions := ReadWritePermissions.instDecidableLtRel

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

abbrev Permissions.lt : Permissions → Permissions → Prop
| p₁, p₂ => p₁ < p₂

instance Permissions.instLT : (LT Permissions) := {lt := Permissions.lt}

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

/- -- Sanity check.
def p1 : Permissions := some .r
def p2 : Permissions := some .wr
#eval p1 < p2
-/

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
deriving DecidableEq

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

def State.le : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c

instance State.instLE : (LE State) := {le := State.le}

instance State.instDecidableLe (s₁ s₂ : State) : Decidable (s₁ ≤ s₂) := by
  dsimp [· ≤ ·]
  unfold State.le
  simp
  infer_instance

abbrev State? := Option State

instance State?.instDecidableLt (s₁? s₂? : State?) : Decidable (s₁? < s₂?) := by
  dsimp [· < ·]
  unfold Option.lt
  match s₁?, s₂? with
  | none, none =>
    infer_instance
  | some s₁, none =>
    infer_instance
  | none, some s₂ =>
    infer_instance
  | some s₁, some s₂ =>
    apply State.instDecidableLt

instance State?.instDecidableLe (s₁? s₂? : State?) : Decidable (s₁? ≤ s₂?) := by
  dsimp [· ≤ ·]
  unfold Option.le
  match s₁?, s₂? with
  | none, none =>
    infer_instance
  | some _, none =>
    infer_instance
  | none, some _ =>
    infer_instance
  | some s₁, some s₂ =>
    apply State.instDecidableLe

inductive ProtocolInstance
| global : ProtocolInstance
| cluster1 : ProtocolInstance
| cluster2 : ProtocolInstance
deriving DecidableEq

variable (n : Nat)

inductive ProtocolCacheInstance'
| globalP : Fin n → ProtocolCacheInstance'
| cluster1 : Fin n → ProtocolCacheInstance'
| cluster2 : Fin n → ProtocolCacheInstance'
deriving DecidableEq

-- this will capture whatever in the context is called `n`
set_option quotPrecheck false in
notation "ProtocolCacheInstance" => ProtocolCacheInstance' n

inductive CacheId'
| proxy : ProtocolInstance → CacheId'
| cache : ProtocolCacheInstance → CacheId'
deriving DecidableEq

set_option quotPrecheck false in
notation "CacheId" => CacheId' n

abbrev Owner' := CacheId
abbrev Sharers' := Finset CacheId

set_option quotPrecheck false in
notation "Owner" => Owner' n

set_option quotPrecheck false in
notation "Sharers" => Sharers' n

inductive DirectoryState'
| SW : StateSW → Owner → DirectoryState'
| MR : StateMR → Sharers → DirectoryState'
| Vd : StateVd → DirectoryState'
| Vc : StateVc → DirectoryState'
| I  : StateI  → DirectoryState'
deriving DecidableEq, BEq

set_option quotPrecheck false in
notation "DirectoryState" => DirectoryState' n

def DirectoryState.CurrentSharers : DirectoryState → Sharers
| ds => match ds with
  | .SW _ owner   => {owner}
  | .MR _ sharers => sharers
  | .Vd _ => {}
  | .Vc _ => {}
  | .I  _ => {}

/-
abbrev SW : State := ⟨some .wr, true⟩
abbrev MR : State := ⟨some .r , true⟩
abbrev Vd : State := ⟨some .wr, false⟩
abbrev Vc : State := ⟨some .r , false⟩
abbrev I  : State := ⟨none    , false⟩
-/
def DirectoryState.toState : DirectoryState → State
| ds => match ds with
  | .SW _ _ => ⟨some .wr, true⟩ -- SW state
  | .MR _ _ => ⟨some .r , true⟩ -- MR state
  | .Vd _ => ⟨some .wr, false⟩  -- Vd state
  | .Vc _ => ⟨some .r, false⟩   -- Vc State
  | .I  _ => ⟨none, false⟩      -- I State

/-- State of an address entry at a structure. -/
structure EntryState where
  cache : State
  directory : DirectoryState

def System.Cache' := CacheId → State
def System.Directory' := ProtocolInstance → DirectoryState

set_option quotPrecheck false in
notation "System.Cache" => System.Cache' n

set_option quotPrecheck false in
notation "System.Directory" => System.Directory' n

/- Initial System State -/
structure InitialSystemState where
  caches : Finset (CacheId)
  cacheStates : System.Cache
  directories : ProtocolInstance
  directoryStates : System.Directory
