import CompositionalProtocolProof.Common

/--
ReadWritePermissions.
State with access permissions may have either write and read permissions, or only read permissions.
-/
inductive ReadWritePermissions
| wr : ReadWritePermissions -- Both Write and Read permissions
| r : ReadWritePermissions -- Read permissions

/--
Permissions.
A structure's state may have WR, R, or no permissions
-/
abbrev Permissions := Option ReadWritePermissions

structure State where
  p : Permissions
  c : Coherent

abbrev SW : State := ⟨some .wr, true⟩
abbrev MR : State := ⟨some .r , true⟩
abbrev Vd : State := ⟨some .wr, false⟩
abbrev Vc : State := ⟨some .r , false⟩
abbrev I  : State := ⟨none    , false⟩

abbrev ℕ := Nat

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
