import CompositionalProtocolProof.Common
import Mathlib.Order.Category.PartOrd
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.FinEnum

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
deriving DecidableEq, Inhabited

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
| s₁, s₂ => s₁ < s₂ ∨ s₁ = s₂

/-
def State.le' : State → State → Prop
| s₁, s₂ => s₁.p ≤ s₂.p ∧ s₁.c ≤ s₂.c
-/

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

/- Consider letting there be different numbers of caches in cluster1 (`i`) and cluster2 (`j`) instead of
a fixed number (`n`) between both -/
-- variable (i j : Nat) -- number of caches for cluster1 and cluster2
variable (n : Nat) -- generic number of caches.

inductive ProtocolCacheInstance
| globalP : Fin 2 → ProtocolCacheInstance -- Fin 2 because there are 2 clusters
| cluster1 : Fin n → ProtocolCacheInstance
| cluster2 : Fin n → ProtocolCacheInstance
deriving DecidableEq

/-
set_option quotPrecheck false in
notation "ProtocolCacheInstance" => ProtocolCacheInstance' n
-/

inductive CacheId
| proxy : ProtocolInstance → CacheId
| cache : ProtocolCacheInstance n → CacheId
deriving DecidableEq

instance : Inhabited (CacheId n) where
  default := CacheId.proxy .global -- Junk

def CacheId.mkCacheGlobalP (m : Fin 2) : CacheId n := CacheId.cache (.globalP m)
def CacheId.mkCacheCluster1 (m : Fin n) : CacheId n := CacheId.cache (.cluster1 m)
def CacheId.mkCacheCluster2 (m : Fin n) : CacheId n := CacheId.cache (.cluster2 m)
def CacheId.mkProxy (n : Nat) (p : ProtocolInstance) : CacheId n := CacheId.proxy p

instance CacheId.mkCacheGlobalP_inj : Function.Injective (CacheId.mkCacheGlobalP n) := by
  simp[Function.Injective]
  simp[mkCacheGlobalP]
instance CacheId.mkCacheCluster1_inj : Function.Injective (CacheId.mkCacheCluster1 n) := by
  simp[Function.Injective]
  simp[mkCacheCluster1]
instance CacheId.mkCacheCluster2_inj : Function.Injective (CacheId.mkCacheCluster2 n) := by
  simp[Function.Injective]
  simp[mkCacheCluster2]
instance CacheId.mkCacheProxy_inj : Function.Injective (CacheId.mkProxy n) := by
  simp[Function.Injective]
  simp[mkProxy]

instance CacheId.isFintype : Fintype (CacheId n) where
  elems := by
    constructor
    case val =>
      exact (
        (List.finRange 2).map (CacheId.mkCacheGlobalP n ·) ++
        (List.finRange n).map (CacheId.mkCacheCluster1 n ·) ++
        (List.finRange n).map (CacheId.mkCacheCluster2 n ·) ++
        [CacheId.mkProxy n .global, CacheId.mkProxy n .cluster1, CacheId.mkProxy n .cluster2]
        )
    case nodup =>
      simp[List.nodup_append]
      apply And.intro
      . case left =>
        rw[List.nodup_map_iff]
        simp[List.nodup_finRange]
        simp[mkCacheGlobalP_inj,]
      . case right =>
        apply And.intro
        . case left =>
          apply And.intro
          . case left =>
            rw[List.nodup_map_iff]
            simp[List.nodup_finRange]
            simp[mkCacheCluster1_inj,]
          . case right =>
            apply And.intro
            . case left =>
              apply And.intro
              . case left =>
                rw[List.nodup_map_iff]
                simp[List.nodup_finRange]
                simp[mkCacheCluster2_inj,]
              . case right =>
                apply And.intro
                . case left =>
                  apply And.intro
                  . case left =>
                    apply And.intro
                    . case left => simp[mkProxy]
                    . case right => simp[mkProxy]
                  . case right => simp[mkProxy]
                . case right =>
                  intro fin
                  apply And.intro
                  . case left => simp[mkCacheCluster2, mkProxy]
                  . case right =>
                    apply And.intro
                    all_goals simp[mkProxy,mkCacheCluster1,mkCacheCluster2]
            . case right =>
              intro fin cid exist
              cases exist
              . case inl h =>
                rw[← h.choose_spec]
                simp[mkCacheCluster1, mkCacheCluster2]
              . case inr h =>
                cases h
                . case inl h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                . case inr h =>
                  cases h
                  . case inl h =>
                    rw[h]
                    simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                  . case inr h =>
                    rw[h]
                    simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
        . case right =>
          intro fin2 cid exist
          cases exist
          . case inl h =>
            rw[← h.choose_spec]
            simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
          . case inr h =>
            cases h
            . case inl h =>
              rw[← h.choose_spec]
              simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
            . case inr h =>
              cases h
              . case inl h =>
                rw[h]
                simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
              . case inr h =>
                cases h
                . case inl h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                . case inr h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
  complete := by
    intro cid
    induction cid with
    | proxy pi =>
      simp
      match pi with
      | .global =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        rfl
      | .cluster1 =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        rfl
      | .cluster2 =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        rfl
    | cache cache_inst =>
      simp
      match cache_inst with
      | .globalP fin2 =>
        apply Or.inl
        apply Exists.intro
        · rfl
      | .cluster1 fin =>
        apply Or.inr
        apply Or.inl
        apply Exists.intro
        · rfl
      | .cluster2 fin =>
        apply Or.inr
        apply Or.inr
        apply Or.inl
        apply Exists.intro
        · rfl

def MatchingProtocolInstances (pi : ProtocolInstance) (pci : ProtocolCacheInstance n) : Prop :=
  match pi, pci with
  | .global, .globalP _
  | .cluster1, .cluster1 _
  | .cluster2, .cluster2 _ => True
  | _, _ => False

def CacheId.sameProtocol (cid₁ cid₂ : CacheId n) : Prop :=
  match cid₁, cid₂ with
  | .proxy pinst₁, .proxy pinst₂ => pinst₁ = pinst₂
  | .cache pcinst₁, .cache pcinst₂ => match pcinst₁, pcinst₂ with
    | .globalP _, .globalP _
    | .cluster1 _, .cluster1 _
    | .cluster2 _, .cluster2 _ => True
    | _, _ => False
  | .cache pcinst, .proxy pinst => MatchingProtocolInstances n pinst pcinst
  | .proxy pinst, .cache pcinst => MatchingProtocolInstances n pinst pcinst

def CacheId.atProtocol (cid : CacheId n) (pi : ProtocolInstance) : Prop :=
  match cid with
  | .proxy pinst => pinst = pi
  | .cache pcinst => match pcinst, pi with
    | .globalP _, .global
    | .cluster1 _, .cluster1
    | .cluster2 _, .cluster2 => True
    | _, _ => False

structure CacheId.differentIdSameProtocol (cid cid_other : CacheId n) : Prop where
  ne : cid ≠ cid_other
  sameProtocol : cid.sameProtocol n cid_other

/-
set_option quotPrecheck false in
notation "CacheId" => CacheId' n
-/

abbrev Owner := CacheId n
abbrev Sharers := Finset (CacheId n)

/-
set_option quotPrecheck false in
notation "Owner" => Owner' n

set_option quotPrecheck false in
notation "Sharers" => Sharers' n
-/

inductive DirectoryState
| SW : StateSW → Owner n → DirectoryState
| MR : StateMR → Sharers n → DirectoryState
| Vd : StateVd → DirectoryState
| Vc : StateVc → DirectoryState
| I  : StateI  → DirectoryState
deriving DecidableEq, BEq, Inhabited

/-
set_option quotPrecheck false in
notation "DirectoryState" => DirectoryState' n
-/

def DirectoryState.CurrentSharers : DirectoryState n → Sharers n
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
def DirectoryState.toState : DirectoryState n → State
| ds => match ds with
  | .SW _ _ => ⟨some .wr, true⟩ -- SW state
  | .MR _ _ => ⟨some .r , true⟩ -- MR state
  | .Vd _ => ⟨some .wr, false⟩  -- Vd state
  | .Vc _ => ⟨some .r, false⟩   -- Vc State
  | .I  _ => ⟨none, false⟩      -- I State

/-
structure EntryState where
  cache : State
  directory : DirectoryState n
-/
/-- State of an address entry at a structure. -/
abbrev EntryState := State ⊕ DirectoryState n

def EntryState.cache (entry_state : EntryState n) : State :=
  match entry_state with
  | .inl cache_state => cache_state
  | .inr _ => panic! "EntryState expected to be cache state (State), but got (DirectoryState) instead!"

def EntryState.isCacheState (entry_state : EntryState n) : Prop := match entry_state with
  | .inl _ => true
  | .inr _ => false

def EntryState.directory (entry_state : EntryState n) : DirectoryState n :=
  match entry_state with
  | .inl _ => panic! "EntryState expected to be cache state (DirectoryState), but got (State) instead!"
  | .inr directory_state => directory_state

/- Define a few concrete cache entry states for convenience -/
abbrev SWEntry : EntryState n := Sum.inl SW
abbrev MREntry : EntryState n := Sum.inl MR
abbrev VdEntry : EntryState n := Sum.inl Vd
abbrev VcEntry : EntryState n := Sum.inl Vc
abbrev IEntry : EntryState n := Sum.inl I

def System.Cache := CacheId n → State
def System.Directory := ProtocolInstance → DirectoryState n

/-
set_option quotPrecheck false in
notation "System.Cache" => System.Cache' n

set_option quotPrecheck false in
notation "System.Directory" => System.Directory' n
-/

/- Initial System State -/
structure InitialSystemState where
  caches : Finset (CacheId n)
  cacheStates : System.Cache n
  directories : ProtocolInstance
  directoryStates : System.Directory n
