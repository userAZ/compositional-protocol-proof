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
deriving DecidableEq, Inhabited

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
          intro cid₁ hsame_cid cid₂ exist
          cases exist
          . case inl h =>
            rw[← h.choose_spec]
            simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
            cases hsame_cid
            . case inl hg_cid₁ =>
              rw[← hg_cid₁]
              simp[mkCacheGlobalP]
            . case inr hg_cid₁ =>
              rw[← hg_cid₁]
              simp[mkCacheGlobalP]
          . case inr h =>
            cases h
            . case inl h =>
              rw[← h.choose_spec]
              rw[Eq.comm] at hsame_cid
              nth_rw 2 [Eq.comm] at hsame_cid
              simp_all[Eq.symm,mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
              cases hsame_cid
              . case inl hg_cid₁ =>
                rw[hg_cid₁]
                simp
              . case inr hg_cid₁ =>
                rw[hg_cid₁]
                simp
            . case inr h =>
              cases h
              . case inl h =>
                rw[h]
                rw[Eq.comm] at hsame_cid
                nth_rw 2 [Eq.comm] at hsame_cid
                simp_all[Eq.symm,mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                cases hsame_cid
                . case inl hg_cid₁ =>
                  rw[hg_cid₁]
                  simp
                . case inr hg_cid₁ =>
                  rw[hg_cid₁]
                  simp
              . case inr h =>
                cases h
                . case inl h =>
                  rw[h]
                  rw[Eq.comm] at hsame_cid
                  nth_rw 2 [Eq.comm] at hsame_cid
                  simp_all[Eq.symm,mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                  cases hsame_cid
                  . case inl hg_cid₁ =>
                    rw[hg_cid₁]
                    simp
                  . case inr hg_cid₁ =>
                    rw[hg_cid₁]
                    simp
                . case inr h =>
                  rw[h]
                  rw[Eq.comm] at hsame_cid
                  nth_rw 2 [Eq.comm] at hsame_cid
                  simp_all[Eq.symm,mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                  cases hsame_cid
                  . case inl hg_cid₁ =>
                    rw[hg_cid₁]
                    simp
                  . case inr hg_cid₁ =>
                    rw[hg_cid₁]
                    simp
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
        simp[mkCacheGlobalP]
        grind only
        -- apply Exists.intro
        -- · rfl
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

abbrev DirI : DirectoryState n := DirectoryState.I ⟨I, by simp⟩

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

def EntryState.state (entry_state : EntryState n) : State :=
  match entry_state with
  | .inl cache_state => cache_state
  | .inr dir_state => dir_state.toState

def EntryState.isCacheState (entry_state : EntryState n) : Prop := match entry_state with
  | .inl _ => True
  | .inr _ => False

def EntryState.isDirectoryState (entry_state : EntryState n) : Prop := match entry_state with
  | .inl _ => False
  | .inr _ => True

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

/- ========== State Lemmas/Proofs ========== -/

/-- Helper: If s₁ ≤ s₂, then s₂.c is at least s₁.c -/
lemma State.le_coherent_preserved {s₁ s₂ : State} (h : s₁ ≤ s₂) : s₁.c ≤ s₂.c := by
  dsimp [LE.le] at h
  unfold State.le at h
  cases h with
  | inl hlt =>
    unfold State.lt at hlt
    exact hlt.2.1
  | inr heq =>
    rw [heq]

/-- Helper: If s₁ ≤ s₂ and s₁.c = true, then s₂.c = true -/
lemma State.le_coherent_true {s₁ s₂ : State} (h : s₁ ≤ s₂) (hc : s₁.c = true) : s₂.c = true := by
  have hle := State.le_coherent_preserved h
  rw [hc] at hle
  cases hs2c : s₂.c
  · -- s₂.c = false, but we have true ≤ false - contradiction
    rw [hs2c] at hle
    nomatch hle
  · rfl

/-- Helper: If s₁ ≤ s₂, then s₂.p is at least s₁.p -/
axiom State.le_perm_preserved {s₁ s₂ : State} (h : s₁ ≤ s₂) : s₁.p ≤ s₂.p

/-- Helper: If s₁ ≤ s₂ and s₁.p = some .wr, then s₂.p = some .wr -/
lemma State.le_perm_wr {s₁ s₂ : State} (h : s₁ ≤ s₂) (hp : s₁.p = some .wr) : s₂.p = some .wr := by
  have hle := State.le_perm_preserved h
  rw [hp] at hle
  cases hs2 : s₂.p with
  | none =>
    rw [hs2] at hle
    -- Have: some .wr ≤ none, contradiction
    nomatch hle
  | some p₂ =>
    cases p₂ with
    | r =>
      rw [hs2] at hle
      -- Have: some .wr ≤ some .r, which means .wr ≤ .r, contradiction
      nomatch hle
    | wr => rfl

lemma ReadWritePermissions.lt_trans {p₁ p₂ p₃ : ReadWritePermissions} (h₁₂ : p₁ < p₂) (h₂₃ : p₂ < p₃) : p₁ < p₃ := by
  simp[LT.lt, ReadWritePermissions.lt] at *
  apply And.intro
  . case left => simp [h₁₂.left]
  . case right => simp [h₂₃.right]

lemma ReadWritePermissions.lt_eq_trans {p₁ p₂ p₃ : ReadWritePermissions} (h₁₂ : p₁ < p₂) (h₂₃ : p₂ = p₃) : p₁ < p₃ := by
  rw[h₂₃] at h₁₂
  exact h₁₂

lemma ReadWritePermissions.eq_le_trans {p₁ p₂ p₃ : ReadWritePermissions} (h₁₂ : p₁ = p₂) (h₂₃ : p₂ ≤ p₃) : p₁ ≤ p₃ := by
  rw[← h₁₂] at h₂₃
  exact h₂₃

lemma Permissions.le_trans {p₁ p₂ p₃ : Permissions} (h₁₂ : p₁ ≤ p₂) (h₂₃ : p₂ ≤ p₃) : p₁ ≤ p₃ := by
  cases p₁ with
  | none =>
    cases p₃ with
    | none => simp
    | some perm₃ => simp
  | some perm₁ =>
    cases p₃ with
    | none =>
      simp
      simp_all only [Option.le_none, reduceCtorEq]
    | some perm₃ =>
      simp
      simp [LE.le]
      simp[ReadWritePermissions.le]
      cases p₂ with
      | none =>
        simp at h₁₂
      | some perm₂ =>
        simp at h₁₂ h₂₃
        cases h₁₂
        . case some.some.some.inl hp₁_lt_p₂ =>
          cases h₂₃
          . case inl hp₂_lt_p₃ =>
            apply Or.intro_left
            apply ReadWritePermissions.lt_trans hp₁_lt_p₂ hp₂_lt_p₃
          . case inr hp₂_eq_p₃ =>
            apply Or.intro_left
            apply ReadWritePermissions.lt_eq_trans hp₁_lt_p₂ hp₂_eq_p₃
        . case some.some.some.inr hp₁_eq_p₂ =>
          apply ReadWritePermissions.eq_le_trans hp₁_eq_p₂ h₂₃

lemma State.lt_trans {s₁ s₂ s₃ : State} (h₁₂ : s₁ < s₂) (h₂₃ : s₂ < s₃) : s₁ < s₃ := by
  simp only [LT.lt, State.lt] at h₁₂ h₂₃ ⊢
  obtain ⟨hp₁₂, hc₁₂, hne₁₂⟩ := h₁₂
  obtain ⟨hp₂₃, hc₂₃, hne₂₃⟩ := h₂₃
  apply And.intro
  · -- Permissions transitivity: s₁.p ≤ s₃.p
    exact Permissions.le_trans hp₁₂ hp₂₃
  · apply And.intro
    · -- Coherence transitivity: s₁.c ≤ s₃.c
      exact le_trans hc₁₂ hc₂₃
    · -- Inequality: s₁ ≠ s₃
      intro hfalse
      rw [hfalse] at hp₁₂ hc₁₂ hne₁₂
      -- After substitution: hp₁₂ : s₃.p ≤ s₂.p, hc₁₂ : s₃.c ≤ s₂.c
      -- Combined with hp₂₃ : s₂.p ≤ s₃.p and hc₂₃ : s₂.c ≤ s₃.c
      have hc_eq : s₂.c = s₃.c := le_antisymm hc₂₃ hc₁₂
      -- For permissions: s₂.p ≤ s₃.p and s₃.p ≤ s₂.p implies s₂.p = s₃.p
      have hp_eq : s₂.p = s₃.p := by
        -- Case analysis on the structure
        cases hperm2 : s₂.p with
        | none =>
          cases hperm3 : s₃.p with
          | none => rfl
          | some p =>
            -- s₂.p = none, s₃.p = some p
            -- Then hp₁₂: some p ≤ none is false (contradicts being a proof)
            exfalso
            simp only [hperm2, hperm3, LE.le, Permissions.le, Option.le] at hp₁₂
        | some p₂ =>
          cases hperm3 : s₃.p with
          | none =>
            -- s₂.p = some p₂, s₃.p = none
            -- Then hp₂₃: some p₂ ≤ none is false
            exfalso
            simp only [hperm2, hperm3, LE.le, Permissions.le, Option.le] at hp₂₃
          | some p₃ =>
            -- s₂.p = some p₂, s₃.p = some p₃
            -- hp₂₃: some p₂ ≤ some p₃, hp₁₂: some p₃ ≤ some p₂
            simp only [hperm2, hperm3, LE.le, Permissions.le, Option.le] at hp₁₂ hp₂₃
            -- Now hp₂₃ and hp₁₂ should be ReadWritePermissions.le after Option.le reduces
            -- ReadWritePermissions.le is p₁ < p₂ ∨ p₁ = p₂
            rcases hp₂₃ with h₂₃_lt | h₂₃_eq
            · -- p₂ < p₃: so p₂ = .r and p₃ = .wr
              rcases hp₁₂ with h₁₂_lt | h₁₂_eq
              · -- p₃ < p₂: so p₃ = .r and p₂ = .wr
                -- Extract the equalities and derive contradiction
                obtain ⟨hp₂_eq_r, hp₃_eq_wr⟩ := h₂₃_lt
                obtain ⟨hp₃_eq_r, hp₂_eq_wr⟩ := h₁₂_lt
                rw [hp₃_eq_wr] at hp₃_eq_r
                exact absurd hp₃_eq_r (by decide : ¬(ReadWritePermissions.wr = ReadWritePermissions.r))
              · -- p₃ = p₂: contradicts p₂ < p₃
                rw [← h₁₂_eq] at h₂₃_lt
                -- Now h₂₃_lt : p₃ < p₃, which unfolds to p₃ = .r ∧ p₃ = .wr
                -- Extract the two claims
                have h_r : p₃ = .r := h₂₃_lt.1
                have h_wr : p₃ = .wr := h₂₃_lt.2
                -- But p₃ can't be both r and wr
                rw [h_r] at h_wr
                exact absurd h_wr (by decide)
            · -- p₂ = p₃
              simp [h₂₃_eq]
      -- Therefore s₂ = s₃
      have h_eq : s₂ = s₃ := by
        cases s₂; cases s₃; simp at hp_eq hc_eq; exact congrArg₂ State.mk hp_eq hc_eq
      exact hne₂₃ h_eq

lemma State.lt_eq_trans {s₁ s₂ s₃ : State} (h₁₂ : s₁ < s₂) (h₂₃ : s₂ = s₃) : s₁ < s₃ := by
  rw [← h₂₃]
  exact h₁₂

lemma State.eq_lt_trans {s₁ s₂ s₃ : State} (h₁₂ : s₁ = s₂) (h₂₃ : s₂ < s₃) : s₁ < s₃ := by
  rw [h₁₂]
  exact h₂₃

lemma State.eq_eq_trans {s₁ s₂ s₃ : State} (h₁₂ : s₁ = s₂) (h₂₃ : s₂ = s₃) : s₁ = s₃ := by rw [h₁₂, h₂₃]

/- TODO NOTE: This lemma is for the case `hasPerms`. Create a version of this lemma for the other case
  `ncRelAcqWeakWriteHasCoherentPerms` in lemma `noInterveningWrites_diffCache_sameProtocol_case` -/
lemma State.le_trans {s₁ s₂ s₃ : State} (h₁₂ : s₁ ≤ s₂) (h : s₂ ≤ s₃) : s₁ ≤ s₃ := by
  simp[LE.le, State.le] at *
  cases h₁₂
  . case inl hs₁_lt_s₂ =>
    cases h
    . case inl hs₂_lt_s₃ =>
      apply Or.intro_left
      apply State.lt_trans hs₁_lt_s₂ hs₂_lt_s₃
    . case inr hs₂_eq_s₃ =>
      apply Or.intro_left
      apply State.lt_eq_trans hs₁_lt_s₂ hs₂_eq_s₃
  . case inr hs₁_eq_s₂ =>
    cases h
    . case inl hs₂_lt_s₃ =>
      apply Or.intro_left
      apply State.eq_lt_trans hs₁_eq_s₂ hs₂_lt_s₃
    . case inr hs₂_eq_s₃ =>
      apply Or.intro_right
      rw [hs₁_eq_s₂, hs₂_eq_s₃]
