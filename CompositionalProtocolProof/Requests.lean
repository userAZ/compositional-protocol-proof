import CompositionalProtocolProof.Common
import CompositionalProtocolProof.States
import Mathlib

inductive ReadWrite
| r : ReadWrite
| w : ReadWrite
deriving DecidableEq

-- abbrev Coherent, from Common.

inductive Consistency
| SC : Consistency
| Rel : Consistency
| Acq : Consistency
| Weak : Consistency
deriving DecidableEq

structure Request where
  rw          : ReadWrite
  coherent    : Coherent
  consistency : Consistency
deriving DecidableEq

inductive LazyEager
| lazy : LazyEager
| eager : LazyEager

def ReadWrite.toRWPerms : ReadWrite → ReadWritePermissions
| rw => match rw with
  | .w => .wr
  | .r => .r

def ReadWrite.toPerms : ReadWrite → Permissions
| rw => some rw.toRWPerms

def Request.isCoherent (r : Request) : Prop := r.coherent
def Request.nonCoherent (r : Request) : Prop := ¬ r.coherent

abbrev Request.SC := λ r : Request => r.rw = .r ∧ r.consistency = .SC

abbrev Request.ReadAcquire := λ r : Request => r.rw = .r ∧ r.consistency = .Acq
abbrev Request.WeakRead := λ r : Request => r.rw = .r ∧ r.consistency = .Weak
-- Disallowed Requests
abbrev Request.SCNonCoherent := λ r : Request => r.consistency = .SC ∧ r.coherent = false
abbrev Request.WriteAcquire := λ r : Request => r.rw = .w ∧ r.consistency = .Acq
abbrev Request.ReadRelease := λ r : Request => r.rw = .r ∧ r.consistency = .Rel
abbrev Request.CoherentAcquire := λ r : Request => r.ReadAcquire ∧ r.coherent = true
abbrev Request.CoherentWeakRead := λ r : Request => r.WeakRead ∧ r.coherent = true
-- Valid Request does not contain disallowed requests.
abbrev Request.NoSCNonCoherent := λ r : Request => ¬r.SCNonCoherent
abbrev Request.NoWriteAcquire := λ r : Request => ¬r.WriteAcquire
abbrev Request.NoReadRelease := λ r : Request => ¬r.ReadRelease
abbrev Request.NoCoherentAcquire := λ r : Request => r.consistency = .Acq → ¬ r.coherent -- ¬r.CoherentAcquire
abbrev Request.NoCoherentWeakRead := λ r : Request => ¬r.CoherentWeakRead

structure Request.IsValid (r : Request) : Prop where
  non_coherent : r.NoSCNonCoherent -- := by simp
  no_write_acq : r.NoWriteAcquire -- := by simp
  no_read_rel : r.NoReadRelease -- := by simp
  no_cacq : r.NoCoherentAcquire -- := by simp
  no_cwr : r.NoCoherentWeakRead -- := by simp

def Request.IsValid' (r : Request) : Prop :=
  r.NoSCNonCoherent ∧ r.NoWriteAcquire ∧ r.NoReadRelease ∧ r.NoCoherentAcquire ∧ r.NoCoherentWeakRead

abbrev ValidRequest := {r : Request // Request.IsValid' r}

/-- Definition 2.12 Minimum Required State of a request. -/
def ValidRequest.MRS : ValidRequest → State
| ⟨⟨rw,true,.SC⟩,_⟩ => ⟨rw.toPerms, true⟩
| ⟨⟨.w,true,.Rel⟩,_⟩ => ⟨some .wr, true⟩
| ⟨⟨.w,true,.Weak⟩,_⟩ => ⟨some .wr, true⟩
| ⟨⟨_,false,.Weak⟩,_⟩ => Vc
| ⟨⟨.w,false,.Rel⟩,_⟩ => Vd
| ⟨⟨.r,false,.Acq⟩,_⟩ => Vc

abbrev SCWrite : ValidRequest := ⟨⟨.w, true, .SC⟩, by simp[Request.IsValid']⟩
abbrev SCRead : ValidRequest := ⟨⟨.r, true, .SC⟩, by simp[Request.IsValid']⟩
abbrev RelWrite : ValidRequest := ⟨⟨.w, false, .Rel⟩, by simp[Request.IsValid']⟩
abbrev CoherentRelWrite : ValidRequest := ⟨⟨.w, true, .Rel⟩, by simp[Request.IsValid']⟩
abbrev AcqRead : ValidRequest := ⟨⟨.r, false, .Acq⟩, by simp[Request.IsValid']⟩
abbrev NonCoherentWeakRead : ValidRequest := ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩
abbrev NonCoherentWeakWrite : ValidRequest := ⟨⟨.w, false, .Weak⟩, by simp[Request.IsValid']⟩
abbrev CoherentWeakWrite : ValidRequest := ⟨⟨.w, true, .Weak⟩, by simp[Request.IsValid']⟩
abbrev CoherentRelease : ValidRequest := ⟨⟨.w, true, .Rel⟩, by simp[Request.IsValid']⟩

def ValidRequest.isCoherent (vr : ValidRequest) : Prop := vr.val.isCoherent

abbrev ValidRequest.NonCoherent (vr : ValidRequest) : Prop := vr.val.nonCoherent
abbrev ValidRequest.SC (vr : ValidRequest) : Prop := vr.val.SC

def Request.isWrite (r : Request) : Prop := r.rw = .w
def Request.isCoherentWrite (r : Request) : Prop := r.isCoherent ∧ r.isWrite
def ValidRequest.isCoherentWrite (vr : ValidRequest) : Prop := vr.val.isCoherentWrite

def Request.isRead (r : Request) : Prop := r.rw = .r
def Request.isCoherentRead (r : Request) : Prop := r.isCoherent ∧ r.isRead
def ValidRequest.isCoherentRead (vr : ValidRequest) : Prop := vr.val.isCoherentRead

def ValidRequest.isAcquire (vr : ValidRequest) := vr = ⟨⟨.r, false, .Acq⟩, by simp[Request.IsValid']⟩
def ValidRequest.isNcRelease (vr : ValidRequest) := vr = ⟨⟨.w, false, .Rel⟩, by simp[Request.IsValid']⟩
def ValidRequest.isNonCoherent (vr : ValidRequest) := ¬ vr.val.coherent
def ValidRequest.isWeak (vr : ValidRequest) := vr.val.consistency = .Weak
def ValidRequest.isNcWeakRead (vr : ValidRequest) := vr = ⟨⟨.r, false, .Weak⟩, by simp[Request.IsValid']⟩
def ValidRequest.isNcWeakWrite (vr : ValidRequest) := vr = ⟨⟨.w, false, .Weak⟩, by simp[Request.IsValid']⟩
def ValidRequest.isCWeakWrite (vr : ValidRequest) := vr = ⟨⟨.w, true, .Weak⟩, by simp[Request.IsValid']⟩

def ValidRequest.isSCWrite (vr : ValidRequest) := vr = ⟨⟨.w, true, .SC⟩,by simp[Request.IsValid']⟩
def ValidRequest.isSCRead (vr : ValidRequest) := vr = ⟨⟨.r, true, .SC⟩, by simp [Request.IsValid']⟩
/-
abbrev NonCoherentWeakRead : Request := ⟨.r, false, .Weak⟩
abbrev NonCoherentWeakWrite : Request := ⟨.w, false, .Weak⟩
abbrev NonCoherentReleaseWrite : Request := ⟨.w, false, .Rel⟩
abbrev NonCoherentAcquire : Request := ⟨.r, false, .Acq⟩
-/

-- abbrev Request.NonCoherentWrite := λ r : Request => r.rw = .w ∧ r.coherent = false
-- abbrev NoWeakWriteOnMR := λ (r : Request) (s : State) => ¬(r.NonCoherentWrite ∧ s = MR)

/- 1. Want to specify that request is a request allowed by the family of interfaces -/
/- 2. Can I remove the "Option" from Option State? -/
/- 3. Likely need to constrain state to allowable states a request can be on -/

-- NOTE: move protocol interface here.
structure ContainsSCNotRel (vr : Set ValidRequest) : Prop where
  scInVr : SCWrite ∈ vr
  relNotInVr : RelWrite ∉ vr
  cRelNotinVr : CoherentRelWrite ∉ vr
structure ContainsNCRelNotSC (vr : Set ValidRequest) : Prop where
  scNotInVr : SCWrite ∉ vr
  relInVr : RelWrite ∈ vr
  cRelNotInVr : CoherentRelWrite ∉ vr
structure ContainsCRelNotSCOrRel (vr : Set ValidRequest) : Prop where
  scNotInVr : SCWrite ∉ vr
  relNotInVr : RelWrite ∉ vr
  cRelInVr : CoherentRelWrite ∈ vr
def ContainsEitherSCOrRelOrCRel (vr : Set ValidRequest) : Prop := ContainsSCNotRel vr ∨ ContainsNCRelNotSC vr ∨ ContainsCRelNotSCOrRel vr

structure ContainsSCNotAcq (vr : Set ValidRequest) : Prop where
  scInVr : SCRead ∈ vr
  acqNotInVr : AcqRead ∉ vr
structure ContainsAcqNotSC (vr : Set ValidRequest) : Prop where
  scNotInVr : SCRead ∉ vr
  acqInVr : AcqRead ∈ vr
def ContainsEitherSCOrAcq (vr : Set ValidRequest) : Prop := ContainsSCNotAcq vr ∨ ContainsAcqNotSC vr

def ValidRequest.isAcqLabel (vr : ValidRequest) := vr.val.consistency = .Acq
def ValidRequest.isRelLabel (vr : ValidRequest) := vr.val.consistency = .Rel

structure FollowsProtocolInterface (vrs : Set ValidRequest) where
  /- "Positive" restrictions (if `r` ∈ vrs, then `r1` ∈ vrs) -/
  sc_rel_crel : ContainsEitherSCOrRelOrCRel vrs := by simp
  sc_or_acq : ContainsEitherSCOrAcq vrs := by simp
  write_read : SCWrite ∈ vrs → SCRead ∈ vrs := by simp
  rel_write_acq : (RelWrite ∈ vrs ∨ CoherentRelWrite ∈ vrs) → AcqRead ∈ vrs := by simp
  acq_weak : AcqRead ∈ vrs → NonCoherentWeakRead ∈ vrs := by simp
  real_weak : RelWrite ∈ vrs → NonCoherentWeakWrite ∈ vrs := by simp
  rel_weak_coherent : CoherentRelWrite ∈ vrs → (CoherentWeakWrite ∈ vrs ∨ NonCoherentWeakWrite ∈ vrs) := by simp
  /- "Negative" restrictions (if `r` ∈ vrs, then `r1` ∉ vrs) -/
  /- No mixing MSI and RCC requests. -/
  nc_no_sc : ∀ vr ∈ vrs, vr ∈ vrs ∧ (vr.NonCoherent ∨ vr.isAcqLabel ∨ vr.isRelLabel) → SCWrite ∉ vrs ∧ SCRead ∉ vrs := by simp
  sc_no_nc : SCWrite ∈ vrs ∨ SCRead ∈ vrs → ∀ vr ∈ vrs, vr.NonCoherent ∨ vr.isAcqLabel ∨ vr.isRelLabel → vr ∉ vrs := by simp
  /- No mixing multiple flavours of RCC requests. -/
  only_one_rel : RelWrite ∈ vrs → CoherentRelWrite ∉ vrs ∧ CoherentRelWrite ∉ vrs → RelWrite ∈ vrs := by simp
  nc_rel_no_coh_ww : RelWrite ∈ vrs → CoherentWeakWrite ∉ vrs := by simp
  coh_rel_one_ww : CoherentRelWrite ∈ vrs → ((CoherentWeakWrite ∈ vrs ∧ NonCoherentWeakWrite ∉ vrs) ∨ (CoherentWeakWrite ∉ vrs ∧ NonCoherentWeakWrite ∈ vrs)) := by simp

def Request.toState : Request → State
| ⟨rw, coherent, _⟩ => ⟨rw.toPerms, coherent⟩

def ValidRequest.toState : ValidRequest → State
| ⟨req, _⟩ => req.toState

/-- What is the state a request leaves a cache entry in.  -/
def ValidRequest.RequestState /-{pi : ProtocolInterface}-/ (vr : ValidRequest) (s : State) /-(h_vr_in_pi : vr ∈ pi.val) (h_pi_has_s : pi.HasState s)-/ : State :=
  match vr with
  | ⟨⟨_, true, _⟩, _⟩ | ⟨⟨.r, false, .Weak⟩, _⟩ =>
    if vr.MRS ≤ s then s
    else vr.MRS
  | ⟨⟨.w, false, .Weak⟩, _⟩ =>
    match s with
    | ⟨some .wr, true⟩ => s
    | ⟨some .r,  true⟩ => Vd -- none -- can avoid `none` by using contradiction from commented-out input arg `h_pi_has_s` and Lemma `ncw_impl_no_mr`.
    | _ => Vd
  | ⟨⟨.w, false, .Rel⟩, _⟩ =>
    match s with
    | ⟨some .wr, true⟩ => s
    | ⟨some .r,  true⟩ => Vc -- none -- can avoid `none` by using contradiction from commented-out input arg `h_pi_has_s` and Lemma `ncw_impl_no_mr`.
    | _ => Vc
  | ⟨⟨.r, false, .Acq⟩, _⟩ => Vc

noncomputable def ValidRequest.DowngradeState (vr : ValidRequest) : State → State
| s => match vr.val.coherent with
  | true =>
    match vr.val.consistency with
    | .Rel | .Weak | .Acq =>
      if s ≤ Vc then s
      else Vc
    | .SC =>
      if s ≤ vr.MRS then I
      else vr.MRS
  | false =>
    if vr.val = NonCoherentWeakRead then
      if s = Vc then I
      else s -- Junk. This is a self-invalidate
    else if vr.val = NonCoherentWeakWrite ∨ vr.val = RelWrite then
      if s = Vd then Vc
      else s -- Junk. This is a write-back to directory
    else s -- Junk. There are no other downgrade events we consider

def ProtocolInterface := {vr : Set ValidRequest // FollowsProtocolInterface vr}

instance : Membership (ValidRequest) (ProtocolInterface) := ⟨fun pi vr => vr ∈ pi.val⟩

/-- Def 2.42: a SWMR protocol. -/
def ProtocolInterface.swmrProtocol : ProtocolInterface := ⟨{SCWrite, SCRead}, by
  all_goals constructor
  all_goals simp [autoParam]
  all_goals constructor
  all_goals try simp[ValidRequest.NonCoherent, Request.nonCoherent, ValidRequest.isAcqLabel, ValidRequest.isRelLabel]
  all_goals constructor
  all_goals simp
  ⟩

def ProtocolInterface.isSWMR : ProtocolInterface → Prop
| pi => pi = swmrProtocol

def ProtocolInterface.ProtocolStates : ProtocolInterface → Set State
| pi => pi.val.image (·.toState)

structure ValidProtocolRequest' (pi : ProtocolInterface) (vr : ValidRequest) : Prop where
  vrInPI : vr ∈ pi.val

def ProtocolInterface.HasState : ProtocolInterface → State → Prop
| pi, s => ∃ vr ∈ pi.val, vr.toState = s

/-- Interface of each protocol "cluster" -/
structure Protocol.interface where
  global_pi : ProtocolInterface
  cluster1_pi : ProtocolInterface
  cluster2_pi : ProtocolInterface

/-- Axiom 14, the global protocol is a SWMR protocol. -/
def Protocol.globalSWMR (pi : Protocol.interface) : Prop := pi.global_pi = ProtocolInterface.swmrProtocol

/- Not worth trying to prove right now.
def ProtocolInterface.HasDirState : ProtocolInterface → DirectoryState → Prop
| pi, ds => ∃ vr ∈ pi.val, vr.toState = ds.toState

/- Be careful using this one, if not intending to use Directory state. -/
def ProtocolInterface.HasEntryState : ProtocolInterface → EntryState → Prop
| pi, entry_s => pi.HasState entry_s.cache ∧ pi.HasDirState entry_s.directory
-/

lemma vr_rel_write_in_pi_impl_rel_write_in_pi {pi : ProtocolInterface} (vr : ValidRequest) (h_vr_in_pi : vr ∈ pi.val)
(h_vr_is_ncw : vr.val = RelWrite) : RelWrite ∈ pi.val := by
  simp_all only
  obtain ⟨val, prop⟩ := vr
  subst h_vr_is_ncw
  simp_all only

/-
lemma non_coherent_in_pi_impl_no_sc_read  {pi : ProtocolInterface} (vr : ValidRequest) (h_vr_in_pi : vr ∈ pi.val)
(h_vr_is_ncw : vr.NonCoherent) : SCRead ∉ pi.val := by
  have h_nc_no_sc := pi.prop.nc_no_sc h_vr_in_pi h_vr_is_ncw
  exact h_nc_no_sc.right
-/
/-
lemma ncw_impl_no_mr {pi : ProtocolInterface} (vr : ValidRequest) (s : State) (h_vr_in_pi : vr ∈ pi.val) (h_s_in_pi : pi.HasState s)
(h_vr_is_ncw : vr.val = RelWrite ∨ vr.val = NonCoherentWeakWrite) (h_s_mr : s = MR) : ¬ pi.HasState s := by
  /- Use PI and h_vr_is_ncw to constrain which VRs are in PI.
  No VR by the constraints of PI produce state MR. -/
  unfold ProtocolInterface.HasState
  subst h_s_mr
  simp

  /- Show no request in pi produces MR state. -/
  intro req hreq_valid hreq_in_pi
  match hreq : req with
    /- Main case: Coherent Read isn't allowed -/
  | ⟨.r, true, .SC⟩ =>
    cases h_vr_is_ncw
    . case inl h_vr_relw =>
      have h_vr_noncoherent : vr.NonCoherent := by
        unfold NonCoherentWeakWrite at h_vr_relw
        unfold ValidRequest.NonCoherent
        unfold Request.nonCoherent
        simp[h_vr_relw]
      have h_no_sc_write_read := pi.prop.nc_no_sc h_vr_in_pi h_vr_noncoherent
      have h_no_sc_read := h_no_sc_write_read.right
      unfold SCRead at h_no_sc_read
      contradiction
    . case inr h_vr_ncww =>
      have h_vr_noncoherent : vr.NonCoherent := by
        unfold NonCoherentWeakWrite at h_vr_ncww
        unfold ValidRequest.NonCoherent
        unfold Request.nonCoherent
        simp[h_vr_ncww]
      have h_no_sc_write_read := pi.prop.nc_no_sc h_vr_in_pi h_vr_noncoherent
      have h_no_sc_read := h_no_sc_write_read.right
      unfold SCRead at h_no_sc_read
      contradiction
    -- absurd h_no_scread_in_pi (by simp [hreq_in_pi]) -- Odd, using absurd leaves this case with a red underline..?
    /- Cases where Request does not map to MR state. -/
  | ⟨.w, false, .Rel⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    simp
  | ⟨.w, true, .Rel⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
  | ⟨.w, true, .SC⟩ =>
    /- Also can't have SC Write `req` with with Release Write `vr`, but this is easier. -/
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
  | ⟨.w, true, .Weak⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
  | ⟨.w, false, .Weak⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
  | ⟨.r, false, .Acq⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
  | ⟨.r, false, .Weak⟩ =>
    unfold ValidRequest.toState
    unfold Request.toState
    unfold ReadWrite.toPerms
    unfold ReadWrite.toRWPerms
    simp
    /- Cases of Disallowed Requests below. -/
  | ⟨.r, false, .SC⟩ =>
    subst hreq

    have hreq_no_noncoherent := hreq_valid.non_coherent
    simp at hreq_no_noncoherent
    /-
    unfold Request.NoSCNonCoherent at hreq_no_noncoherent
    unfold Request.SCNonCoherent at hreq_no_noncoherent
    simp at hreq_no_noncoherent
    -/
  | ⟨.r, true, .Weak⟩ =>
    subst hreq
    have hreq_no_cwr := hreq_valid.no_cwr
    simp at hreq_no_cwr
  | ⟨.w, false, .SC⟩ =>
    subst hreq
    have hreq_no_noncoherent := hreq_valid.non_coherent
    simp at hreq_no_noncoherent
  | ⟨.r, true, .Acq⟩ =>
    subst hreq
    have hreq_no_cacq := hreq_valid.no_cacq
    simp at hreq_no_cacq
  | ⟨.w, false, .Acq⟩ =>
    subst hreq
    have hreq_no_wacq := hreq_valid.no_write_acq
    simp at hreq_no_wacq
  | ⟨.r, false, .Rel⟩ =>
    subst hreq
    have hreq_no_rrel := hreq_valid.no_read_rel
    simp at hreq_no_rrel

lemma pi_ncw_on_mr_contradiction {pi : ProtocolInterface} (vr : ValidRequest) (s : State) (h_vr_in_pi : vr ∈ pi.val) (h_s_in_pi : pi.HasState s)
(h_vr_is_ncw : vr.val = RelWrite ∨ vr.val = NonCoherentWeakWrite) (h_s_mr : s = MR) : False := by
  have h_s_not_mr := ncw_impl_no_mr vr s h_vr_in_pi h_s_in_pi h_vr_is_ncw h_s_mr
  absurd h_s_not_mr h_s_in_pi
  contradiction
-/

/- Not worth trying to prove right now.
lemma ValidRequest.RequestState_in_pi {pi : ProtocolInterface} (vr : ValidRequest) (s : State)
(h_vr_in_pi : vr ∈ pi.val) (h_pi_has_s : pi.HasState s) : let next_state := ValidRequest.RequestState vr s h_vr_in_pi h_pi_has_s; pi.HasState next_state := by
  -- intro next_state
  -- unfold next_state
  -- unfold RequestState
  -- simp
  unfold ProtocolInterface.HasState
  simp
  apply Exists.intro
  . case h =>
    cases vr
  match hvr : vr.val with
  | ⟨_, true, _⟩ | ⟨.r, false, .Weak⟩ =>
    if s ≤ vr.MRS then s
    else vr.MRS -- Must be a way to state this does not produce a
  | ⟨.w, false, .Weak⟩ =>
    match hs : s with
    | ⟨some .wr, true⟩ => s
    | ⟨some .r,  true⟩ => -- none -- can avoid `none` by using co
      -- /- Can use this proof instead to state this case isn't p
      by
      have h_s_is_mr : s = MR := by simp[hs]
      have h_vr_is_ncw : vr.val = RelWrite ∨ vr.val = NonCoherent
      have h_s_not_mr := ncw_impl_no_mr vr s h_vr_in_pi (by subst

      subst hs
      absurd h_s_not_mr h_pi_has_s
      contradiction
      -- -/
    | _ => Vd
  | ⟨.w, false, .Rel⟩ =>
    match hs : s with
    | ⟨some .wr, true⟩ => s
    | ⟨some .r,  true⟩ => -- none -- can avoid `none` by using co
      by
      have h_s_is_mr : s = MR := by simp[hs]
      have h_vr_is_ncw : vr.val = RelWrite ∨ vr.val = NonCoherent
      have h_s_not_mr := ncw_impl_no_mr vr s h_vr_in_pi (by subst

      subst hs
      absurd h_s_not_mr h_pi_has_s
      contradiction
    | _ => Vc
  | ⟨.r, false, .Acq⟩ => Vc
  | ⟨.w, false, .SC ⟩ | ⟨.r, false, .SC ⟩ => absurd vr.prop.non_c
  | ⟨.w, false, .Acq⟩ => absurd vr.prop.no_write_acq (by simp [h]
  | ⟨.r, false, .Rel⟩ => absurd vr.prop.no_read_rel (by simp [h])
  sorry
-/

/-
lemma ValidRequest.RequestState_never_none {pi : ProtocolInterface} (vr : ValidRequest) (s : State) (h_vr_in_pi : vr ∈ pi.val) (h_pi_has_s : pi.HasState s) : ValidRequest.RequestState vr s ≠ none := by
  unfold ValidRequest.RequestState
  simp
  unfold ValidRequest.MRS
  simp

  match hvr_req : vr with
  | ⟨⟨_, true, _⟩, _⟩
  | ⟨⟨.r, false, .Weak⟩, _⟩ =>
    simp
    subst hvr_req
    -- aesop?
    apply Aesop.BuiltinRules.not_intro
    intro a
    split at a
    next h => simp_all only [reduceCtorEq]
    next h => simp_all only [reduceCtorEq]
  | ⟨⟨.w, false, .Weak⟩, _⟩
  | ⟨⟨.w, false, .Rel⟩, _⟩ =>
    match hs : s with
    | ⟨some .wr, true⟩ => simp
    | ⟨some .r, true⟩ =>
      have h_s_is_mr : s = MR := by simp[hs]
      have h_vr_is_ncw : vr.val = RelWrite ∨ vr.val = NonCoherentWeakWrite := by simp [hvr_req]
      have h_s_not_mr := ncw_impl_no_mr vr s (by subst hvr_req; exact h_vr_in_pi) (by subst hs; exact h_pi_has_s) h_vr_is_ncw h_s_is_mr

      subst hs
      absurd h_s_not_mr h_pi_has_s
      contradiction
    | ⟨some .r, false⟩ | ⟨some .wr, false⟩ | ⟨none, false⟩ =>
      subst hs
      simp
  | ⟨⟨.r, false, .Acq⟩, _⟩ => simp
-/
