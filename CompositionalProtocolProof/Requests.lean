import CompositionalProtocolProof.Common
import CompositionalProtocolProof.States

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

/-- Definition 2.12 Minimum Required State of a request.
How to specify a request that's allowed by the Family Interface?
-/
def Request.MRS : Request → Option State
| r => match r.coherent with
  | true => some ⟨r.rw.toPerms, r.coherent⟩
  | false => match r.consistency with
    | .Weak => some Vc
    | .Rel | .Acq => none
    | .SC => none -- Non-Coherent SC request not allowed by interface family

def Request.isCoherent (r : Request) : Prop := r.coherent = true
def Request.nonCoherent (r : Request) : Prop := r.coherent = false

-- Disallowed Requests
abbrev Request.SCNonCoherent := λ r : Request => r.consistency = .SC ∧ r.coherent = false
abbrev Request.WriteAcquire := λ r : Request => r.rw = .w ∧ r.consistency = .Acq
abbrev Request.ReadRelease := λ r : Request => r.rw = .r ∧ r.consistency = .Rel
-- Valid Request does not contain disallowed requests.
abbrev Request.NoSCNonCoherent := λ r : Request => ¬r.SCNonCoherent
abbrev Request.NoWriteAcquire := λ r : Request => ¬r.WriteAcquire
abbrev Request.NoReadRelease := λ r : Request => ¬r.ReadRelease

structure Request.IsValid (r : Request) where
  non_coherent : r.NoSCNonCoherent := by simp
  no_write_acq : r.NoWriteAcquire := by simp
  no_read_rel : r.NoReadRelease := by simp

abbrev ValidRequest := {r : Request // Request.IsValid r}

abbrev SCWrite : ValidRequest := ⟨⟨.w, true, .SC⟩, {}⟩
abbrev SCRead : ValidRequest := ⟨⟨.r, true, .SC⟩, {}⟩
abbrev RelWrite : ValidRequest := ⟨⟨.w, false, .Rel⟩, {}⟩
abbrev CoherentRelWrite : ValidRequest := ⟨⟨.w, true, .Rel⟩, {}⟩
abbrev AcqRead : ValidRequest := ⟨⟨.r, false, .Acq⟩, {}⟩
abbrev NonCoherentWeakRead : ValidRequest := ⟨⟨.r, false, .Weak⟩, {}⟩
abbrev NonCoherentWeakWrite : ValidRequest := ⟨⟨.w, false, .Weak⟩, {}⟩
abbrev CoherentWeakWrite : ValidRequest := ⟨⟨.w, true, .Weak⟩, {}⟩

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

structure FollowsProtocolInterface (vr : Set ValidRequest) where
  sc_rel_crel : ContainsEitherSCOrRelOrCRel vr
  sc_or_acq : ContainsEitherSCOrAcq vr
  write_read : SCWrite ∈ vr → SCRead ∈ vr
  rel_write_acq : (RelWrite ∈ vr ∨ CoherentRelWrite ∈ vr) → AcqRead ∈ vr
  acq_weak : AcqRead ∈ vr → NonCoherentWeakRead ∈ vr
  real_weak : RelWrite ∈ vr → NonCoherentWeakWrite ∈ vr
  rel_weak_coherent : CoherentRelWrite ∈ vr → (CoherentWeakWrite ∈ vr ∨ NonCoherentWeakWrite ∈ vr)
  /- no mixing SC and Weak -/
  write_no_weak_write : SCWrite ∈ vr → NonCoherentWeakWrite ∉ vr
  write_no_weak_read : SCWrite ∈ vr → NonCoherentWeakRead ∉ vr
  weak_write_no_sc_write : NonCoherentWeakWrite ∈ vr → SCWrite ∉ vr
  weak_read_no_sc_write : NonCoherentWeakRead ∈ vr → SCRead ∉ vr
  rel_no_sc_write : RelWrite ∈ vr → SCRead ∉ vr

def ProtocolInterface := {vr : Set ValidRequest // FollowsProtocolInterface vr}
  -- Want to find states a protocol interface has.
def Request.toState : Request → State
| ⟨rw, coherent, _⟩ => ⟨rw.toPerms, coherent⟩

def ValidRequest.toState : ValidRequest → State
| ⟨req, _⟩ => req.toState

def ProtocolInterface.ProtocolStates : ProtocolInterface → Set State
| pi => pi.val.image (·.toState)

def AllowedState (pi : ProtocolInterface) := {s : State // s ∈ pi.ProtocolStates}

structure ValidProtocolRequest' (pi : ProtocolInterface) (vr : ValidRequest) : Prop where
  vrInPI : vr ∈ pi.val

lemma mr_in_pi_impl_sc_read_in_pi {pi : ProtocolInterface} (s : AllowedState pi) (hs_mr : s.val = ⟨some .r, true⟩) : SCRead ∈ pi.val := by
  sorry

/--
What is the state a request leaves a cache entry in.
-/
def ValidRequest.RequestState {pi : ProtocolInterface} (vr : ValidRequest) (s : AllowedState pi) (vr_in_pi : vr ∈ pi.val) : Option State :=
-- | s =>
  match h : vr.val with
  | ⟨_, true, _⟩ | ⟨.r, false, .Weak⟩ =>
    if some s.val ≤ vr.val.MRS then s.val
    else vr.val.MRS -- Must be a way to state this does not produce an Option Type?
  | ⟨.w, false, .Weak⟩ | ⟨.w, false, .Rel⟩ =>
    match hs : s.val with
    | ⟨some .wr, true⟩ => s.val
    | ⟨some .r,  true⟩ =>
      none
      /-
      by
      /- Show a contradiction; MR (read, coherent) means coherent read request is in Protocol Interface.
      But if a noncoherent write (vr) is in pi, then a coherent read can't also be in the protocol interface! -/
      unfold ProtocolInterface at pi
      have h_s_from_pi := s.prop
      have h_pi_no_sc_read_and_weak := pi.prop.rel_no_sc_write
      have h_pi_has_sc_read : SCRead ∈ pi.val := by
        -- `s` is MR, and can only get MR state ∈ pi.val if SCRead ∈ pi.val. -- Hard to show this?
        sorry
      sorry
      -/
    | _ => Vd
  | ⟨.r, false, .Acq⟩ => Vc
  | ⟨.w, false, .SC ⟩ | ⟨.r, false, .SC ⟩ => absurd vr.prop.non_coherent (by simp [h])
  | ⟨.w, false, .Acq⟩ => absurd vr.prop.no_write_acq (by simp [h])
  | ⟨.r, false, .Rel⟩ => absurd vr.prop.no_read_rel (by simp [h])

def ValidRequest.DowngradeState (vr : ValidRequest) : State → Option State
| s => match vr.val.coherent with
  | true =>
    if s ≤ vr.val.MRS then I
    else vr.val.MRS
  | false =>
    if vr.val = NonCoherentWeakRead then
      if s = Vc then I
      else none
    else if vr.val = NonCoherentWeakWrite then
      if s = Vd then Vc
      else none
    else none
