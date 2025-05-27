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
abbrev ValidRequest := {r : Request // r.NoSCNonCoherent ∧ r.NoWriteAcquire ∧ r.NoReadRelease}

abbrev SCWrite : ValidRequest := ⟨⟨.w, true, .SC⟩, by simp⟩
abbrev SCRead : ValidRequest := ⟨⟨.r, true, .SC⟩, by simp⟩
abbrev RelWrite : ValidRequest := ⟨⟨.w, false, .Rel⟩, by simp⟩
abbrev CoherentRelWrite : ValidRequest := ⟨⟨.w, true, .Rel⟩, by simp⟩
abbrev AcqRead : ValidRequest := ⟨⟨.r, false, .Acq⟩, by simp⟩
abbrev NonCoherentWeakRead : ValidRequest := ⟨⟨.r, false, .Weak⟩, by simp⟩
abbrev NonCoherentWeakWrite : ValidRequest := ⟨⟨.w, false, .Weak⟩, by simp⟩
abbrev CoherentWeakWrite : ValidRequest := ⟨⟨.w, true, .Weak⟩, by simp⟩

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
/--
What is the state a request leaves a cache entry in.
-/
def ValidRequest.RequestState (vr : ValidRequest) : State → Option State
| s =>
  match h : vr.val with
  | ⟨_, true, _⟩ | ⟨.r, false, .Weak⟩ =>
    if some s ≤ vr.val.MRS then s
    else vr.val.MRS -- Must be a way to state this does not produce an Option Type?
  | ⟨.w, false, .Weak⟩ | ⟨.w, false, .Rel⟩ =>
    match hs : s with
    | ⟨some .wr, true⟩ => s
    | ⟨some .r, false⟩ =>
      -- by sorry -- Not allowed by Family of Protocols
      none
    | _ => Vd
  | ⟨.r, false, .Acq⟩ => Vc
  | ⟨.w, false, .SC ⟩ | ⟨.r, false, .SC ⟩ => by
    let hrestrictions := vr.prop
    let hno_nc_sc := hrestrictions.left
    exfalso
    apply hno_nc_sc
    unfold Request.SCNonCoherent
    simp[h]
  | ⟨.w, false, .Acq⟩ => by
    let hrestrictions := vr.prop
    let hno_nc_sc := hrestrictions.right.left
    exfalso
    apply hno_nc_sc
    unfold Request.WriteAcquire
    simp[h]
  | ⟨.r, false, .Rel⟩ => by
    let hrestrictions := vr.prop
    let hno_nc_sc := hrestrictions.right.right
    exfalso
    apply hno_nc_sc
    unfold Request.ReadRelease
    simp[h]

def ValidRequest.DowngradeState (vr : ValidRequest) : State → Option State
| s => match vr.val.coherent with
  | true =>
    if some s ≤ vr.val.MRS then I
    else vr.val.MRS
  | false =>
    if vr.val = NonCoherentWeakRead then
      if s = Vc then I
      else none
    else if vr.val = NonCoherentWeakWrite then
      if s = Vd then Vc
      else none
    else none

-- NOTE: move protocol interface here.
abbrev ContainsEitherSCOrRelOrCRel := λ vr : Set ValidRequest => (SCWrite ∈ vr ∨ RelWrite ∈ vr ∨ CoherentRelWrite ∈ vr)
abbrev ContainsEitherSCOrAcq := λ vr : Set ValidRequest => (SCRead ∈ vr ∨ AcqRead ∈ vr)
abbrev ProtocolInterface := {vr : Set ValidRequest //
  ContainsEitherSCOrRelOrCRel vr ∧ ContainsEitherSCOrAcq vr ∧
  (SCWrite ∈ vr → SCRead ∈ vr) ∧ ((RelWrite ∈ vr ∨ CoherentRelWrite ∈ vr) → AcqRead ∈ vr) ∧
  (AcqRead ∈ vr → NonCoherentWeakRead ∈ vr) ∧ (RelWrite ∈ vr → NonCoherentWeakWrite ∈ vr) ∧
  (CoherentRelWrite ∈ vr → (CoherentWeakWrite ∈ vr ∨ NonCoherentWeakWrite ∈ vr))}

-- Want to find states a protocol interface has.
abbrev Request.toState : Request → State
| ⟨rw, coherence, _⟩ => ⟨rw.toPerms, coherence⟩

abbrev ValidRequest.toState : ValidRequest → State
| ⟨req, _⟩ => req.toState

-- Allowable state -- want to say all the states a valid protocol inerface (allowed by ProtocolInterface) allows
abbrev ProtocolStates := (p : ProtocolInterface) → {s : Set State // ∀ r ∈ p.val, r.toState ∈ s}
