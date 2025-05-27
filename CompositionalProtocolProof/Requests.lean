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
