import CompositionalProtocolProof.Common
import CompositionalProtocolProof.States

inductive ReadWrite
| r : ReadWrite
| w : ReadWrite

-- abbrev Coherent, from Common.

inductive Consistency
| SC : Consistency
| Rel : Consistency
| Acq : Consistency
| Weak : Consistency

structure Request where
  rw          : ReadWrite
  coherent    : Coherent
  consistency : Consistency

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

-- abbrev CoherentRead : Request := ⟨.r, true, ·⟩

/- Want to specify that request is a request allowed by the family of interfaces -/
def Request.RequestState : Request → State → State
| r, s =>
  match r with
  | ⟨.r, true, _⟩ | ⟨.w, true, _⟩ | ⟨.r, false, .Weak⟩ =>
    if s ≥ r.MRS then s
    else r.MRS
