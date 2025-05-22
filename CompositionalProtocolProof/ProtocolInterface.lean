import CompositionalProtocolProof.Requests
import Mathlib

abbrev ProtocolInterface := Set Request

abbrev CoherentSCRequest := {r : Request // r.consistency = .SC ∧ r.coherent = true}
abbrev CoherentSCWriteRequest := {r : Request // r.consistency = .SC ∧ r.coherent = true ∧ r.rw = .w}
abbrev CoherentSCReadRequest := {r : Request // r.consistency = .SC ∧ r.coherent = true ∧ r.rw = .r}

abbrev WeakRequest := {r : Request // r.consistency = .Weak}
abbrev ReleaseRequest := {r : Request // r.consistency = .Rel}
abbrev AcquireRequest := {r : Request // r.consistency = .Acq}

abbrev InterfaceMSI {csc : CoherentSCReadRequest} : ProtocolInterface := { csc.val }

def ProtocolInterfaceFamily {pi : ProtocolInterface}
-- {csc : CoherentSCRequest} {writecsc : CoherentSCWriteRequest} {readcsc : CoherentSCReadRequest}
: Prop :=
  {csc : CoherentSCRequest // csc.val ∈ pi} →
    ∃ writecsc : CoherentSCWriteRequest,
    ∃ readcsc : CoherentSCReadRequest,
    pi = { writecsc.val, readcsc.val}

def StoreMSI : Request := ⟨.w, true, .SC ⟩
def LoadMSI : Request := ⟨.r, true, .SC ⟩
def Acquire : Request := ⟨.r, false, .Acq ⟩
def MSI : Set Request := {StoreMSI, Acquire}

#check ProtocolInterfaceFamily

---------- Define if a Coherent Release Write is Lazy (LRCC) or Eager (RCCO) -------------

abbrev NonCoherentWeakWrite := {r : Request // r.rw = .w ∧ r.coherent = false ∧ r.consistency = .Weak}
abbrev CoherentWeakWrite := {r : Request // r.rw = .w ∧ r.coherent = true ∧ r.consistency = .Weak}
abbrev CoherentReleaseWrite := {r : Request // r.rw = .w ∧ r.coherent = true ∧ r.consistency = .Rel}

def LazyCoherentReleaseWrite {pi : ProtocolInterface} {crw : CoherentReleaseWrite} {ncww : NonCoherentWeakWrite} :
(crw.val ∈ pi) ∧ (ncww.val ∈ pi) → LazyEager
| _ => .lazy

def EagerCoherentReleaseWrite {pi : ProtocolInterface} {crw : CoherentReleaseWrite} {cww : CoherentWeakWrite} :
(crw.val ∈ pi) ∧ (cww.val ∈ pi) → LazyEager
| _ => .eager

def LazyOrEagerCoherentReleaseWrite {pi : ProtocolInterface} {crw : CoherentReleaseWrite} {ncww : NonCoherentWeakWrite} {cww : CoherentWeakWrite}:
(crw.val ∈ pi) → LazyEager
| crw_in_pi => ncww.val ∈ pi → LazyCoherentReleaseWrite (crw_in_pi ∧ ncww.val ∈ pi) ∨ cww.val ∈ pi → EagerCoherentReleaseWrite (crw_in_pi ∧ cww.val ∈ pi)
