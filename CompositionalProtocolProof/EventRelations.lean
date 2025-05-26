import CompositionalProtocolProof.Events
import CompositionalProtocolProof.Requests

def Event.Encapsulates (e₁ e₂ : Event) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd

def Event.Ordered (e₁ e₂ : Event) : Prop := e₁.oEnd < e₂.oStart
def CacheEvent.Ordered (e₁ e₂ : CacheEvent) : Prop := e₁.oEnd < e₂.oStart
def DirectoryEvent.Ordered (e₁ e₂ : DirectoryEvent) : Prop := e₁.oEnd < e₂.oStart

def Event.ProgramOrdered (e₁ e₂ : CacheEvent) : Prop := e₁.Ordered e₂ ∧ e₁.rid = e₂.rid

-- Axiom 1
def OrderedDirectoryEvents (de₁ de₂ : DirectoryEvent) : Prop := de₁.a = de₂.a → de₁.Ordered de₂ ∨ de₂.Ordered de₁

-- def CacheEventOrdered (e₁ e₂ : CacheEvent) : Prop :=
--   if e₁.requestEvent ∧ e₂.requestEvent ∧ e₁.sameAddress e₂

-- def CoherentRead (r : Request) : Prop := r.coherent
-- abbrev CoherentRead := {r : Request // r.coherent = true ∧ r.rw = .r}
def CoherentRead : Request := ⟨ .r, true, .SC ⟩
def CoherentWrite : Request := ⟨ .w, true, .SC ⟩

-- NOTE: this requires State LT (<) relation
/-
def CacheEvent.SucceedingState : CacheEvent → State → State
| e, s => match e.r.coherent with
  | true =>
    if  then
  | false =>
    MR
-/
