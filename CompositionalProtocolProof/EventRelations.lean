import CompositionalProtocolProof.Events
import CompositionalProtocolProof.Requests

def Event.Encapsulates (e₁ e₂ : Event) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd
def CacheEvent.Encapsulates (e₁ e₂ : CacheEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd
def DirectoryEvent.Encapsulates (e₁ e₂ : DirectoryEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd

def Event.Ordered (e₁ e₂ : Event) : Prop := e₁.oEnd < e₂.oStart
def CacheEvent.Ordered (e₁ e₂ : CacheEvent) : Prop := e₁.oEnd < e₂.oStart
def DirectoryEvent.Ordered (e₁ e₂ : DirectoryEvent) : Prop := e₁.oEnd < e₂.oStart

def Event.ProgramOrdered (e₁ e₂ : CacheEvent) : Prop := e₁.Ordered e₂ ∧ e₁.rid = e₂.rid

/-- Axiom 1
Events at a Directory address are ordered.
-/
abbrev OrderedDirectoryEvents (de₁ de₂ : DirectoryEvent) : Prop := de₁.a = de₂.a → de₁.Ordered de₂ ∨ de₂.Ordered de₁

/-- Definition 2.18. Directory Event ID.
Ordered Directory Events.
-/
abbrev MonotonicDirectoryEventIds (de₁ de₂ : DirectoryEvent) : Prop := de₁.Ordered de₂ → (de₁.deid + 1) = de₂.deid

abbrev CacheEvent.Local (e : CacheEvent) : Prop := e.cid = e.rid

abbrev CacheEvent.Weak (e : CacheEvent) : Prop := (e.Local ∧ e.r.val.coherent = false ∧ e.r.val.consistency = .Weak)
abbrev CacheEvent.WithCoherentPermissions (e : CacheEvent) (s : State) : Prop := (e.Local ∧ e.r.val.coherent = true ∧ e.r.val.MRS ≤ s)
abbrev CacheEvent.Downgrade (e : CacheEvent) : Prop := e.d = true
abbrev CacheEvent.NoEncapSameAddressDowngrade (e : CacheEvent) (s : State) : Prop := (e.Weak ∨ e.WithCoherentPermissions s ∨ e.Downgrade)

abbrev CacheEvent.External (e : CacheEvent) : Prop := ¬e.Local
abbrev CacheEvent.WithoutCoherentPermissions (e : CacheEvent) (s : State) : Prop := (e.Local ∧ e.r.val.coherent = true ∧ s < e.r.val.MRS)

/-- Axiom 2
Events at the same address at a cache are ordered, or may encapsulate an external event to the same address.
-/
abbrev OrderedCacheEvents (e₁ e₂ : CacheEvent) (s : State) : Prop :=
  e₁.cid = e₂.cid ∧ e₁.a = e₂.a ∧
  if e₁.NoEncapSameAddressDowngrade s ∧ e₂.NoEncapSameAddressDowngrade s then (e₁.Ordered e₂ ∨ e₂.Ordered e₁)
  else if e₁.WithoutCoherentPermissions s ∧ e₂.External then (e₁.Ordered e₂ ∨ e₂.Ordered e₁ ∨ e₁.Encapsulates e₂)
  else if e₁.External ∧ e₂.WithoutCoherentPermissions s then (e₁.Ordered e₂ ∨ e₂.Ordered e₁ ∨ e₂.Encapsulates e₁)
  else (e₁.Ordered e₂ ∨ e₂.Ordered e₁)

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
