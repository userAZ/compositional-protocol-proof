import CompositionalProtocolProof.Events
import CompositionalProtocolProof.Requests

def Event.Encapsulates (e₁ e₂ : Event) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd
def CacheEvent.Encapsulates (e₁ e₂ : CacheEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd
def DirectoryEvent.Encapsulates (e₁ e₂ : DirectoryEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₁.oEnd < e₂.oEnd

def Event.Ordered (e₁ e₂ : Event) : Prop := e₁.oEnd < e₂.oStart
def CacheEvent.Ordered (e₁ e₂ : CacheEvent) : Prop := e₁.oEnd < e₂.oStart
def DirectoryEvent.Ordered (e₁ e₂ : DirectoryEvent) : Prop := e₁.oEnd < e₂.oStart

instance Event.Encapsulates.instDecidableEncap (e₁ e₂ : Event) : Decidable (e₁.Encapsulates e₂) :=
  inferInstanceAs (Decidable (e₁.o.Encapsulates e₂.o))

instance Event.Ordered.instLT : LT Event := {lt := Event.Ordered}

instance Event.Ordered.instDecidableLT (e₁ e₂ : Event) : Decidable (e₁ < e₂) :=
  inferInstanceAs (Decidable (e₁.o < e₂.o))

lemma Event.ordered_trans {e₁ e₂ e₃ : Event} : e₁ < e₂ → e₂ < e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold Ordered.instLT
  simp
  unfold Event.Ordered;
  intro he₁_lt_e₂ he₂_lt_e₃
  have he₂_well_formed := e₂.o.wellFormed
  calc
    e₁.o.oEnd < e₂.o.oStart := he₁_lt_e₂
    _ < e₂.oEnd := he₂_well_formed
    _ < e₃.o.oStart := he₂_lt_e₃

instance Event.instTransOrderOrder : Trans Event.Ordered Event.Ordered Event.Ordered := {trans := Event.ordered_trans}

lemma Event.order_encap_trans {e₁ e₂ e₃ : Event} : e₁ < e₂ → e₂.Encapsulates e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold Ordered.instLT
  simp
  unfold Event.Ordered;
  unfold Encapsulates
  intro he₁_lt_e₂ he₂_encap_e₃
  calc
    e₁.o.oEnd < e₂.o.oStart := he₁_lt_e₂
    _ < e₃.oStart := he₂_encap_e₃.left

instance Event.instTransOrderEncap : Trans Event.Ordered Event.Encapsulates Event.Ordered := {trans := Event.order_encap_trans}

lemma Event.encap_order_trans {e₁ e₂ e₃ : Event} : e₁.Encapsulates e₂ → e₂ < e₃ → e₂ < e₃ := by
  simp -- wow. why doesn't this work in the lemmas above?

abbrev CacheEvent.SameRequester (e₁ e₂ : CacheEvent) : Prop := e₁.rid = e₂.rid
-- abbrev CacheEvent.SameCache (e₁ e₂ : CacheEvent) : Prop := e₁.cid = e₂.cid

structure CacheEvent.ProgramOrdered (e₁ e₂ : CacheEvent) where
  ordered : e₁.Ordered e₂ := by simp
  same_requester : e₁.SameRequester e₂ := by simp

def Event.ProgramOrdered (e₁ e₂ : Event) : Prop :=
  match e₁ with
  | .cacheEvent ce₁ =>
    match e₂ with
    | .cacheEvent ce₂ =>
      ce₁.ProgramOrdered ce₂
    | .directoryEvent _ => true -- nothing happens
  | .directoryEvent _ => true -- nothing happens

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

-- NOTE: May need to use a different Prop other than External below. May need explicit field for Grant
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
def CacheEvent.SucceedingState : CacheEvent → State → Option State
| e, s => match e.d with
  | false => e.r.RequestState s
  | true => e.r.DowngradeState s

def DirectoryEvent.SucceedingState : /- ProtocolInterface → -/ DirectoryEvent → DirectoryState → Option DirectoryState
| de, ds => match de.d with
  | false => match de.r.val with
    | ⟨.w, true, _⟩ => -- Coherent-Write
      DirectoryState.SW ⟨SW, by simp⟩ de.eReq.rid
    | ⟨.r, true, _⟩ => -- Coherent-Read
      DirectoryState.MR ⟨MR, by simp⟩ (ds.CurrentSharers ∪ {de.eReq.rid})
    | ⟨.w, false, _⟩ => -- Non-Coherent-Write
      -- MR forbidden
      DirectoryState.Vd ⟨Vd, by simp⟩
    | ⟨.r, false, _⟩ => -- Non-Coherent-Read
      match ds with
      | .Vd vd => DirectoryState.Vd vd
      -- MR forbidden
      | _ => DirectoryState.Vc ⟨Vc, by simp⟩
  | true => match de.r.val with
    | ⟨.w, true, _⟩ => -- Coherent-Write Downgrade
      match ds with
      | .SW _ owner => -- Determined by the Protocol
        if de.eReq.rid == owner then DirectoryState.I ⟨I, by simp⟩
        else ds
      | .MR mr sharers =>  DirectoryState.MR mr (sharers \ {de.eReq.rid})
      | .Vd _ | .Vc _ | .I _ => DirectoryState.I ⟨I, by simp⟩
    | ⟨.r, true, _⟩ => -- Coherent-Read Downgrade
      match ds with
      | .SW _ _ | .I _ => ds
      | .MR mr sharers => DirectoryState.MR mr (sharers \ {de.eReq.rid})
      | .Vd _ | .Vc _ => -- Not allowed
        -- sorry
        none -- NOTE: Can avoid `Option DirectoryState` if I choose something reasonable to return (Same state (Vd or Vc)).
    | ⟨.w, false, _⟩ => DirectoryState.Vc ⟨Vc, by simp⟩ -- Non-Coherent-Write downgrade
    | ⟨.r, false, _⟩ => DirectoryState.I ⟨I, by simp⟩ -- Non-Coherent-Read downgrade

/-
 -- Try alternate approach to using Set of EventRelation as a Context Γ
 -- Is there any benefit to using EventRelation as a Context Γ?
inductive EventRelation
| encapsulates (e₁ e₂ : Event) (e₁_encap_e₂ : e₁.Encapsulates e₂) : EventRelation
| ordered (e₁ e₂ : Event) (e₁_ordered_e₂ : e₁.Ordered e₂) : EventRelation
| programOrdered (e₁ e₂ : Event) (e₁_po_e₂ : e₁.ProgramOrdered e₂) : EventRelation
/- take a field accessor function, and constraint on the field. -/
| fieldMatch {α : Type} (e₁ : Event) (f : Event → α) (val : α) (e₁_field_match : f e₁ = val) : EventRelation
/- a field accessor fn. check if fields of e₁ and e₂ are equal -/
| noFieldMatch {α : Type} (e₁ : Event) (f : Event → α) (val : α) (e₁_no_field_match : f e₁ ≠ val) : EventRelation
/- a field accessor fn. check if fields of e₁ and e₂ are equal -/
| matchingFields {α : Type} (e₁ e₂ : Event) (f : Event → α) (e₁_e₂_field_match : f e₁ = f e₂) : EventRelation
/- a field accessor fn. check if fields of e₁ and e₂ are equal -/
| noMatchingFields {α : Type} (e₁ e₂ : Event) (f : Event → α) (e₁_e₂_no_field_match : f e₁ ≠ f e₂) : EventRelation
-- deriving DecidableEq
-/
