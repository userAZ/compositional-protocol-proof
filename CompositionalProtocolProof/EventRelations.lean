import CompositionalProtocolProof.Events
import CompositionalProtocolProof.Requests

def Event.Encapsulates (e₁ e₂ : Event) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd
def CacheEvent.Encapsulates (e₁ e₂ : CacheEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd
def DirectoryEvent.Encapsulates (e₁ e₂ : DirectoryEvent) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd

def Event.OrderedBefore (e₁ e₂ : Event) : Prop := e₁.oEnd < e₂.oStart
def CacheEvent.OrderedBefore (e₁ e₂ : CacheEvent) : Prop := e₁.oEnd < e₂.oStart
def DirectoryEvent.OrderedBefore (e₁ e₂ : DirectoryEvent) : Prop := e₁.oEnd < e₂.oStart

def Event.fromDirectoryEvent (de : DirectoryEvent) (e : Event) : Prop :=
  match e with
  | .directoryEvent de' => de = de'
  | .cacheEvent _ => false

lemma DirectoryEvent.ordered_events {de₁ de₂ : DirectoryEvent} {e₁ e₂ : Event}
  (he₁_is_de₁ : e₁.fromDirectoryEvent de₁) (he₂_is_de₂ : e₂.fromDirectoryEvent de₂) : de₁.OrderedBefore de₂ → e₁.OrderedBefore e₂ := by
  unfold DirectoryEvent.OrderedBefore; unfold Event.OrderedBefore
  -- unfold DirectoryEvent.oEnd; unfold DirectoryEvent.oStart
  unfold Event.oEnd; unfold Event.oStart
  match he₁ : e₁, he₂ : e₂ with
  | .directoryEvent de₁', .directoryEvent de₂' =>
    subst he₁_is_de₁ he₂_is_de₂
    intro h_de₁_lt_de₂
    simp [Event.o]
    exact h_de₁_lt_de₂
  | .directoryEvent _, .cacheEvent _ => contradiction
  | .cacheEvent _, .directoryEvent _ => contradiction
  | .cacheEvent _, .cacheEvent _ => contradiction

def Event.Predecessor : Event → Event → Prop
| e_pred, e_succ => e_pred.OrderedBefore e_succ

def Event.Successor : Event → Event → Prop
| e_pred, e_succ => e_pred.Predecessor e_succ

instance Event.Encapsulates.instDecidableEncap (e₁ e₂ : Event) : Decidable (e₁.Encapsulates e₂) :=
  inferInstanceAs (Decidable (e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd))

instance Event.OrderedBefore.instLT : LT Event := {lt := Event.OrderedBefore}

instance Event.OrderedBefore.instDecidableLT (e₁ e₂ : Event) : Decidable (e₁ < e₂) :=
  inferInstanceAs (Decidable (e₁.oEnd < e₂.oStart))

lemma Event.ordered_trans {e₁ e₂ e₃ : Event} : e₁ < e₂ → e₂ < e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold OrderedBefore.instLT
  simp
  unfold Event.OrderedBefore;
  intro he₁_lt_e₂ he₂_lt_e₃
  have he₂_well_formed := e₂.oWellFormed
  calc
    e₁.oEnd < e₂.oStart := he₁_lt_e₂
    _ < e₂.oEnd := he₂_well_formed
    _ < e₃.oStart := he₂_lt_e₃

instance Event.instTransOrderOrder : Trans Event.OrderedBefore Event.OrderedBefore Event.OrderedBefore := {trans := Event.ordered_trans}

lemma Event.order_encap_trans {e₁ e₂ e₃ : Event} : e₁ < e₂ → e₂.Encapsulates e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold OrderedBefore.instLT
  simp
  unfold Event.OrderedBefore;
  unfold Encapsulates
  intro he₁_lt_e₂ he₂_encap_e₃
  calc
    e₁.oEnd < e₂.oStart := he₁_lt_e₂
    _ < e₃.oStart := he₂_encap_e₃.left

instance Event.instTransOrderEncap : Trans Event.OrderedBefore Event.Encapsulates Event.OrderedBefore := {trans := Event.order_encap_trans}

abbrev Event.EncapsulatedBy (e₁ e₂ : Event) : Prop := e₂.Encapsulates e₁

lemma Event.encap_by_order_trans {e₁ e₂ e₃ : Event} : e₁.EncapsulatedBy e₂ → e₂ < e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold OrderedBefore.instLT
  simp
  -- unfold BottomEncapsulates;
  unfold EncapsulatedBy; unfold Encapsulates
  unfold OrderedBefore
  simp
  intro he₂_lt_e₁_start he₂_lt_e₁_end he₂_lt_e₃
  calc
    e₁.oEnd < e₂.oEnd := he₂_lt_e₁_end
    _ < e₃.oStart := he₂_lt_e₃

/- The shape of Trans's definition doesn't match to Event.encap_order_trans. Need to massage def. -/
instance Event.instTransEncapByOrder : Trans Event.EncapsulatedBy Event.OrderedBefore Event.OrderedBefore := {trans := Event.encap_by_order_trans}

structure Event.OrderedBetween (e e_pred e_succ : Event) where
  pred : e_pred.OrderedBefore e := by simp
  succ : e.OrderedBefore e_succ := by simp

def CacheEvent.SameRequester (e₁ e₂ : CacheEvent) : Prop := e₁.rid = e₂.rid
def CacheEvent.SameCache (e₁ e₂ : CacheEvent) : Prop := e₁.cid = e₂.cid
def CacheEvent.SameAddress (e₁ e₂ : CacheEvent) : Prop := e₁.a = e₂.a

def Event.CacheRelation (e₁ e₂ : Event) : (CacheEvent → CacheEvent → Prop) → Prop
| p => match e₁ with
  | .cacheEvent ce₁ =>
    match e₂ with
    | .cacheEvent ce₂ => p ce₁ ce₂
    | .directoryEvent _ => false -- nothing happens
  | .directoryEvent _ => false -- nothing happens

def Event.SameStructureRelation (e₁ e₂ : Event) :
  (CacheEvent → CacheEvent → Prop) → (DirectoryEvent → DirectoryEvent → Prop) → Prop
| cp, dp => match e₁ with
  | .cacheEvent ce₁ =>
    match e₂ with
    | .cacheEvent ce₂ => cp ce₁ ce₂
    | .directoryEvent _ => false -- nothing happens
  | .directoryEvent de₁ =>
    match e₂ with
    | .cacheEvent _ => false -- nothing happens
    | .directoryEvent de₂ => dp de₁ de₂

-- abbrev CacheEvent.SameRequester (e₁ e₂ : CacheEvent) : Prop := e₁.rid = e₂.rid
def DirectoryEvent.SameStructure (_ _ : DirectoryEvent) : Prop := true
def DirectoryEvent.SameAddress (e₁ e₂ : DirectoryEvent) : Prop := e₁.a = e₂.a

def Event.CacheSameRequester (e₁ e₂ : Event) : Prop := e₁.CacheRelation e₂ (·.SameRequester ·)
def Event.SameStructure (e₁ e₂ : Event) : Prop := e₁.SameStructureRelation e₂ (·.SameCache ·) (·.SameStructure ·)
def Event.SameAddress (e₁ e₂ : Event) : Prop := e₁.SameStructureRelation e₂ (·.SameAddress ·) (·.SameAddress ·)

lemma Event.same_address_reflexive {e₁ e₂ e₃ : Event} : e₁.SameAddress e₃ → e₂.SameAddress e₃ → e₁.SameAddress e₂ := by
  unfold SameAddress
  unfold CacheEvent.SameAddress; unfold DirectoryEvent.SameAddress
  unfold SameStructureRelation
  simp
  intro he₁_sa_e₃ he₂_sa_e₃
  match he₁ : e₁, he₂ : e₂, he₃ : e₃ with
  | .cacheEvent ce₁, .cacheEvent ce₂, .cacheEvent ce₃ => simp_all
  | .directoryEvent de₁, .directoryEvent de₂, .directoryEvent de₃ => simp_all
  | .cacheEvent ce₁, .cacheEvent ce₂, .directoryEvent de => contradiction
  | .cacheEvent ce₁, .directoryEvent de, .cacheEvent ce₃ => contradiction
  | .directoryEvent de, .cacheEvent ce₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .directoryEvent de₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .cacheEvent ce, .directoryEvent de₃ => contradiction
  | .cacheEvent ce, .directoryEvent de₂, .directoryEvent de₃ => contradiction

lemma Event.same_address_reflexive' {e₁ e₂ e₃ : Event} : e₁.SameAddress e₂ → e₁.SameAddress e₃ → e₂.SameAddress e₃ := by
  unfold SameAddress
  unfold CacheEvent.SameAddress; unfold DirectoryEvent.SameAddress
  unfold SameStructureRelation
  simp
  intro he₁_sa_e₂ he₁_sa_e₃
  match he₁ : e₁, he₂ : e₂, he₃ : e₃ with
  | .cacheEvent ce₁, .cacheEvent ce₂, .cacheEvent ce₃ => simp_all
  | .directoryEvent de₁, .directoryEvent de₂, .directoryEvent de₃ => simp_all
  | .cacheEvent ce₁, .cacheEvent ce₂, .directoryEvent de => contradiction
  | .cacheEvent ce₁, .directoryEvent de, .cacheEvent ce₃ => contradiction
  | .directoryEvent de, .cacheEvent ce₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .directoryEvent de₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .cacheEvent ce, .directoryEvent de₃ => contradiction
  | .cacheEvent ce, .directoryEvent de₂, .directoryEvent de₃ => contradiction

lemma Event.same_structure_reflexive {e₁ e₂ e₃ : Event} : e₁.SameStructure e₃ → e₂.SameStructure e₃ → e₁.SameStructure e₂ := by
  unfold SameStructure
  unfold CacheEvent.SameCache; unfold DirectoryEvent.SameStructure
  unfold SameStructureRelation
  simp
  intro he₁_ss_e₃ he₂_ss_e₃
  match he₁ : e₁, he₂ : e₂, he₃ : e₃ with
  | .cacheEvent ce₁, .cacheEvent ce₂, .cacheEvent ce₃ => simp_all
  | .directoryEvent de₁, .directoryEvent de₂, .directoryEvent de₃ => simp_all
  | .cacheEvent ce₁, .cacheEvent ce₂, .directoryEvent de => contradiction
  | .cacheEvent ce₁, .directoryEvent de, .cacheEvent ce₃ => contradiction
  | .directoryEvent de, .cacheEvent ce₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .directoryEvent de₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .cacheEvent ce, .directoryEvent de₃ => contradiction
  | .cacheEvent ce, .directoryEvent de₂, .directoryEvent de₃ => contradiction

lemma Event.same_structure_reflexive' {e₁ e₂ e₃ : Event} : e₁.SameStructure e₂ → e₁.SameStructure e₃ → e₂.SameStructure e₃ := by
  unfold SameStructure
  unfold CacheEvent.SameCache; unfold DirectoryEvent.SameStructure
  unfold SameStructureRelation
  simp
  intro he₁_ss_e₂ he₁_ss_e₃
  match he₁ : e₁, he₂ : e₂, he₃ : e₃ with
  | .cacheEvent ce₁, .cacheEvent ce₂, .cacheEvent ce₃ => simp_all
  | .directoryEvent de₁, .directoryEvent de₂, .directoryEvent de₃ => simp_all
  | .cacheEvent ce₁, .cacheEvent ce₂, .directoryEvent de => contradiction
  | .cacheEvent ce₁, .directoryEvent de, .cacheEvent ce₃ => contradiction
  | .directoryEvent de, .cacheEvent ce₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .directoryEvent de₂, .cacheEvent ce => contradiction
  | .directoryEvent de₁, .cacheEvent ce, .directoryEvent de₃ => contradiction
  | .cacheEvent ce, .directoryEvent de₂, .directoryEvent de₃ => contradiction

structure CacheEvent.ProgramOrdered (e₁ e₂ : CacheEvent) where
  ordered : e₁.OrderedBefore e₂ := by simp
  same_requester : e₁.SameRequester e₂ := by simp

def Event.ProgramOrdered (e₁ e₂ : Event) : Prop := e₁.CacheRelation e₂ (·.ProgramOrdered ·)

/-- Axiom 1
Events at a Directory address are ordered.
-/
def OrderedDirectoryEvents (de₁ de₂ : DirectoryEvent) : Prop := de₁.a = de₂.a → de₁.OrderedBefore de₂ ∨ de₂.OrderedBefore de₁
/-
def Event.isDirectoryEvent : Event → Prop
| .directoryEvent _ => true
| .cacheEvent _ => false
def OrderedDirectoryEvents' (e₁ e₂ : Event) : Prop :=
  e₁.isDirectoryEvent → e₂.isDirectoryEvent → e₁.SameAddress e₂ → e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁
-/

/-- Definition 2.18. Directory Event ID.
Ordered Directory Events.
-/
def MonotonicDirectoryEventIds (de₁ de₂ : DirectoryEvent) : Prop := de₁.OrderedBefore de₂ → (de₁.deid + 1) = de₂.deid

/- Lean can't synthesize decidability in OrderedCacheEvents if these aren't `abbrev`s -/
abbrev CacheEvent.Local (e : CacheEvent) : Prop := e.cid = e.rid
abbrev CacheEvent.NonCoherent (e : CacheEvent) : Prop := e.r.val.coherent = false
abbrev CacheEvent.WeakConsistency (e : CacheEvent) : Prop := e.r.val.consistency = .Weak

abbrev CacheEvent.Weak (e : CacheEvent) : Prop := e.Local ∧ e.NonCoherent ∧ e.WeakConsistency

abbrev CacheEvent.RequestHasPermissions (e : CacheEvent) (s : State) : Prop := e.r.MRS ≤ s
abbrev CacheEvent.Coherent (e : CacheEvent) : Prop := e.r.val.coherent = true

abbrev CacheEvent.WithCoherentPermissions (e : CacheEvent) (s : State) : Prop := e.Local ∧ e.Coherent ∧ e.RequestHasPermissions s

abbrev CacheEvent.Downgrade (e : CacheEvent) : Prop := e.d = true
abbrev CacheEvent.NoEncapSameAddressDowngrade (e : CacheEvent) (s : State) : Prop := e.Weak ∨ e.WithCoherentPermissions s ∨ e.Downgrade

abbrev CacheEvent.Grant (e : CacheEvent) : Prop := e.deid? ≠ none
abbrev CacheEvent.External (e : CacheEvent) : Prop := ¬e.Local ∨ e.Grant
abbrev CacheEvent.NoRequestPermissions (e : CacheEvent) (s : State) : Prop := s < e.r.MRS

abbrev CacheEvent.WithoutCoherentPermissions (e : CacheEvent) (s : State) : Prop := e.Local ∧ e.Coherent ∧ e.NoRequestPermissions s

/-- Axiom 2
Events at the same address at a cache are ordered, or may encapsulate an external event to the same address.
-/
def OrderedCacheEvents (e₁ e₂ : CacheEvent) (s₁ s₂ : State) : Prop :=
  e₁.cid = e₂.cid → e₁.a = e₂.a →
  if e₁.NoEncapSameAddressDowngrade s₁ ∧ e₂.NoEncapSameAddressDowngrade s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)
  else if e₁.WithoutCoherentPermissions s₁ ∧ e₂.External then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₁.Encapsulates e₂)
  else if e₁.External ∧ e₂.WithoutCoherentPermissions s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₂.Encapsulates e₁)
  else (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)

/- -- Lean can't synthesize decidablability in OrderedCacheEvents'?
def Event.isCacheEvent : Event → Prop
| .directoryEvent _ => false
| .cacheEvent _ => true

def Event.CacheConstraint (e : Event) (constraint : CacheEvent → Prop) : Prop := match e with
  | .cacheEvent ce => constraint ce
  | .directoryEvent _ => false

abbrev Event.CacheLocal (e : Event) : Prop := e.CacheConstraint (·.Local)

abbrev Event.CacheNonCoherent (e : Event) : Prop := e.CacheConstraint (·.NonCoherent)
abbrev Event.CacheWeakConsistency (e : Event) : Prop := e.CacheConstraint (·.WeakConsistency)

abbrev Event.CacheWeak (e : Event) : Prop := e.CacheLocal ∧ e.CacheNonCoherent ∧ e.CacheWeakConsistency

abbrev Event.CacheRequestHasPermissions (e : Event) (s : State) : Prop := e.CacheConstraint (·.RequestHasPermissions s)

abbrev Event.CacheCoherent (e : Event) : Prop := e.CacheConstraint (·.Coherent)

abbrev Event.CacheWithCoherentPermissions (e : Event) (s : State) : Prop := e.CacheLocal ∧ e.CacheCoherent ∧ e.CacheRequestHasPermissions s

abbrev Event.CacheDowngrade (e : Event) : Prop := e.CacheConstraint (·.Downgrade)
abbrev Event.CacheNoEncapSameAddressDowngrade (e : Event) (s : State) : Prop := (e.CacheWeak ∨ e.CacheWithCoherentPermissions s ∨ e.CacheDowngrade)

abbrev Event.CacheGrant (e : Event) : Prop := e.CacheConstraint (·.Grant)
abbrev Event.CacheExternal (e : Event) : Prop := ¬e.CacheLocal ∨ e.CacheGrant
abbrev Event.CacheNoRequestPermissions (e : Event) (s : State) : Prop := e.CacheConstraint (·.NoRequestPermissions s)

abbrev Event.CacheWithoutCoherentPermissions (e : Event) (s : State) : Prop := e.CacheLocal ∧ e.CacheCoherent ∧ e.CacheNoRequestPermissions s

def OrderedCacheEvents' (e₁ e₂ : Event) (s₁ s₂ : State) : Prop :=
  e₁.isCacheEvent → e₂.isCacheEvent →
  e₁.SameStructure e₂ → e₁.SameAddress e₂ →
  if e₁.CacheNoEncapSameAddressDowngrade s₁ ∧ e₂.CacheNoEncapSameAddressDowngrade s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)
  else if e₁.CacheWithoutCoherentPermissions s₁ ∧ e₂.CacheExternal then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₁.Encapsulates e₂)
  else if e₁.CacheExternal ∧ e₂.CacheWithoutCoherentPermissions s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₂.Encapsulates e₁)
  else (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)
-/

-- def CoherentRead (r : Request) : Prop := r.coherent
-- abbrev CoherentRead := {r : Request // r.coherent = true ∧ r.rw = .r}
def CoherentRead : Request := ⟨ .r, true, .SC ⟩
def CoherentWrite : Request := ⟨ .w, true, .SC ⟩

def CacheEvent.SucceedingState (e : CacheEvent) (s : State) : State :=
  match e.d with
  | false => e.r.RequestState s
  | true => e.r.DowngradeState s

def DirectoryEvent.SucceedingState : /- ProtocolInterface → -/ DirectoryEvent → DirectoryState → DirectoryState
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
      /- These two cases .Vd .Vc, can be proven absurd by adding a hypothesis that the DirectoryState is an `Allowed` Directory State. -/
      | .Vd _ => DirectoryState.Vd ⟨Vd, by simp⟩
      | .Vc _ => DirectoryState.Vc ⟨Vc, by simp⟩
    | ⟨.w, false, _⟩ => DirectoryState.Vc ⟨Vc, by simp⟩ -- Non-Coherent-Write downgrade
    | ⟨.r, false, _⟩ => DirectoryState.I ⟨I, by simp⟩ -- Non-Coherent-Read downgrade

/- Can either prove a lemma to state the succeeding state is not `none` under `allowed input state` and `interface requests`,
   OR build in the input state and interface requests into the types.
-/

def Event.SucceedingState (e : Event) (s : EntryState) : EntryState := match e with
  | .cacheEvent ce => ⟨ce.SucceedingState s.cache, s.directory⟩
  | .directoryEvent de => ⟨s.cache, de.SucceedingState s.directory⟩
