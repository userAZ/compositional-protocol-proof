import CompositionalProtocolProof.Events
import CompositionalProtocolProof.Requests

variable (n : Nat)

def Event.Encapsulates (e₁ e₂ : Event n) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd
def CacheEvent.Encapsulates (e₁ e₂ : CacheEvent n) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd
def DirectoryEvent.Encapsulates (e₁ e₂ : DirectoryEvent n) : Prop := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd

abbrev CacheEvent.EncapsulatedBy (e₁ e₂ : CacheEvent n) : Prop := e₂.Encapsulates n e₁

def Event.OrderedBefore (e₁ e₂ : Event n) : Prop := e₁.oEnd < e₂.oStart
def CacheEvent.OrderedBefore (e₁ e₂ : CacheEvent n) : Prop := e₁.oEnd < e₂.oStart
def DirectoryEvent.OrderedBefore (e₁ e₂ : DirectoryEvent n) : Prop := e₁.oEnd < e₂.oStart

def Event.Ordered (e₁ e₂ : Event n) : Prop := e₁.OrderedBefore n e₂ ∨ e₂.OrderedBefore n e₁
def CacheEvent.Ordered (e₁ e₂ : CacheEvent n) : Prop := e₁.OrderedBefore n e₂ ∨ e₂.OrderedBefore n e₁
def DirectoryEvent.Ordered (e₁ e₂ : DirectoryEvent n) : Prop := e₁.OrderedBefore n e₂ ∨ e₂.OrderedBefore n e₁

/- Def for SWMR on pg 34. -/
/-- An event `e_pred` ends before another event `e_succ` -/
def Event.finishesBefore (e_pred e_succ : Event n) : Prop := e_pred.oEnd < e_succ.oEnd

/- Def for SWMR on pg 34. -/
/-- There's an intermediate event `e_inter` that finishes before the successor `e_succ`, and
predecessor `e_pred` finishes before `e_inter`, where `e_pred` and `e_inter` are at the same Entry. -/
structure Event.intermediateFinishesBeforeOfSameEntry (e_inter e_pred e_succ : Event n) : Prop where
  sameCidInterPred : e_inter.struct = e_pred.struct
  sameAddr : e_inter.addr = e_pred.addr
  interPred : e_pred.finishesBefore n e_inter
  interSucc : e_inter.finishesBefore n e_succ

/-- Inter finishes before `e_pred`, and is also not encapsulated by `e_succ` -/
structure Event.intermediateFinishesBeforeOfSameEntryNotEncap (e_inter e_pred e_succ : Event n) : Prop where
  interFinish : e_inter.intermediateFinishesBeforeOfSameEntry n e_pred e_succ
  notEncap : ¬ e_succ.Encapsulates n e_inter

def Event.fromDirectoryEvent (de : DirectoryEvent n) (e : Event n) : Prop :=
  match e with
  | .directoryEvent de' => de = de'
  | .cacheEvent _ => false

lemma DirectoryEvent.ordered_events {de₁ de₂ : DirectoryEvent n} {e₁ e₂ : Event n}
  (he₁_is_de₁ : e₁.fromDirectoryEvent n de₁) (he₂_is_de₂ : e₂.fromDirectoryEvent n de₂) : de₁.OrderedBefore n de₂ → e₁.OrderedBefore n e₂ := by
  unfold DirectoryEvent.OrderedBefore; unfold Event.OrderedBefore
  -- unfold DirectoryEvent.oEnd; unfold DirectoryEvent.oStart
  unfold Event.oEnd; unfold Event.oStart
  match he₁ : e₁, he₂ : e₂ with
  | .directoryEvent de₁', .directoryEvent de₂' =>
    subst he₁_is_de₁ he₂_is_de₂
    intro h_de₁_lt_de₂
    simp
    exact h_de₁_lt_de₂
  | .directoryEvent _, .cacheEvent _ => contradiction
  | .cacheEvent _, .directoryEvent _ => contradiction
  | .cacheEvent _, .cacheEvent _ => contradiction

lemma Event.contradiction_of_reflexive_ordered_before
  (he_ob_e : Event.OrderedBefore n e e)
  : False := by
  simp[Event.OrderedBefore] at he_ob_e
  absurd he_ob_e
  simp[Nat.le_iff_lt_or_eq]
  apply Or.intro_left
  exact e.oWellFormed

lemma Event.contradiction_of_ordered_both_ways
  (he_ob_e' : Event.OrderedBefore n e e')
  (he'_ob_e : Event.OrderedBefore n e' e)
  : False := by
  absurd he_ob_e'
  simp[OrderedBefore]
  simp[Nat.le_iff_lt_or_eq]
  apply Or.intro_left
  calc e'.oStart < e'.oEnd := e'.oWellFormed
    _ < e.oStart := he'_ob_e
    _ < e.oEnd := e.oWellFormed

lemma Event.contradiction_of_directory_event_ends_eq {de de2}
  {he_eq_cdir_end : Event.oEnd n (Event.directoryEvent de) = Event.oEnd n (Event.directoryEvent de2) }
  {hde_ob_cdir : DirectoryEvent.OrderedBefore n de de2}
  : False := by
  simp[DirectoryEvent.OrderedBefore] at hde_ob_cdir
  have hde_before_cdir_end : de.oEnd < de2.oEnd := by
    calc de.oEnd < de2.oStart := hde_ob_cdir
      _ < de2.oEnd := de2.oWellFormed
  absurd hde_before_cdir_end
  simp[Nat.le_iff_lt_or_eq,]
  apply Or.intro_right
  simp[Event.oEnd] at he_eq_cdir_end
  simp[he_eq_cdir_end]

def Event.Predecessor : Event n → Event n → Prop
| e_pred, e_succ => e_pred.OrderedBefore n e_succ

def Event.Successor : Event n → Event n → Prop
| e_pred, e_succ => e_pred.Predecessor n e_succ

instance Event.Encapsulates.instDecidableEncap (e₁ e₂ : Event n) : Decidable (e₁.Encapsulates n e₂) :=
  inferInstanceAs (Decidable (e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd))

instance Event.OrderedBefore.instLT : LT (Event n) := {lt := Event.OrderedBefore n}

instance Event.OrderedBefore.instDecidableLT (e₁ e₂ : Event n) : Decidable (e₁ < e₂) :=
  inferInstanceAs (Decidable (e₁.oEnd < e₂.oStart))

instance Event.OrderedBefore.instDecidableRel : DecidableRel (Event.OrderedBefore n) := by
  unfold DecidableRel
  intro e₁ e₂
  unfold Event.OrderedBefore
  infer_instance

lemma Event.ordered_trans {e₁ e₂ e₃ : Event n} : e₁ < e₂ → e₂ < e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold OrderedBefore.instLT
  simp
  unfold Event.OrderedBefore;
  intro he₁_lt_e₂ he₂_lt_e₃
  have he₂_well_formed := e₂.oWellFormed
  calc
    e₁.oEnd < e₂.oStart := he₁_lt_e₂
    _ < e₂.oEnd := he₂_well_formed
    _ < e₃.oStart := he₂_lt_e₃

instance Event.instTransOrderOrder : Trans (Event.OrderedBefore n) (Event.OrderedBefore n) (Event.OrderedBefore n) := {trans := Event.ordered_trans n}

lemma Event.order_encap_trans {e₁ e₂ e₃ : Event n} : e₁ < e₂ → e₂.Encapsulates n e₃ → e₁ < e₃ := by
  unfold LT.lt; unfold OrderedBefore.instLT
  simp
  unfold Event.OrderedBefore;
  unfold Encapsulates
  intro he₁_lt_e₂ he₂_encap_e₃
  calc
    e₁.oEnd < e₂.oStart := he₁_lt_e₂
    _ < e₃.oStart := he₂_encap_e₃.left

instance Event.instTransOrderEncap : Trans (Event.OrderedBefore n) (Event.Encapsulates n) (Event.OrderedBefore n) := {trans := Event.order_encap_trans n}

lemma Event.encap_encap_trans {e₁ e₂ e₃ : Event n} : e₁.Encapsulates n e₂ → e₂.Encapsulates n e₃ → e₁.Encapsulates n e₃ := by
  unfold Encapsulates;
  -- unfold OrderedBefore.instLT
  simp
  -- unfold Event.OrderedBefore;
  -- unfold Encapsulates
  intro he₁_lt_e₂_start he₂_lt_e₁_end he₂_lt_e₃_start he₃_lt_e₂_end
  apply And.intro
  . case left =>
    calc e₁.oStart < e₂.oStart := he₁_lt_e₂_start
      _ < e₃.oStart := he₂_lt_e₃_start
  . case right =>
    calc e₃.oEnd < e₂.oEnd := he₃_lt_e₂_end
      _ < e₁.oEnd := he₂_lt_e₁_end

instance Event.instTransEncapEncap : Trans (Event.Encapsulates n) (Event.Encapsulates n) (Event.Encapsulates n) := {trans := Event.encap_encap_trans n}

abbrev Event.EncapsulatedBy (e₁ e₂ : Event n) : Prop := e₂.Encapsulates n e₁

lemma Event.encap_by_order_trans {e₁ e₂ e₃ : Event n} : e₁.EncapsulatedBy n e₂ → e₂ < e₃ → e₁ < e₃ := by
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
instance Event.instTransEncapByOrder : Trans (Event.EncapsulatedBy n) (Event.OrderedBefore n) (Event.OrderedBefore n) := {trans := Event.encap_by_order_trans n}

lemma Event.encap_by_encap_by_trans {e₁ e₂ e₃ : Event n} : e₁.EncapsulatedBy n e₂ → e₂.EncapsulatedBy n e₃ → e₁.EncapsulatedBy n e₃ := by
  simp[EncapsulatedBy, Encapsulates]
  intro he₂_lt_e₁_start he₁_lt_e₂_end he₃_lt_e₂_start he₂_lt_e₃_end
  apply And.intro
  . case left =>
    calc oStart n e₃ < oStart n e₂ := he₃_lt_e₂_start
      _ < oStart n e₁ := he₂_lt_e₁_start
  . case right =>
    calc oEnd n e₁ < oEnd n e₂ := he₁_lt_e₂_end
      _ < oEnd n e₃ := he₂_lt_e₃_end

/- The shape of Trans's definition doesn't match to Event.encap_order_trans. Need to massage def. -/
instance Event.instTransEncapByEncapBy : Trans (Event.EncapsulatedBy n) (Event.EncapsulatedBy n) (Event.EncapsulatedBy n) := {trans := Event.encap_by_encap_by_trans n}

def Event.PropOnEvent (e : Event n) (p : Event n → Prop) : Prop := p e

structure Event.OrderedBetween (e e_pred e_succ : Event n) where
  pred : e_pred.OrderedBefore n e := by simp
  succ : e.OrderedBefore n e_succ := by simp

structure Event.OrderedBetweenSatisfyingProp (e e_pred e_succ : Event n) (p : Event n → Prop) where
  orderedBetween : e.OrderedBetween n e_pred e_succ
  satProp : p e

def CacheEvent.SameRequester (e₁ e₂ : CacheEvent n) : Prop := e₁.rid = e₂.rid
def CacheEvent.SameCache (e₁ e₂ : CacheEvent n) : Prop := e₁.cid = e₂.cid
def CacheEvent.SameAddress (e₁ e₂ : CacheEvent n) : Prop := e₁.addr = e₂.addr

def Event.CacheRelation (e₁ e₂ : Event n) : (CacheEvent n → CacheEvent n → Prop) → Prop
| p => match e₁ with
  | .cacheEvent ce₁ =>
    match e₂ with
    | .cacheEvent ce₂ => p ce₁ ce₂
    | .directoryEvent _ => false -- nothing happens
  | .directoryEvent _ => false -- nothing happens

def Event.SameStructureRelation (e₁ e₂ : Event n) :
  (CacheEvent n → CacheEvent n → Prop) → (DirectoryEvent n → DirectoryEvent n → Prop) → Prop
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
def DirectoryEvent.SameStructure (_ _ : DirectoryEvent n) : Prop := true
def DirectoryEvent.SameAddress (e₁ e₂ : DirectoryEvent n) : Prop := e₁.addr = e₂.addr

def Event.CacheSameRequester (e₁ e₂ : Event n) : Prop := e₁.CacheRelation n e₂ (·.SameRequester n ·)
def Event.SameStructure (e₁ e₂ : Event n) : Prop := e₁.SameStructureRelation n e₂ (·.SameCache n ·) (·.SameStructure n ·)
def Event.SameAddress (e₁ e₂ : Event n) : Prop := e₁.SameStructureRelation n e₂ (·.SameAddress n ·) (·.SameAddress n ·)

lemma Event.same_address_reflexive {e₁ e₂ e₃ : Event n} : e₁.SameAddress n e₃ → e₂.SameAddress n e₃ → e₁.SameAddress n e₂ := by
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

lemma Event.same_address_reflexive' {e₁ e₂ e₃ : Event n} : e₁.SameAddress n e₂ → e₁.SameAddress n e₃ → e₂.SameAddress n e₃ := by
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

lemma Event.same_structure_reflexive {e₁ e₂ e₃ : Event n} : e₁.SameStructure n e₃ → e₂.SameStructure n e₃ → e₁.SameStructure n e₂ := by
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

lemma Event.same_structure_reflexive' {e₁ e₂ e₃ : Event n} : e₁.SameStructure n e₂ → e₁.SameStructure n e₃ → e₂.SameStructure n e₃ := by
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

structure CacheEvent.ProgramOrdered (e₁ e₂ : CacheEvent n) where
  ordered : e₁.OrderedBefore n e₂ := by simp
  same_requester : e₁.SameRequester n e₂ := by simp

def Event.ProgramOrdered (e₁ e₂ : Event n) : Prop := e₁.CacheRelation n e₂ (·.ProgramOrdered n ·)

structure CacheEvent.sameCacheEntry (e₁ e₂ : CacheEvent n) : Prop where
  sameCache : e₁.cid = e₂.cid
  sameAddr : e₁.addr = e₂.addr

/-- Axiom 1
Events at a Directory address are ordered.
-/
structure DirectoryEvent.AreOrdered (de₁ de₂ : DirectoryEvent n) : Prop where
  sameDirectoryEntry : de₁.addr = de₂.addr
  ordered : de₁.Ordered n de₂

def CacheEvent.encapsulatedOrBefore (e₁ e₂ : CacheEvent n) : Prop := e₁.EncapsulatedBy n e₂ ∨ e₁.OrderedBefore n e₂
def CacheEvent.encapsulatedOrOrdered (e₁ e₂ : CacheEvent n) : Prop :=
  e₁.encapsulatedOrBefore n e₂ ∨ e₂.encapsulatedOrBefore n e₁

/-- If two cache events end at the same time, we show a contradiction
due to the fact that CacheEvents are Ordered. -/
lemma Event.contradiction_of_cache_event_ends_eq {ce ce_greq}
  {he_eq_greq_end : (Event.cacheEvent ce).oEnd = (Event.cacheEvent ce_greq).oEnd n}
  {hce_ob_greq : CacheEvent.encapsulatedOrBefore n ce ce_greq}
  : False := by
  simp[CacheEvent.encapsulatedOrBefore] at hce_ob_greq
  cases hce_ob_greq
  . case inl hce_encap_by_ce_greq =>
    have hde_before_greq_end : ce.oEnd < ce_greq.oEnd := hce_encap_by_ce_greq.right
    absurd hde_before_greq_end
    simp[Nat.le_iff_lt_or_eq,]
    apply Or.intro_right
    simp[Event.oEnd] at he_eq_greq_end
    simp[he_eq_greq_end]
  . case inr hce_ob_ce_greq =>
    have hde_before_greq_end : ce.oEnd < ce_greq.oEnd := by
      calc ce.oEnd < ce_greq.oStart := hce_ob_ce_greq
        _ < ce_greq.oEnd := ce_greq.oWellFormed
    absurd hde_before_greq_end
    simp[Nat.le_iff_lt_or_eq,]
    apply Or.intro_right
    simp[Event.oEnd] at he_eq_greq_end
    simp[he_eq_greq_end]

/-- Axiom 2.0: all cache events e₁ e₂ are ordered, either by:
1. e₁ is encapsulated by e₂, or
2. e₁ is ordered before e₂ -/
structure CacheEvent.AreOrdered (e₁ e₂ : CacheEvent n) : Prop where
  sameCacheEntry : e₁.sameCacheEntry n e₂
  ordered: e₁.encapsulatedOrOrdered n e₂

/-- Encapsulated at the `same` cache entry means it's a downgrade. -/
def CacheEvent.encapsulatedIsDowngrade (e₁ e₂ : CacheEvent n) : Prop :=
  e₁.Encapsulates n e₂ → e₂.down
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
def MonotonicDirectoryEventIds (de₁ de₂ : DirectoryEvent n) : Prop := de₁.OrderedBefore n de₂ → (de₁.deid + 1) = de₂.deid

/- Lean can't synthesize decidability in OrderedCacheEvents if these aren't `abbrev`s -/
abbrev CacheEvent.Local (e : CacheEvent n) : Prop := e.cid = e.rid
abbrev CacheEvent.NonCoherent (e : CacheEvent n) : Prop := e.req.val.coherent = false
abbrev CacheEvent.WeakConsistency (e : CacheEvent n) : Prop := e.req.val.consistency = .Weak

abbrev CacheEvent.Weak (e : CacheEvent n) : Prop := e.Local ∧ e.NonCoherent ∧ e.WeakConsistency

abbrev CacheEvent.RequestHasPermissions (e : CacheEvent n) (s : State) : Prop := e.req.MRS ≤ s
abbrev CacheEvent.Coherent (e : CacheEvent n) : Prop := e.req.val.coherent = true

abbrev CacheEvent.WithCoherentPermissions (e : CacheEvent n) (s : State) : Prop := e.Local ∧ e.Coherent ∧ e.RequestHasPermissions n s

abbrev CacheEvent.Downgrade (e : CacheEvent n) : Prop := e.down = true
abbrev CacheEvent.NoEncapSameAddressDowngrade (e : CacheEvent n) (s : State) : Prop := e.Weak ∨ e.WithCoherentPermissions n s ∨ e.Downgrade

abbrev CacheEvent.Grant (e : CacheEvent n) : Prop := e.deid? ≠ none ∧ ¬ e.Downgrade
abbrev CacheEvent.External (e : CacheEvent n) : Prop := ¬e.Local ∨ e.Grant
abbrev CacheEvent.NoRequestPermissions (e : CacheEvent n) (s : State) : Prop := s < e.req.MRS ∧ s ≠ I

abbrev CacheEvent.WithoutCoherentPermissions (e : CacheEvent n) (s : State) : Prop := e.Local ∧ e.Coherent ∧ e.NoRequestPermissions n s

def Event.sameStructure (e₁ e₂ : Event n) : Prop := e₁.struct = e₂.struct

def Event.sameAddr (e₁ e₂ : Event n) : Prop := e₁.addr = e₂.addr

structure Event.sameEntry (e₁ e₂ : Event n) : Prop where
  sameStruct : e₁.sameStructure n e₂
  sameAddr : e₁.sameAddr n e₂

lemma InitialSystemState.same_entry_eq {init e₁ e₂}
  (h : e₁.sameEntry n e₂)
  : (InitialSystemState.stateAt n init e₁) = (InitialSystemState.stateAt n init e₂) := by
  have hsame_struct := h.sameStruct
  simp[Event.sameStructure] at hsame_struct
  simp[Event.struct] at hsame_struct

  match e₁, e₂ with
  | .directoryEvent de₁, .directoryEvent de₂
  | .cacheEvent ce₁, .cacheEvent ce₂ =>
    simp at hsame_struct
    simp [stateAt]
    rw[hsame_struct]
  | .directoryEvent de₁, .cacheEvent ce₂
  | .cacheEvent ce₁, .directoryEvent de₂ =>
    simp at hsame_struct


noncomputable def CacheEvent.SucceedingState (e : CacheEvent n) (s : State) : State :=
  match e.down with
  | false => e.req.RequestState s
  | true => e.req.DowngradeState s

def DirectoryEvent.SucceedingState : /- ProtocolInterface → -/ DirectoryEvent n → DirectoryState n → DirectoryState n
| de, ds => match de.down with
  | false => match de.req.val with
    | ⟨.w, true, _⟩ => -- Coherent-Write
      DirectoryState.SW ⟨SW, by simp⟩ de.eReq.cid
    | ⟨.r, true, _⟩ => -- Coherent-Read
      DirectoryState.MR ⟨MR, by simp⟩ (ds.CurrentSharers ∪ {de.eReq.rid})
    | ⟨.w, false, _⟩ => -- Non-Coherent-Write
      -- MR forbidden
      DirectoryState.Vd ⟨Vd, by simp⟩
    | ⟨.r, false, _⟩ => -- Non-Coherent-Read
      match ds with
      | .SW sw _ => DirectoryState.Vd ⟨Vd, by simp⟩
      | .Vd vd => DirectoryState.Vd vd
      -- MR forbidden
      | _ => DirectoryState.Vc ⟨Vc, by simp⟩
  | true => match de.req.val with
    | ⟨.w, true, _⟩ => -- Coherent-Write Downgrade
      match ds with
      | .SW _ owner => -- Determined by the Protocol
        if de.eReq.cid == owner then DirectoryState.I ⟨I, by simp⟩
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
    | ⟨.w, false, _⟩ =>
      match ds with
      | .Vd _ => DirectoryState.Vc ⟨Vc, by simp⟩ -- Non-Coherent-Write downgrade
      | _ => ds -- Junk.
    | ⟨.r, false, _⟩ =>
      match ds with
      | .Vc _ => DirectoryState.I ⟨I, by simp⟩ -- Non-Coherent-Read downgrade
      | _ => ds -- Junk.

/-- Axiom. Directory state is the state after the Directory Event, this captures a Coherent Read's requester getting added to sharers. -/
def DirectoryEvent.directoryState (de : DirectoryEvent n) (s : EntryState n) : Prop := de.SucceedingState n s.directory = de.dirS

def Event.directoryState (e : Event n) (s : EntryState n) : Prop := match e with
  | .directoryEvent de => de.directoryState n s
  | .cacheEvent _ => false

/- Can either prove a lemma to state the succeeding state is not `none` under `allowed input state` and `interface requests`,
   OR build in the input state and interface requests into the types.
-/

noncomputable def Event.SucceedingState (e : Event n) (s : EntryState n) : EntryState n := match e with
  | .cacheEvent ce => Sum.inl <| ce.SucceedingState n s.cache
  | .directoryEvent de => Sum.inr <| de.SucceedingState n s.directory

structure Event.fwdRequest (e_req e_fwd : Event n) : Prop where
  sameRequest : e_req.req = e_fwd.req
  sameRequester : e_req.CacheSameRequester n e_fwd
  sameAddr : e_req.sameAddr n e_fwd

/-- Definition 2.35 -- A Downgrade Event generated by a corresponding to a Request Event -/
structure Event.downgradeOfRequestToOthers : Prop where
  atCid   : ∀ e_down : Event n, ∀ cid : CacheId n, e_down.isCacheEventAtCid n cid
  isDown  : ∀ e_down : Event n, e_down.isCacheEventDowngrade
  isFwded : ∀ e_req e_down : Event n, e_req.fwdRequest n e_down

def Event.isDirEventOfReqEvent : Event n → Event n → Prop
| e_dir, e_req => match e_dir with
  | .directoryEvent de => match e_req with
    | .cacheEvent ce => de.eReq = ce
    | .directoryEvent _ => false
  | .cacheEvent _ => false

def Event.deidOrderBefore (e₁ e₂ : Event n) : Prop := match e₁, e₂ with
| .cacheEvent ce₁, .cacheEvent ce₂ => ce₁.deid? < ce₂.deid?
| _, _ => false

/- Event Relations for Axioms 9 and 10, downgrades as a result of Coherent Requests accessing the Directory -/
/-- Def. Constraints/Props on the downgrade caused by a request -/
structure CacheEvent.downgradeOfReq (e_req e_down : CacheEvent n) : Prop where
  sameReq : e_req.req = e_down.req
  isDown : e_down.down
  downFromRequester : e_req.rid = e_down.rid

def Event.downgradeCorrespondingToRequest (e_req e_down : Event n) : Prop := match e_req, e_down with
  | .cacheEvent ce_req, .cacheEvent ce_down => ce_req.downgradeOfReq n ce_down
  | _, _ => false

/-- Def. Event is sent from the Directory, so carries the Directory's deid. -/
def Event.fromDirectory (e_from_dir e_dir : Event n) : Prop := match e_from_dir, e_dir with
  | .cacheEvent ce, .directoryEvent de => ce.deid? = de.deid
  | _, _ => false

/-- Def. A (downgrade) event is sent to the prev owner of a Directory Event's state. -/
def Event.downgradeAtPrevOwner (e_down : Event n) (dir_state : DirectoryState n) : Prop := match dir_state with
  | .SW _ owner => match e_down with
    | .cacheEvent ce => ce.cid = owner
    | .directoryEvent _ => false
  | _ => false

/-- Abbreviation 25. Grant Event of a Request Event. -/
structure CacheEvent.grantOfRequest (e_grant e_req: CacheEvent n) : Prop where
  sameReq : e_grant.req = e_req.req
  sameAddr : e_grant.addr = e_req.addr
  sameCache : e_grant.cid = e_req.cid
  sameRequester : e_grant.rid = e_req.rid
  sameDown : e_grant.down = e_req.down
  notDown : ¬ e_grant.down

/-- Event.Wrapper for Abbreviation 25. Grant Event of a Request Event. -/
def Event.grantToRequester (e_dir e_req e_grant : Event n) : Prop := match e_dir, e_req, e_grant with
  | .directoryEvent de, .cacheEvent req, .cacheEvent grant => de.deid = grant.deid? ∧ grant.grantOfRequest n req
  | _, _, _ => false

structure CacheEvent.downgradeOfReqToCache (e_req e_down : CacheEvent n) (destination_cid : CacheId n) : Prop where
  downgradeOfReq : e_req.downgradeOfReq n e_down
  atCache : e_down.cid = destination_cid

structure Event.encapGrantAfterDirEvent (e_req e_dir e_grant : Event n) : Prop where
  requestEncapGrant : e_req.Encapsulates n e_grant
  grantOfRequest : e_dir.grantToRequester n e_req e_grant
  grantEndsRequest : e_grant.oEnd = (e_req.oEnd + 1)
  dirBeforeGrant : e_dir.OrderedBefore n e_grant

structure Event.fwdMRDowngradeEventOrdering (e_req e_dir e_down e_grant : Event n) : Prop where
  dirEncapDowngrade : e_dir.Encapsulates n e_down
  reqDirGrantOrderings : e_req.encapGrantAfterDirEvent n e_dir e_grant

/- Defs for Def 2.36: Broadcast an event `e` to other entry addresses at a cache. -/

/-- Def. State that `e_original` and `e_cast_copy` have the same key fields {Requester, CacheId, Req, Down}. -/
structure CacheEvent.copyOfForCasting (e_original e_cast : CacheEvent n) : Prop where
  sameRequester : e_cast.rid = e_original.rid
  sameCache : e_cast.cid = e_original.cid
  sameReq : e_cast.req = e_original.req
  sameDown : e_cast.down = e_original.down

/-- Def. Open up Events `e_original` and `e_cast_copy`, to state they have the same key fields {Requester, CacheId, Req, Down}.
This is an events Wrapper for `CacheEvent.copyOfForCasting`. -/
def Event.copyOfForCasting (e_original e_cast_copy : Event n) : Prop := match e_original, e_cast_copy with
  | .cacheEvent original, .cacheEvent cast_copy => original.copyOfForCasting n cast_copy
  | _, _ => false

/-- Def. Copy an `e_original`, to a `e_cast_copy` at an Addr `other_addr`, where `e_cast_copy` is encapsulated by `e_base`. -/
structure Event.baseEncapBroadcast (other_addr : Addr) (e_base e_original e_cast_copy : Event n) : Prop where
  castOriginal : e_original.copyOfForCasting n e_cast_copy
  toOtherAddr : e_cast_copy.addr = other_addr
  baseEncapCast : e_base.Encapsulates n e_cast_copy

/-- Def. (broadcast ordered before e_dir) Copy an `e_original`, to a `e_cast_copy` at an Addr `other_addr`, where `e_cast_copy` is encapsulated by `e_base`. -/
structure Event.baseEncapBroadcastBefore (other_addr : Addr) (e_base e_original e_cast_copy e_dir : Event n) : Prop where
  broadcastEncapInBase : e_base.baseEncapBroadcast n other_addr e_original e_cast_copy
  beforeDir : e_cast_copy.OrderedBefore n e_dir

/-- Def. (broadcast ordered after e_dir) Copy an `e_original`, to a `e_cast_copy` at an Addr `other_addr`, where `e_cast_copy` is encapsulated by `e_base`. -/
structure Event.baseEncapBroadcastAfter (other_addr : Addr) (e_base e_original e_cast_copy e_dir : Event n) : Prop where
  broadcastEncapInBase : e_base.baseEncapBroadcast n other_addr e_original e_cast_copy
  afterDir : e_dir.OrderedBefore n e_cast_copy

/-- Def. two events are ordered before to the same entry.-/
structure Event.orderedBeforeToSameEntry (e_lin₂ e_lin₃ : Event n) : Prop where
  e₂e₃Before : e_lin₂.OrderedBefore n e_lin₃
  e₂e₃sameEntry : e_lin₂.sameEntry n e_lin₃

/-- The protocol instance of an event. -/
def Event.protocol (e_req : Event n) : ProtocolInstance := match e_req with
  | .cacheEvent ce => match ce.cid with
    | .proxy pi => pi
    | .cache pci => match pci with
      | .globalP _ => .global
      | .cluster1 _ => .cluster1
      | .cluster2 _ => .cluster2
  | .directoryEvent de => de.pInst

/-- State if two Events are of the same protocol -/
def Event.sameProtocol (e_req e_dir : Event n) : Prop := e_req.protocol = e_dir.protocol

/-- Define Lazy Linearization Order: For Linearization Events `e₁` `e₂` and `e₃`,
If `e₂` is Ordered Before `e₃`, and `e₁` finishes linearizing before `e₃`,
then we say `e₁` lazily linearizses before `e₃`. -/
structure Event.lazyLinearizationOrder (e_lin₁ e_lin₂ e_lin₃ : Event n) : Prop where
  e₁e₂sameProtocol : e_lin₁.sameProtocol n e_lin₂
  e₂e₃sameProtocol : e_lin₂.sameProtocol n e_lin₃
  e₁e₃FinishesBefore : e_lin₁.finishesBefore n e_lin₃
