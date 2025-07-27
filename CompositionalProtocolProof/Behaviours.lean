import CompositionalProtocolProof.EventRelations
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib

variable (n : Nat)

/-- New Axiom 2.
Use lemma `Behaviour.orderedBottomCacheEntries` to show two bottom cache events are
Totally Ordered. -/
structure Event.AtEntryOrdered where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent n), CacheEvent.AreOrdered n e₁ e₂

structure Behaviour where
  es : Set (Event n)
  -- es : Finset Event
  finite : Finite es
  orderedAtEntry : Event.AtEntryOrdered n

instance : Membership (Event n) (Behaviour n) := ⟨fun b e => e ∈ b.es⟩

def Behaviour.OrderedBetween : (Behaviour n) → (Event n) → (Event n) → Set (Event n)
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween n e_pred e_succ}

/-
def Behaviour.NoIntermediatePredecessor' (b : Behaviour) (e_pred e_succ : Event) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅
-/

structure Event.EncapAtSameStructure (e_bottom e : Event n) : Prop where
  encap : e_bottom.Encapsulates n e
  sameEntry : Event.sameEntry n e_bottom e

abbrev Behaviour.IsNotEncapAtSameStruct (b : Behaviour n) (e : Event n) : Prop := ∀ e' ∈ b.es, ¬ e'.EncapAtSameStructure n e

def Behaviour.IsBottomEvent (b : Behaviour n) (e : Event n) : Prop := b.IsNotEncapAtSameStruct n e

structure Behaviour.bottomSameEntry (b : Behaviour n) (e₁ e₂ : Event n) : Prop where
  sameEntry : e₁.sameEntry n e₂
  isBottom : b.IsBottomEvent n e₁

def Behaviour.noBottomIntermediatePredecessorAtSucc (b : Behaviour n) (e_inter e_pred e_succ : Event n) : Prop :=
  b.bottomSameEntry n e_inter e_succ → ¬ (e_inter.OrderedBetween n e_pred e_succ)

def Behaviour.NoIntermediatePredecessor (b : Behaviour n) (e_pred e_succ : Event n) : Prop :=
  ∀ e ∈ b, b.noBottomIntermediatePredecessorAtSucc n e e_pred e_succ

def Behaviour.noBottomIntermediatePredecessorAtSuccSatisfyingProp (b : Behaviour n) (e_inter e_pred e_succ : Event n) (p : Event n → Prop) : Prop :=
  b.bottomSameEntry n e_inter e_succ → ¬ (e_inter.OrderedBetweenSatisfyingProp n e_pred e_succ p)

def Behaviour.NoIntermediatePredecessorSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) : Prop :=
  ∀ e ∈ b, b.noBottomIntermediatePredecessorAtSuccSatisfyingProp n e e_pred e_succ p

/-
structure Behaviour.noBottomIntermediatePredecessorAtSuccSatisfyingProp (b : Behaviour n) (e_inter e_pred e_succ : Event n) (p : Event n → Prop) : Prop where
  bottomEntryNotInter : b.noBottomIntermediatePredecessorAtSuccSatisfyingProp n e_inter e_pred e_succ p
  satisfiesP : p e_inter

def Behaviour.NoIntermediatePredecessorSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) : Prop :=
  ∀ e ∈ b, b.noBottomIntermediatePredecessorAtSuccSatisfyingProp n e e_pred e_succ p
-/

structure Behaviour.Predecessor (b : Behaviour n) (e_pred e_succ : Event n) where
  sameEntry : Event.sameEntry n e_pred e_succ
  isPred : e_pred.Predecessor n e_succ
  predInB : e_pred ∈ b
  succInB : e_succ ∈ b

structure Behaviour.EntryImmediatePredecessor (b : Behaviour n) (e_pred e_succ : Event n) where
  -- sameEntry : Event.sameEntry n e_pred e_succ
  bPred : Behaviour.Predecessor n b e_pred e_succ
  noIntermediate : b.NoIntermediatePredecessor n e_pred e_succ

structure Behaviour.EntryImmediatePredecessorSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) where
  -- sameEntry : Event.sameEntry n e_pred e_succ
  bPred : Behaviour.Predecessor n b e_pred e_succ
  noIntermediateSatisfyingP : b.NoIntermediatePredecessorSatisfyingProp n e_pred e_succ p

/- Access properties nested deeper in Behaviour.ImmediatePredecessor -/
def Behaviour.EntryImmediatePredecessor.isPred {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred.Predecessor n e_succ := hb_imm_pred.bPred.isPred
def Behaviour.EntryImmediatePredecessor.predInB {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred ∈ b.es := hb_imm_pred.bPred.predInB
def Behaviour.EntryImmediatePredecessor.sameStructure {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred.sameStructure n e_succ := hb_imm_pred.bPred.sameEntry.sameStruct

/-- Old Axiom 2. Replaced by CacheEvent.AreOrdered.
Use lemma `Behaviour.orderedBottomCacheEntries` to show two bottom cache events are
Totally Ordered. -/
structure CacheEvent.BottomAreOrdered (e₁ e₂ : CacheEvent n) (b : Behaviour n) : Prop where
  sameCacheEntry : e₁.sameCacheEntry n e₂
  e₁Bottom : b.IsBottomEvent n (Event.cacheEvent e₁)
  e₂Bottom : b.IsBottomEvent n (Event.cacheEvent e₂)
  ordered : e₁.Ordered n e₂

structure Behaviour.IsImmediateBottomPred (b : Behaviour n) (e_pred e_succ : Event n) where
  isImmPred : b.EntryImmediatePredecessor n e_pred e_succ
  isBottomPred : b.IsBottomEvent n e_pred
  isBottomSucc : b.IsBottomEvent n e_succ

structure Behaviour.IsImmediateBottomPredSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) where
  isImmPred : b.EntryImmediatePredecessorSatisfyingProp n e_pred e_succ p
  isBottomPred : b.IsBottomEvent n e_pred
  isBottomSucc : b.IsBottomEvent n e_succ
  satisfyP : e_pred.PropOnEvent n p

/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour n → Event n → Event n → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred n e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor n e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

lemma Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction {e_pred₁ e_pred₂ e_succ : Event n} {b : Behaviour n}
(he₁_b : b.IsImmediateBottomPred n e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred n e_pred₂ e_succ)
(hes₁_ordered_es₂ : e_pred₁.Ordered n e_pred₂)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmPred.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₁_no_intermediate_to_e_suc

    /-
    have h := he₁_no_intermediate_to_e_suc e_pred₂ he₂_b.isImmPred.predInB
    simp[noBottomIntermediatePredecessorAtSucc] at h-/
    apply he₁_no_intermediate_to_e_suc e_pred₂ he₂_b.isImmPred.predInB
    . case a =>
      constructor
      . case sameEntry => exact he₂_b.isImmPred.bPred.sameEntry
      . case isBottom => exact he₂_b.isBottomPred
    . case a =>
      constructor
      unfold autoParam
      . case pred =>
        exact es₁_ordered_es₂
      . case succ =>
        unfold autoParam

        have e₂_o_e_succ := he₂_b.isImmPred.isPred
        unfold Event.Predecessor at e₂_o_e_succ
        exact e₂_o_e_succ
  . case inr es₂_ordered_es₁ =>
    have he₂_no_intermediate_to_e_suc := he₂_b.isImmPred.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₂_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₂_no_intermediate_to_e_suc

    apply he₂_no_intermediate_to_e_suc e_pred₁ he₁_b.isImmPred.predInB
    . case a =>
      constructor
      . case sameEntry => exact he₁_b.isImmPred.bPred.sameEntry
      . case isBottom => exact he₁_b.isBottomPred
    . case a =>
      constructor
      unfold autoParam
      . case pred =>
        exact es₂_ordered_es₁
      . case succ =>
        unfold autoParam

        have e₁_o_e_succ := he₁_b.isImmPred.isPred
        unfold Event.Predecessor at e₁_o_e_succ
        exact e₁_o_e_succ

lemma Behaviour.es₁_ordered_es₂_imm_bottom_pred_satisfying_p_contradiction {p : Event n → Prop} {e_pred₁ e_pred₂ e_succ : Event n} {b : Behaviour n}
(he₁_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₁ e_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₂ e_succ p)
(hes₁_ordered_es₂ : e_pred₁.Ordered n e_pred₂)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have h := he₁_b.isImmPred.noIntermediateSatisfyingP e_pred₂ he₂_b.isImmPred.bPred.predInB
    apply he₁_b.isImmPred.noIntermediateSatisfyingP e_pred₂ he₂_b.isImmPred.bPred.predInB
    . case a =>
      constructor
      . case sameEntry => exact he₂_b.isImmPred.bPred.sameEntry
      . case isBottom => exact he₂_b.isBottomPred
    . case a =>
      constructor
      . case orderedBetween =>
        constructor
        . case pred =>
          exact es₁_ordered_es₂
        . case succ =>
          unfold autoParam

          have e₂_o_e_succ := he₂_b.isImmPred.bPred.isPred
          unfold Event.Predecessor at e₂_o_e_succ
          exact e₂_o_e_succ
      . case satProp => exact he₂_b.satisfyP
  . case inr es₂_ordered_es₁ =>
    apply he₂_b.isImmPred.noIntermediateSatisfyingP e_pred₁ he₁_b.isImmPred.bPred.predInB
    . case a =>
      constructor
      . case sameEntry => exact he₁_b.isImmPred.bPred.sameEntry
      . case isBottom => exact he₁_b.isBottomPred
    . case a =>
      constructor
      . case orderedBetween =>
        constructor
        . case pred =>
          exact es₂_ordered_es₁
        . case succ =>
          unfold autoParam

          have e₁_o_e_succ := he₁_b.isImmPred.bPred.isPred
          unfold Event.Predecessor at e₁_o_e_succ
          exact e₁_o_e_succ
      . case satProp => exact he₁_b.satisfyP

lemma CacheEvent.encap_then_event_encap (ce₁ ce₂ : CacheEvent n) (hencap : ce₁.Encapsulates n ce₂) :
  (Event.cacheEvent ce₁).Encapsulates n (Event.cacheEvent ce₂) := by
  unfold Event.Encapsulates Event.oStart Event.oEnd
  simp[CacheEvent.Encapsulates] at hencap
  exact hencap

lemma Event.same_entry_symm (e₁ e₂ : Event n) (hsame_entry : e₁.sameEntry n e₂) : e₂.sameEntry n e₁ := by
  constructor
  . case sameStruct =>
    have hsame_struct := hsame_entry.sameStruct
    simp_all[Event.sameStructure]
  . case sameAddr =>
    have hsame_addr := hsame_entry.sameAddr
    simp_all[Event.sameAddr]

lemma Behaviour.orderedBottomCacheEntries (b : Behaviour n) (ce₁ ce₂ : CacheEvent n)
  (he₁_in_b : Event.cacheEvent ce₁ ∈ b.es) (he₂_in_b : Event.cacheEvent ce₂ ∈ b.es)
  (he₁_bottom : b.IsBottomEvent n (Event.cacheEvent ce₁))
  (he₂_bottom : b.IsBottomEvent n (Event.cacheEvent ce₂))
  (he₁_same_entry_e₂ : (Event.cacheEvent ce₁).sameEntry n (Event.cacheEvent ce₂))
  : ce₁.Ordered n ce₂ := by
  have hce₁_encap_ordered_e₂ := b.orderedAtEntry.cache_ordered ce₁ ce₂ |>.ordered
  unfold CacheEvent.encapsulatedOrOrdered CacheEvent.encapsulatedOrBefore at hce₁_encap_ordered_e₂

  unfold CacheEvent.Ordered
  cases hce₁_encap_ordered_e₂
  . case inl hencap_order =>
    cases hencap_order
    . case inl hencap =>
      unfold CacheEvent.EncapsulatedBy at hencap
      unfold IsBottomEvent IsNotEncapAtSameStruct at he₁_bottom
      have hnot_e₂_encap_e₁ := he₁_bottom (Event.cacheEvent ce₂) (he₂_in_b)
      simp at hnot_e₂_encap_e₁
      apply Event.same_entry_symm at he₁_same_entry_e₂
      have he₂_encap_e₁ :
        Event.EncapAtSameStructure n (Event.cacheEvent ce₂) (Event.cacheEvent ce₁)
        := {encap := (ce₂.encap_then_event_encap n ce₁ hencap),
            sameEntry := he₁_same_entry_e₂}
      absurd hnot_e₂_encap_e₁
      exact he₂_encap_e₁
    . case inr horder =>
      apply Or.intro_left
      exact horder
  . case inr hencap_order =>
    cases hencap_order
    . case inl hencap =>
      unfold CacheEvent.EncapsulatedBy at hencap
      unfold IsBottomEvent IsNotEncapAtSameStruct at he₁_bottom
      have hnot_e₁_encap_e₂ := he₂_bottom (Event.cacheEvent ce₁) (he₁_in_b)
      simp at hnot_e₁_encap_e₂
      -- apply Event.same_entry_symm at he₁_same_entry_e₂
      have he₁_encap_e₂ :
        Event.EncapAtSameStructure n (Event.cacheEvent ce₁) (Event.cacheEvent ce₂)
        := {encap := (ce₁.encap_then_event_encap n ce₂ hencap),
            sameEntry := he₁_same_entry_e₂}
      absurd hnot_e₁_encap_e₂
      exact he₁_encap_e₂
    . case inr horder =>
      apply Or.intro_right
      exact horder

lemma Event.same_entry_trans {e₁ e₂ e : Event n} (he₁_entry_e : e₁.sameEntry n e) (he₂_entry_e : e₂.sameEntry n e)
  : e₁.sameEntry n e₂ := by
  constructor
  . case sameStruct =>
    have he₁_struct_e := he₁_entry_e.sameStruct
    have he₂_struct_e := he₂_entry_e.sameStruct
    simp_all[sameStructure]
  . case sameAddr =>
    have he₁_addr_e := he₁_entry_e.sameAddr
    have he₂_addr_e := he₂_entry_e.sameAddr
    simp_all[sameAddr]

lemma Event.same_entry_trans' {e₁ e₂ e : Event n} (he_entry_e₁ : e.sameEntry n e₁) (he_entry_e₂ : e.sameEntry n e₂)
  : e₁.sameEntry n e₂ := by
  constructor
  . case sameStruct =>
    have he_struct_e₁ := he_entry_e₁.sameStruct
    have he_struct_e₂ := he_entry_e₂.sameStruct
    simp_all[sameStructure]
  . case sameAddr =>
    have he_addr_e₁ := he_entry_e₁.sameAddr
    have he_addr_e₂ := he_entry_e₂.sameAddr
    simp_all[sameAddr]

lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour n) (e_succ : Event n)
  (e_pred₁ e_pred₂ : Event n)
  (he₁_b : b.IsImmediateBottomPred n e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred n e_pred₂ e_succ) :
  e_pred₁ = e_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b's NoIntermediatePredecessor.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : e_pred₁, h_pred₂ : e_pred₂ with
    | .directoryEvent de₁, .directoryEvent de₂ => -- Use dir_ordered to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := b.orderedAtEntry.dir_ordered de₁ de₂
      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction n he₁_b he₂_b de₁_de₂_ordered_prop.ordered
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      have hpred₁_pred₂_same_entry := Event.same_entry_trans n he₁_b.isImmPred.bPred.sameEntry he₂_b.isImmPred.bPred.sameEntry
      have ce₁_ce₂_ordered := orderedBottomCacheEntries n b ce₁ ce₂ he₁_b.isImmPred.predInB he₂_b.isImmPred.predInB
        he₁_b.isBottomPred he₂_b.isBottomPred hpred₁_pred₂_same_entry

      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction n he₁_b he₂_b ce₁_ce₂_ordered
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmPred.sameStructure
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_cache
        unfold Event.struct at e₂_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₂_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_dir
        unfold Event.struct at e₁_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₁_same_struct_e_succ
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_cache
        unfold Event.struct at e₁_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₁_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_dir
        unfold Event.struct at e₂_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₂_same_struct_e_succ

lemma Behaviour.immediate_bottom_predecessor_satisfying_p_unique {p : Event n → Prop} {b : Behaviour n} {e_succ : Event n} {e_pred₁ e_pred₂ : Event n}
  (he₁_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₁ e_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₂ e_succ p) :
  e_pred₁ = e_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b's NoIntermediatePredecessor.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : e_pred₁, h_pred₂ : e_pred₂ with
    | .directoryEvent de₁, .directoryEvent de₂ => -- Use dir_ordered to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := b.orderedAtEntry.dir_ordered de₁ de₂
      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_satisfying_p_contradiction n he₁_b he₂_b de₁_de₂_ordered_prop.ordered
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      have hpred₁_pred₂_same_entry := Event.same_entry_trans n he₁_b.isImmPred.bPred.sameEntry he₂_b.isImmPred.bPred.sameEntry
      have ce₁_ce₂_ordered := orderedBottomCacheEntries n b ce₁ ce₂ he₁_b.isImmPred.bPred.predInB he₂_b.isImmPred.bPred.predInB
        he₁_b.isBottomPred he₂_b.isBottomPred hpred₁_pred₂_same_entry

      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_satisfying_p_contradiction n he₁_b he₂_b ce₁_ce₂_ordered
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.bPred.sameEntry.sameStruct
      have h_e_succ_is_cache := he₂_b.isImmPred.bPred.sameEntry.sameStruct
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_cache
        unfold Event.struct at e₂_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₂_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_dir
        unfold Event.struct at e₁_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₁_same_struct_e_succ
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.bPred.sameEntry.sameStruct
      have h_e_succ_is_dir   := he₂_b.isImmPred.bPred.sameEntry.sameStruct
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_cache
        unfold Event.struct at e₁_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₁_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_dir
        unfold Event.struct at e₂_same_struct_e_succ
        simp[Event.sameStructure, Event.struct] at e₂_same_struct_e_succ

lemma Set.nonempty_unique_is_singleton {α} (s : Set α) (h_nonempty : Nonempty s)
  (h_unique : ∀ (a b : α),  a ∈ s → b ∈ s → a = b) : s.IsSingleton := by
  have ⟨a, ha⟩ := h_nonempty
  exists a
  apply Set.ext
  intro x
  constructor
  · case mp =>
    intro hxa
    exact -- canonical
      Eq.rec (motive := fun a_1 t ↦ s a_1)
        (Nonempty.rec (motive := fun t ↦ s a) (fun val ↦ ha) h_nonempty)
        (Eq.rec (motive := fun a t ↦ a = x) (Eq.refl x) hxa)
  · case mpr =>
    intro hxs
    exact h_unique x a hxs ha

/-- Lemma 1 from the Doc.
The set of Immediate Bottom Predecessors is Empty or Unique. (without the φ on the predecessor yet.)
-/
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour n) (e_succ : Event n)
  :
  let imm_bottom_preds := b.ImmBottomPredecessors n e_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event n), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique n b e_succ e₁ e₂
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

lemma Behaviour.IsImmediateBottomPredSatisfyingProp_neg {b : Behaviour n} {e_pred e_succ : Event n} {p : Event n → Prop}
  : ¬ b.IsImmediateBottomPredSatisfyingProp n e_pred e_succ p → ¬ (b.IsImmediateBottomPredSatisfyingProp n e_pred e_succ p ∧ e_pred.PropOnEvent n p) := by
  intro hneg_imm_pred hprop_fields
  apply hneg_imm_pred
  constructor
  . case isImmPred => exact hprop_fields.left.isImmPred
  . case isBottomPred => exact hprop_fields.left.isBottomPred
  . case isBottomSucc => exact hprop_fields.left.isBottomSucc
  . case satisfyP => exact hprop_fields.right

def Behaviour.ImmediateBottomPredSatisfyingProp : Behaviour n → Event n → Event n → (Event n → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomPredSatisfyingProp n e_pred e_succ p

def Behaviour.ImmBottomPredecessorsSatisfyingP : Behaviour n → Event n → (Event n → Prop) → Set (Event n)
| b, e_succ, p => {e_pred ∈ b.es | b.ImmediateBottomPredSatisfyingProp n e_pred e_succ p}

/-- Lemma 1, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_predecessor_satisfying_p_empty_or_unique (b : Behaviour n) (e_succ : Event n) (p : Event n → Prop)
  :
  let imm_bottom_preds := b.ImmBottomPredecessorsSatisfyingP n e_succ p; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event n), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_satisfying_p_unique n /-b e_succ e₁ e₂ p-/
      . case he₁_b => exact And.right he₁
      . case he₂_b => exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Now define the immediate bottom successor. -/

structure Behaviour.ImmediateSuccessorConstraint (b : Behaviour n) (e_pred e_succ : Event n) where
  isSucc : e_pred.Successor n e_succ
  noIntermediate : b.NoIntermediatePredecessor n e_pred e_succ
  sameEntry : e_pred.sameEntry n e_succ
  -- sameAddress : e_pred.SameAddress n e_succ
  -- sameStructure : e_pred.SameStructure n e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

structure Behaviour.IsImmediateBottomSucc (b : Behaviour n) (e_pred e_succ : Event n) where
  isImmSucc : b.ImmediateSuccessorConstraint n e_pred e_succ
  isBottom : b.IsBottomEvent n e_succ

def Behaviour.ImmediateBottomSuccessor : Behaviour n → Event n → Event n → Prop
| b, e_pred, e_succ => b.IsImmediateBottomSucc n e_pred e_succ

def Behaviour.ImmBottomSuccessors : Behaviour n → Event n → Set (Event n)
| b, e_pred => {e_succ ∈ b.es | b.ImmediateBottomSuccessor n e_pred e_succ}

lemma Event.event_same_entry_trans {e₁ e₂ e₃} (he₁_e₃ : Event.sameEntry n e₃ e₁) (he₂_e₃ : e₃.sameEntry n e₂) : (e₁.sameEntry n e₂) := by
  constructor
  . case sameStruct =>
    simp_all[sameStructure,]
    rw[← he₂_e₃.sameStruct, he₁_e₃.sameStruct]
  . case sameAddr =>
    simp_all[sameAddr,]
    rw[← he₂_e₃.sameAddr, he₁_e₃.sameAddr]

lemma Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction {e_pred e_succ₁ e_succ₂ : Event n} {b : Behaviour n}
(he₁_b : b.IsImmediateBottomSucc n e_pred e_succ₁) (he₂_b : b.IsImmediateBottomSucc n e_pred e_succ₂)
(hes₁_ordered_es₂ : e_succ₁.OrderedBefore n e_succ₂ ∨ e_succ₂.OrderedBefore n e_succ₁)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have e_pred_o_e_succ₁ := he₁_b.isImmSucc.isSucc
    unfold Event.Predecessor at e_pred_o_e_succ₁
    unfold Event.Successor at e_pred_o_e_succ₁
    simp at e_pred_o_e_succ₁

    apply he₂_b.isImmSucc.noIntermediate e_succ₁ he₁_b.isImmSucc.succInB
    . case a =>
      constructor
      . case sameEntry =>
        constructor
        . case sameStruct =>
          have he₁_struct := he₁_b.isImmSucc.sameEntry.sameStruct
          have he₂_struct := he₂_b.isImmSucc.sameEntry.sameStruct
          simp_all[Event.sameStructure]
        . case sameAddr =>
          have he₁_addr := he₁_b.isImmSucc.sameEntry.sameAddr
          have he₂_addr := he₂_b.isImmSucc.sameEntry.sameAddr
          simp_all[Event.sameAddr]
      . case isBottom => exact he₁_b.isBottom
    . case a =>
      constructor
      unfold autoParam
      . case pred =>
        unfold Event.Predecessor at e_pred_o_e_succ₁
        simp at e_pred_o_e_succ₁
        unfold Event.OrderedBefore
        exact e_pred_o_e_succ₁
      . case succ =>
        unfold autoParam
        exact es₁_ordered_es₂
  . case inr es₂_ordered_es₁ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmSucc.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₁_no_intermediate_to_e_suc
    have e_pred_o_e_succ₂ := he₂_b.isImmSucc.isSucc
    unfold Event.Successor at e_pred_o_e_succ₂
    simp at e_pred_o_e_succ₂

    apply he₁_b.isImmSucc.noIntermediate e_succ₂ he₂_b.isImmSucc.succInB
    . case a =>
      constructor
      . case sameEntry =>
        constructor
        . case sameStruct =>
          have he₁_struct := he₁_b.isImmSucc.sameEntry.sameStruct
          have he₂_struct := he₂_b.isImmSucc.sameEntry.sameStruct
          simp_all[Event.sameStructure]
        . case sameAddr =>
          have he₁_addr := he₁_b.isImmSucc.sameEntry.sameAddr
          have he₂_addr := he₂_b.isImmSucc.sameEntry.sameAddr
          simp_all[Event.sameAddr]
      . case isBottom => exact he₂_b.isBottom
    . case a =>
      constructor
      unfold autoParam
      . case pred =>
        unfold Event.Predecessor at e_pred_o_e_succ₂
        simp at e_pred_o_e_succ₂
        unfold Event.OrderedBefore
        exact e_pred_o_e_succ₂
      . case succ =>
        unfold autoParam
        exact es₂_ordered_es₁

lemma Behaviour.immediate_bottom_successor_unique (b : Behaviour n) (e_pred : Event n)
  (e_succ₁ e_succ₂ : Event n) (he₁_b : b.IsImmediateBottomSucc n e_pred e_succ₁) (he₂_b : b.IsImmediateBottomSucc n e_pred e_succ₂) :
  e_succ₁ = e_succ₂ := by
    by_contra h_e_pred_diff
    match h_succ₁ : e_succ₁, h_succ₂ : e_succ₂ with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      have de₁_de₂_ordered_prop := b.orderedAtEntry.dir_ordered de₁ de₂
      apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction n he₁_b he₂_b de₁_de₂_ordered_prop.ordered
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      /- Part 1. Use OrderedCacheEvents to show that ce₁ and ce₂ (which are bottom predecessors to e_succ)
      are always ordered. Part 2. This is a contradiction with ImmediateBottomPred's NoIntermediatePred. -/
      have hpred₁_pred₂_same_entry := Event.same_entry_trans' n he₁_b.isImmSucc.sameEntry he₂_b.isImmSucc.sameEntry
      have hce₁_ce₂_ordered := orderedBottomCacheEntries n b ce₁ ce₂ he₁_b.isImmSucc.succInB he₂_b.isImmSucc.succInB
        he₁_b.isBottom he₂_b.isBottom hpred₁_pred₂_same_entry
      apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction n he₁_b he₂_b hce₁_ce₂_ordered
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmSucc.sameEntry.sameStruct
      have h_e_succ_is_cache := he₂_b.isImmSucc.sameEntry.sameStruct
      simp_all[Event.sameStructure, Event.struct]
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmSucc.sameEntry.sameStruct
      have h_e_succ_is_dir   := he₂_b.isImmSucc.sameEntry.sameStruct
      simp_all[Event.sameStructure, Event.struct]

lemma Behaviour.immediate_bottom_successor_empty_or_unique (b : Behaviour n) (e_pred : Event n)
  :
  let imm_bottom_succs := b.ImmBottomSuccessors n e_pred; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event n), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_unique n b e_pred e₁ e₂
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Verision of Immediate Bottom Successor that also satisfies Prop `p`. -/

structure Behaviour.IsImmediateBottomSuccSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) where
  isImmBottomSucc : b.IsImmediateBottomSucc n e_pred e_succ
  satisfyP : e_succ.PropOnEvent n p

def Behaviour.ImmediateBottomSuccSatisfyingProp : Behaviour n → Event n → Event n → (Event n → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomSuccSatisfyingProp n e_pred e_succ p

def Behaviour.ImmBottomSuccessorsSatisfyingP : Behaviour n → Event n → (Event n → Prop) → Set (Event n)
| b, e_pred, p => {e_succ ∈ b.es | b.ImmediateBottomSuccSatisfyingProp n e_pred e_succ p}

lemma Behaviour.immediate_bottom_successor_satisfying_p_unique (b : Behaviour n) (e_pred : Event n)
  (e_succ₁ e_succ₂ : Event n) (p : Event n → Prop)
  (he₁_b : b.IsImmediateBottomSuccSatisfyingProp n e_pred e_succ₁ p) (he₂_b : b.IsImmediateBottomSuccSatisfyingProp n e_pred e_succ₂ p) :
  e_succ₁ = e_succ₂ := by
    have he₁_b' : b.IsImmediateBottomSucc n e_pred e_succ₁ := by
      constructor
      exact he₁_b.isImmBottomSucc.isImmSucc
      exact he₁_b.isImmBottomSucc.isBottom
    have he₂_b' : b.IsImmediateBottomSucc n e_pred e_succ₂ := by
      constructor
      exact he₂_b.isImmBottomSucc.isImmSucc
      exact he₂_b.isImmBottomSucc.isBottom

    apply Behaviour.immediate_bottom_successor_unique n b e_pred e_succ₁ e_succ₂ he₁_b' he₂_b'

/-- Lemma 2, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_successor (b : Behaviour n) (e_pred : Event n) (p : Event n → Prop)
  :
  let imm_bottom_succs := b.ImmBottomSuccessorsSatisfyingP n e_pred p; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event n), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_satisfying_p_unique n b e_pred e₁ e₂ p
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Defs for SWMR on pg 34. -/

structure Behaviour.finishesBeforeNotEncap (b : Behaviour n) (e_pred e_succ : Event n) where
  endBefore : e_pred.finishesBefore n e_succ
  notEncap : ¬ e_succ.Encapsulates n e_pred
  sameAddr : e_pred.sameAddr n e_succ
  predInB : e_pred ∈ b
  succInB : e_succ ∈ b

-- [NOTE] Consider declaring instance of Transitivity

structure Behaviour.finishesBefore (b : Behaviour n) (e_pred e_succ : Event n) where
  endBefore : e_pred.finishesBefore n e_succ
  sameAddr : e_pred.sameAddr n e_succ
  predInB : e_pred ∈ b
  succInB : e_succ ∈ b

/-- An event `e_pred` ends before another event `e_succ` in a Behaviour `b`, in a different Cache `cid`
and the same protocol. -/
structure Behaviour.finishesBeforeAtDifferentCid (b : Behaviour n) (e_pred e_succ : Event n) where
  finBefore : b.finishesBefore n e_pred e_succ
  diffCidSameProtocol : e_pred.eventOfDifferentCidInSameProtocol n e_succ

/-- There is _no_ intermediate event `e_inter` that finishes before the successor `e_succ`, and
predecessor `e_pred` finishes before `e_inter` in the same entry. Note that `e_pred` is at a different `cid`
than `e_succ` in the same Protocol. -/
def Behaviour.noIntermediateFinishesBeforeOfSameEntry (b : Behaviour n) (e_pred e_succ : Event n) : Prop :=
  ∀ e_inter ∈ b, ¬ e_inter.intermediateFinishesBeforeOfSameEntry n e_pred e_succ

/-- There is no event `e_inter` that _immediately_ finishes before the successor `e_succ` -/
structure Behaviour.immediateFinishesBeforeAtDifferentCid (b : Behaviour n) (e_pred e_succ : Event n) where
  finishBefore : Behaviour.finishesBeforeAtDifferentCid n b e_pred e_succ
  noIntermediate : b.noIntermediateFinishesBeforeOfSameEntry n e_pred e_succ

def Behaviour.immediateFinishesBeforeAtDifferentCidEvents : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b.es | b.immediateFinishesBeforeAtDifferentCid n e_pred e_succ}

lemma Behaviour.contradiction_of_e_succ_eq_e_imm_finishes_before'
  {e e' e_succ : Event n} {cid : CacheId n} {b : Behaviour n}
  (he_at_cid : Event.atCid n e cid) (he'_at_cid : Event.atCid n e' cid)
  (he_eq_e_succ : e = e_succ)
  (he'_imm_fin_before : e' ∈ b.es ∧ Behaviour.immediateFinishesBeforeAtDifferentCid n b e' e_succ)
  : False := by
  have hcid_e' := he'_imm_fin_before.right.finishBefore.diffCidSameProtocol
  simp[Event.eventOfDifferentCidInSameProtocol, Event.propOnUnitaryCid,
    Event.propOnBinaryCid,] at hcid_e'
  match hce' : e', he_succ' : e_succ with
  | .cacheEvent ce', .cacheEvent ce_succ =>
    simp[] at hcid_e'
    have hdiff_cid := hcid_e'.ne
    have same_cid : ce'.cid = ce_succ.cid := by
      simp[Event.atCid, he_eq_e_succ] at he_at_cid he'_at_cid
      rw[he_at_cid, he'_at_cid]
    contradiction
  | .cacheEvent _, .directoryEvent _
  | .directoryEvent _, .cacheEvent _
  | .directoryEvent _, .directoryEvent _ =>
    simp[] at hcid_e'

lemma Behaviour.contradiction_of_e_e'_immediate_finishes_before_successor_e_finishes_before_e'
  {e e' e_succ : Event n} {cid : CacheId n} {b : Behaviour n}
  (he_imm : Behaviour.immediateFinishesBeforeAtDifferentCid n b e e_succ) (he'_imm : Behaviour.immediateFinishesBeforeAtDifferentCid n b e' e_succ)
  (he_at_cid : e.atCid n cid) (he'_at_cid : e'.atCid n cid)
  (he_in_b : e ∈ b.es) (he'_in_b : e' ∈ b.es)
  (he_finish_before_e' : e.finishesBefore n e')
  : False := by
  have he_no_inter := he_imm.noIntermediate
  simp[noIntermediateFinishesBeforeOfSameEntry] at he_no_inter
  have he_no_inter_of_e' := he_no_inter e' he'_in_b
  exfalso
  apply he_no_inter_of_e'
  constructor
  . case sameCidInterPred =>
    match hce : e, hce' : e' with
    | .cacheEvent ce, .cacheEvent ce' =>
      simp[Event.atCid] at he_at_cid he'_at_cid
      simp[Event.struct, he_at_cid, he'_at_cid]
    | .cacheEvent _, .directoryEvent _
    | .directoryEvent _, .cacheEvent _
    | .directoryEvent _, .directoryEvent _ =>
      simp[Event.atCid] at he_at_cid he'_at_cid
  . case sameAddr =>
    have he_at_addr := he_imm.finishBefore.finBefore.sameAddr
    have he'_at_addr := he'_imm.finishBefore.finBefore.sameAddr
    simp[Event.sameAddr] at he_at_addr he'_at_addr
    simp[he_at_addr, he'_at_addr]
  . case interPred => exact he_finish_before_e'
  . case interSucc => exact he'_imm.finishBefore.finBefore.endBefore

lemma CacheEvent.contradiction_of_ce_ce'_end_at_same_time {ce ce' : CacheEvent n}
  (he'_e_finish_at_the_same_time : Event.oEnd n (Event.cacheEvent ce') = Event.oEnd n (Event.cacheEvent ce))
  (hce_encap_or_before_ce' : CacheEvent.encapsulatedOrBefore n ce ce')
  : False := by
  simp[CacheEvent.encapsulatedOrBefore] at hce_encap_or_before_ce'
  cases hce_encap_or_before_ce'
  . case inl hce_encap_by_ce' =>
    have hce_ce'_end_at_different_times :
      (Event.cacheEvent ce').oEnd ≠ (Event.cacheEvent ce).oEnd := by
      simp[CacheEvent.EncapsulatedBy, CacheEvent.Encapsulates] at hce_encap_by_ce'
      rw[Nat.ne_iff_lt_or_gt]
      apply Or.intro_right
      . case h => exact hce_encap_by_ce'.right
    contradiction
  . case inr hce_before_ce' =>
    have hce_ce'_end_at_different_times :
      (Event.cacheEvent ce').oEnd ≠ (Event.cacheEvent ce).oEnd := by
      simp[CacheEvent.OrderedBefore] at hce_before_ce'
      have hce_end_before_ce' : ce.oEnd < ce'.oEnd :=
        calc ce.oEnd < ce'.oStart := hce_before_ce'
          _ < ce'.oEnd := ce'.oWellFormed
      rw[Nat.ne_iff_lt_or_gt]
      apply Or.intro_right
      . case h => exact hce_end_before_ce'
    contradiction

lemma Behaviour.contradiction_of_two_events_immediate_finishes_before_successor_event
  {b : Behaviour n} {cid : CacheId n} {e e' e_succ : Event n}
  (he_imm : Behaviour.immediateFinishesBeforeAtDifferentCid n b e e_succ)
  (he'_imm : Behaviour.immediateFinishesBeforeAtDifferentCid n b e' e_succ)
  (he_at_cid : e.atCid n cid)
  (he'_at_cid : e'.atCid n cid)
  (he_in_b : e ∈ b.es)
  (he'_in_b : e' ∈ b.es)
  : False := by
  by_cases he_finishes_before_e' : e.finishesBefore n e'
  . case pos =>
    apply b.contradiction_of_e_e'_immediate_finishes_before_successor_e_finishes_before_e'
    . case he_imm => exact he_imm
    . case he'_imm => exact he'_imm
    . case he_at_cid => exact he_at_cid
    . case he'_at_cid => exact he'_at_cid
    . case he_in_b => exact he_in_b
    . case he'_in_b => exact he'_in_b
    . case he_finish_before_e' => exact he_finishes_before_e'
  . case neg =>
    apply b.contradiction_of_e_e'_immediate_finishes_before_successor_e_finishes_before_e'
    . case he_imm => exact he'_imm
    . case he'_imm => exact he_imm
    . case he_at_cid => exact he'_at_cid
    . case he'_at_cid => exact he_at_cid
    . case he_in_b => exact he'_in_b
    . case he'_in_b => exact he_in_b
    . case he_finish_before_e' =>
      simp[Event.finishesBefore] at he_finishes_before_e'
      simp[Nat.le_iff_lt_or_eq] at he_finishes_before_e'
      cases he_finishes_before_e'
      . case inl he'_finishes_before_e =>
        rw[← Event.finishesBefore.eq_def] at he'_finishes_before_e
        exact he'_finishes_before_e
      . case inr he'_e_finish_at_the_same_time =>
        have he_ordered := b.orderedAtEntry
        match hce : e, hce' : e' with
        | .cacheEvent ce, .cacheEvent ce' =>
          have hordered := b.orderedAtEntry.cache_ordered ce ce' |>.ordered
          simp[CacheEvent.encapsulatedOrOrdered] at hordered
          cases hordered
          . case inl hce_encap_or_before_ce' =>
            exfalso
            apply ce.contradiction_of_ce_ce'_end_at_same_time
            . case he'_e_finish_at_the_same_time => exact he'_e_finish_at_the_same_time
            . case hce_encap_or_before_ce' => exact hce_encap_or_before_ce'
          . case inr hce'_encap_or_before_ce =>
            exfalso
            apply ce'.contradiction_of_ce_ce'_end_at_same_time
            . case he'_e_finish_at_the_same_time =>
              apply Eq.symm
              exact he'_e_finish_at_the_same_time
            . case hce_encap_or_before_ce' => exact hce'_encap_or_before_ce
        | .cacheEvent _, .directoryEvent _
        | .directoryEvent _, .cacheEvent _
        | .directoryEvent _, .directoryEvent _ =>
          simp[Event.atCid] at he_at_cid he'_at_cid

/-- (For SWMR Def. 2.41) Define the set of events that immediately (no intermediate event(s))
end before an event `e` ends. -/
def Behaviour.eventsEndingImmediatelyBefore (b : Behaviour n) (e : Event n) : Set (Event n) :=
  (b.immediateFinishesBeforeAtDifferentCidEvents n e) ∪ {e}

lemma Behaviour.immediateFinishesBeforeEvents_is_subsingleton (b : Behaviour n) (e_succ : Event n)
  : ∀ cid : CacheId n, {e ∈ b.eventsEndingImmediatelyBefore n e_succ | e.atCid n cid}.Subsingleton := by
  simp[eventsEndingImmediatelyBefore]
  simp[Behaviour.immediateFinishesBeforeAtDifferentCidEvents]
  simp only [Set.Subsingleton, Set.mem_setOf_eq,]
  intro cid e he_in_set e' he'_in_set
  have he  := Set.mem_setOf.mp he_in_set
  have he' := Set.mem_setOf.mp he'_in_set
  cases hcases_e : he.left
  . case inl he_eq_e_succ =>
    cases hcases_e' : he'.left
    . case inl he'_eq_e_succ =>
      rw[he_eq_e_succ, he'_eq_e_succ]
    . case inr he'_imm_fin_before =>
      exfalso
      apply contradiction_of_e_succ_eq_e_imm_finishes_before'
      . case he_at_cid => exact he.right
      . case he'_at_cid => exact he'.right
      . case he_eq_e_succ => exact he_eq_e_succ
      . case he'_imm_fin_before => exact he'_imm_fin_before
  . case inr he_imm_fin_before =>
    cases hcases_e' : he'.left
    . case inl he'_eq_e_succ =>
      exfalso
      apply contradiction_of_e_succ_eq_e_imm_finishes_before'
      . case he_at_cid => exact he'.right
      . case he'_at_cid => exact he.right
      . case he_eq_e_succ => exact he'_eq_e_succ
      . case he'_imm_fin_before => exact he_imm_fin_before
    . case inr he'_imm_fin_before =>
      have he_imm := he_imm_fin_before.right
      have he'_imm := he'_imm_fin_before.right
      exfalso
      apply b.contradiction_of_two_events_immediate_finishes_before_successor_event
      . case he_imm => exact he_imm_fin_before.right
      . case he'_imm => exact he'_imm_fin_before.right
      . case he_at_cid => exact he.right
      . case he'_at_cid => exact he'.right
      . case he_in_b => exact he_imm_fin_before.left
      . case he'_in_b => exact he'_imm_fin_before.left

/- Def 2.32 Behaviour.PreviousEvent -/
open scoped Classical in
noncomputable def Behaviour.PreviousEvent (b : Behaviour n) (e : Event n) : Option (Event n) :=
  by classical exact
  -- Not clear how to open up `preds_empty_or_singleton` and use the `empty or singleton` statement inside?
  let preds_empty_or_singleton := b.ImmBottomPredecessors n e
  have h_empty_or_unique := b.immediate_bottom_predecessor_empty_or_unique n e
  if he : preds_empty_or_singleton = ∅ then -- Can't synthesize?
    none
  else
    (h_empty_or_unique.resolve_left he).choose

noncomputable def Set.finSetEvents (es : Set (Event n)) (hes_fin : Finite es) : Finset (Event n) := Set.Finite.toFinset hes_fin

structure Event.isBottomAtEntry (b : Behaviour n) (st : Struct n) (addr : Addr) (e : Event n) where
  addr : e.addr = addr
  atStruct : e.struct = st
  isBottom : b.IsBottomEvent n e

def Behaviour.bottomEventsAtEntry (b : Behaviour n) (addr : Addr) (st : Struct n) : Set (Event n) :=
  {e ∈ b.es | e.isBottomAtEntry n b st addr}

theorem Behaviour.bottomEventsAtEntry_finite (b : Behaviour n) (addr : Addr) (st : Struct n) : Finite (b.bottomEventsAtEntry n addr st) := by
  cases st <;> simp [Behaviour.bottomEventsAtEntry]
  · case directory =>
      have _ : Finite b.es := b.finite
      apply Finite.Set.finite_inter_of_left
  · case cache _ =>
      have _ : Finite b.es := b.finite
      apply Finite.Set.finite_inter_of_left

lemma Behaviour.bottomEventsAtEntry_complete (b : Behaviour n) (addr : Addr) (st : Struct n) :
  ∀ {e : Event n}, (e ∈ b.bottomEventsAtEntry n addr st) ↔ (e ∈ b.es ∧ e.isBottomAtEntry n b st addr) := by
    intro e; constructor <;> exact fun a ↦ a

/- Behaviour bottom events at an entry are totally ordered
lemma Behaviour.bottomEventsAtEntry_totally_ordered (b : Behaviour) (addr : Addr) (st : Struct) (hentry_ordered : Event.AtEntryOrdered) :
  let es := b.bottomEventsAtEntry addr st;
  ∀ e₁ ∈ es, ∀ e₂ ∈ es, e₁.Ordered e₂ := by
  intro es e₁ he₁_in_es e₂ he₂_in_es
  match hst : st with
  | .directory =>
    match he₁ : e₁, he₂ : e₂ with
    | .directoryEvent de₁, .directoryEvent de₂ => exact hentry_ordered.dir_ordered de₁ de₂ |>.ordered
    | .cacheEvent ce, .directoryEvent de =>
      simp[es] at he₁_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₁_in_es he₂_in_es
      have he₁_at_st_dir := he₁_in_es.right.atStruct
      simp[Event.atStruct, Event.isDirectoryEvent, hst] at he₁_at_st_dir
    | .directoryEvent de, .cacheEvent ce =>
      simp[es] at he₂_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₂_in_es he₂_in_es
      have he₂_at_st_dir := he₂_in_es.right.atStruct
      simp[Event.atStruct, Event.isDirectoryEvent, hst] at he₂_at_st_dir
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      simp[es] at he₁_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₁_in_es he₂_in_es
      have he₁_at_st_dir := he₁_in_es.right.atStruct
      simp[Event.atStruct, Event.isDirectoryEvent, hst] at he₁_at_st_dir
  | .cache cid =>
    match he₁ : e₁, he₂ : e₂ with
    | .cacheEvent ce₁, .cacheEvent ce₂ => exact hentry_ordered.cache_ordered ce₁ ce₂ b |>.ordered
    | .directoryEvent de₁, .directoryEvent de₂ =>
      simp[es] at he₁_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₁_in_es he₂_in_es
      have he₁_at_st_dir := he₁_in_es.right.atStruct
      simp[Event.atStruct, Event.isCacheEventAtCid, hst] at he₁_at_st_dir
    | .cacheEvent ce, .directoryEvent de =>
      simp[es] at he₂_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₂_in_es he₂_in_es
      have he₂_at_st_dir := he₂_in_es.right.atStruct
      simp[Event.atStruct, Event.isCacheEventAtCid, hst] at he₂_at_st_dir
    | .directoryEvent de, .cacheEvent ce =>
      simp[es] at he₁_in_es he₂_in_es
      simp[bottomEventsAtEntry] at he₁_in_es he₂_in_es
      have he₁_at_st_dir := he₁_in_es.right.atStruct
      simp[Event.atStruct, Event.isCacheEventAtCid, hst] at he₁_at_st_dir
-/

-- [TODO] Use EventAtEntry to define a total order.
-- Note: because you put the event first it makes this hard to curry...
structure Behaviour.eventAtEntry (b : Behaviour n) (e : Event n) (st : Struct n) (addr : Addr) : Prop where
  eInB : e ∈ b.es
  eAtStruct : e.struct = st
  eAtAddr : e.addr = addr
  -- eBottom : b.IsBottomEvent n e

def EventAtEntry (b : Behaviour n) (st : Struct n) (addr : Addr) : Type :=
  {e : Event n // b.eventAtEntry n e st addr }

instance EventAtEntry.instDecidableEq {b st addr} : DecidableEq (EventAtEntry n b st addr) := by
  simp[DecidableEq]
  intro e₁ e₂
  rw[Subtype.eq_iff]
  infer_instance

/-
instance EventAtEntry.instBEq {b st addr} : BEq (EventAtEntry n b st addr) := by
  constructor
  intro e₁ e₂
  exact e₁.val == e₂.val

instance EventAtEntry.instLawfulBEq {b st addr} : LawfulBEq (EventAtEntry n b st addr) where
  rfl := by
    intro e
    rw[Subtype.beq_iff]
    simp
  eq_of_beq {e₁ e₂ heq} := by
    rw[Subtype.beq_iff] at heq
    rw[Subtype.eq_iff]
    simp at heq
    exact heq

instance EventAtEntry.instEquivBEq {b st addr} [BEq (EventAtEntry n b st addr)] [LawfulBEq (EventAtEntry n b st addr)]
  : EquivBEq (EventAtEntry n b st addr) where
  symm := by
    intro e₁ e₂ heq
    rw[beq_iff_eq]
    simp[] at heq
    rw[Eq.comm]
    exact heq
  trans := by
    intro e₁ e₂ e₃ he₁_eq_e₂ he₂_eq_e₃
    simp_all
  rfl := by
    intro e
    simp
-/
def EventAtEntry.OrderedBefore (b : Behaviour n) (st : Struct n) (addr : Addr)
  (e₁ e₂ : EventAtEntry n b st addr) : Prop := e₁.val.OrderedBefore n e₂.val

def EventAtEntry.encapOrOrderedBefore (b : Behaviour n) (st : Struct n) (addr : Addr)
  (e₁ e₂ : EventAtEntry n b st addr) : Prop := e₁.val.EncapsulatedBy n e₂.val ∨ e₁.val.OrderedBefore n e₂.val

lemma CacheEvent.encapsulate_or_ordered_lift_event {b : Behaviour n} {st : Struct n} {addr : Addr}
  {ce₁ ce₂ : CacheEvent n} {e₁ e₂ : EventAtEntry n b st addr}
  (he₁ : e₁.val = Event.cacheEvent ce₁) (he₂ : e₂.val = Event.cacheEvent ce₂)
  (hce_encap_ordered : CacheEvent.encapsulatedOrOrdered n ce₁ ce₂)
  : EventAtEntry.encapOrOrderedBefore n b st addr e₁ e₂ ∨ EventAtEntry.encapOrOrderedBefore n b st addr e₂ e₁ := by
  dsimp[EventAtEntry.encapOrOrderedBefore]
  rw[he₁, he₂]
  dsimp[Event.EncapsulatedBy, Event.Encapsulates]
  dsimp[Event.OrderedBefore, Event.oEnd, Event.oStart]

  dsimp[encapsulatedOrOrdered, encapsulatedOrBefore] at hce_encap_ordered
  dsimp[EncapsulatedBy, Encapsulates] at hce_encap_ordered
  exact hce_encap_ordered

lemma DirectoryEvent.encapsulate_or_ordered_lift_event {b : Behaviour n} {st : Struct n} {addr : Addr}
  {de₁ de₂ : DirectoryEvent n} {e₁ e₂ : EventAtEntry n b st addr}
  (he₁ : e₁.val = Event.directoryEvent de₁) (he₂ : e₂.val = Event.directoryEvent de₂)
  (hde_ordered : DirectoryEvent.Ordered n de₁ de₂)
  : EventAtEntry.encapOrOrderedBefore n b st addr e₁ e₂ ∨ EventAtEntry.encapOrOrderedBefore n b st addr e₂ e₁ := by

  dsimp[Ordered] at hde_ordered
  dsimp[OrderedBefore] at hde_ordered
  cases hde_ordered
  . case inl hde₁_ordered_de₂ =>
    apply Or.intro_left
    dsimp[EventAtEntry.encapOrOrderedBefore]
    apply Or.intro_right
    rw[he₁, he₂]
    dsimp[Event.OrderedBefore, Event.oEnd, Event.oStart]
    exact hde₁_ordered_de₂
  . case inr hde₂_ordered_de₁ =>
    apply Or.intro_right
    dsimp[EventAtEntry.encapOrOrderedBefore]
    apply Or.intro_right
    rw[he₁, he₂]
    dsimp[Event.OrderedBefore, Event.oEnd, Event.oStart]
    exact hde₂_ordered_de₁

instance EventAtEntry.instIsTotal {n} {b} {st} {addr} :
  IsTotal (EventAtEntry n b st addr) (EventAtEntry.encapOrOrderedBefore n b st addr) := by
  constructor
  intro e₁ e₂
  have h := e₁.val
  match he₁ : e₁.val, he₂ : e₂.val with
  | .cacheEvent ce₁, .cacheEvent ce₂ =>
    have hordered_ce := b.orderedAtEntry.cache_ordered ce₁ ce₂
    have h := hordered_ce.ordered
    dsimp[encapOrOrderedBefore]
    dsimp[CacheEvent.encapsulatedOrOrdered, CacheEvent.encapsulatedOrBefore] at h
    apply CacheEvent.encapsulate_or_ordered_lift_event n he₁ he₂ h
  | .directoryEvent de₁, .directoryEvent de₂ =>
    have hordered_de := b.orderedAtEntry.dir_ordered de₁ de₂
    have h := hordered_de.ordered
    dsimp[encapOrOrderedBefore]
    apply DirectoryEvent.encapsulate_or_ordered_lift_event n he₁ he₂ h
  | .cacheEvent ce₁, .directoryEvent de₂ =>
    have he₁_at_c := e₁.prop.eAtStruct
    have he₂_at_d := e₂.prop.eAtStruct
    rw[he₁] at he₁_at_c
    rw[he₂] at he₂_at_d
    absurd he₁_at_c
    rw[← he₂_at_d]
    simp[Event.struct]
  | .directoryEvent de₁, .cacheEvent ce₂ =>
    have he₁_at_d := e₁.prop.eAtStruct
    have he₂_at_c := e₂.prop.eAtStruct
    rw[he₁] at he₁_at_d
    rw[he₂] at he₂_at_c
    absurd he₁_at_d
    rw[← he₂_at_c]
    simp[Event.struct]

def Behaviour.bottomEventsAtEntry' (b : Behaviour n) (addr : Addr) (st : Struct n) : Set (EventAtEntry n b st addr) :=
  {e : EventAtEntry n b st addr | e.val ∈ b.es ∧ e.val.isBottomAtEntry n b st addr}

lemma Behaviour.bottomEventsAtEntry'_at_cache_all_cache (b : Behaviour n) (addr : Addr) (st : Struct n) (hst_cache : st.atCache)
  : ∀ e ∈ b.bottomEventsAtEntry' n addr st, e.val.isCacheEvent := by
  intro e he_in_bes
  simp [Event.isCacheEvent]
  match h : e.val with
  | .cacheEvent _ => simp
  | .directoryEvent _ =>
    simp[bottomEventsAtEntry'] at he_in_bes
    have he_at_st := he_in_bes.right.atStruct
    simp[Event.struct, h] at he_at_st
    match hst : st with
    | .directory _ => simp[Struct.atCache, hst] at hst_cache
    | .cache _ => simp at he_at_st

lemma Behaviour.bottom_e_in_b_impl_bottomEventsAtEntry' (b : Behaviour n) (st : Struct n) (addr : Addr) (e : Event n)
  (he_in_b : e ∈ b) (he_bottom : b.IsBottomEvent n e) (he_eq_st : e.struct = st) (he_eq_addr : e.addr = addr)
  : ⟨e, ⟨he_in_b, by simp[he_eq_st], by simp[he_eq_addr]⟩⟩ ∈ b.bottomEventsAtEntry' n addr st := by
  simp[bottomEventsAtEntry']
  apply And.intro
  . case left => exact he_in_b
  . case right =>
    constructor
    . case addr => simp[he_eq_addr]
    . case atStruct => simp[he_eq_st]
    . case isBottom => exact he_bottom

lemma Behaviour.bottomEventsAtEntry'_in_b (b : Behaviour n) (addr : Addr) (st : Struct n)
  : ∀ e ∈ b.bottomEventsAtEntry' n addr st, e.val ∈ b := by
  simp[bottomEventsAtEntry']
  intro e he_in_b he_is_bottom
  exact he_in_b

lemma Behaviour.bottomEventsAtEntry'_are_bottom (b : Behaviour n) (addr : Addr) (st : Struct n)
  : ∀ e ∈ b.bottomEventsAtEntry' n addr st, e.val.isBottomAtEntry n b st addr := by
  simp[bottomEventsAtEntry']

noncomputable def Set.finSetEvents' {b} {st} {addr} (es : Set (EventAtEntry n b st addr)) (hes_fin : Finite es) : Finset (EventAtEntry n b st addr) := Set.Finite.toFinset hes_fin

lemma Set.finSetEvents'_e_in_result  {b} {st} {addr} (es : Set (EventAtEntry n b st addr)) (hes_fin : Finite es)
  : ∀ e ∈ Set.finSetEvents' n es hes_fin, e ∈ es := by
  intro e he_in_finset_events
  simp[finSetEvents'] at he_in_finset_events
  exact he_in_finset_events

--https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/How.20to.20prove.20fin.20subtype.20with.20stricter.20restriction.20is.20fin/with/526216387
lemma Subtype.equiv_fin_impl_equiv_fin' {α : Type*} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : {x // p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x // q x} ≃ Fin m) :=
by
  have := Cardinal.mk_subtype_mono himpl
  rw [Cardinal.le_def] at this
  obtain ⟨map, map_inj⟩ := this
  have finite_p : Finite { x // p x } := Finite.of_equiv _ f.symm
  have finite_q : Finite { x // q x } := Finite.of_injective map map_inj
  rw [← Nat.card_eq_of_equiv_fin f]
  exact ⟨
    Nat.card {x // q x},
    Nat.card_le_card_of_injective map map_inj,
    ⟨Finite.equivFin {x // q x}⟩
  ⟩

lemma Subtype.impl_finite {α : Type*} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (hfinite : Finite {x // p x}) : Finite { x // q x} := by
  cases hfinite
  · case intro n fin_equiv =>
    apply finite_iff_exists_equiv_fin.2
    have ⟨m,⟨_, _⟩⟩ := Subtype.equiv_fin_impl_equiv_fin' himpl fin_equiv
    exists m

/-- state the Set of EventAtState from bottom events at an entry is a finite set. -/
theorem Behaviour.bottomEventsAtEntry_finite' (b : Behaviour n) (addr : Addr) (st : Struct n) : Finite (b.bottomEventsAtEntry' n addr st) := by
  have _ : Finite (EventAtEntry n b st addr) := by
    simp [EventAtEntry]
    apply Subtype.impl_finite (p:=fun e => e ∈ b.es) (q:= fun e => eventAtEntry n b e st addr)
    · case himpl =>
      intro e h; exact h.eInB
    · case hfinite => exact b.finite
  apply Subtype.finite

noncomputable def Behaviour.listBottomEventsAtEntry' (b : Behaviour n) (addr : Addr) (st : Struct n) : List (EventAtEntry n b st addr) :=
  let e_at_centry := b.bottomEventsAtEntry' n addr st
  Set.finSetEvents' n e_at_centry (b.bottomEventsAtEntry_finite' n addr st) |>.toList

lemma Behaviour.listBottomEventsAtEntry'_at_cache_all_cache (b : Behaviour n) (addr : Addr) (st : Struct n) (hst_cache : st.atCache)
  : ∀ e ∈ b.listBottomEventsAtEntry' n addr st, e.val.isCacheEvent := by
  simp [listBottomEventsAtEntry']
  simp [Set.finSetEvents']
  apply bottomEventsAtEntry'_at_cache_all_cache
  . case hst_cache => exact hst_cache

lemma Behaviour.bottom_e_in_bottomEventsAtEntry'_impl_in_listBottomEventsAtEntry' (b : Behaviour n) (st : Struct n) (addr : Addr) (e : Event n)
  (he_in_b : e ∈ b) (he_bottom : b.IsBottomEvent n e) (he_eq_st : e.struct = st) (he_eq_addr : e.addr = addr)
  : ⟨e, ⟨he_in_b, by simp[he_eq_st], by simp[he_eq_addr]⟩⟩ ∈ b.listBottomEventsAtEntry' n addr st := by
  simp[listBottomEventsAtEntry']
  simp[Set.finSetEvents']
  apply b.bottom_e_in_b_impl_bottomEventsAtEntry'
  . case he_in_b => exact he_in_b
  . case he_bottom => exact he_bottom
  . case he_eq_st => simp[he_eq_st]
  . case he_eq_addr => simp[he_eq_addr]

def Behaviour.listBottomEventsAtEntry'_no_dups (b : Behaviour n) (addr : Addr) (st : Struct n)
  : b.listBottomEventsAtEntry' n addr st |>.Nodup := by
  simp [listBottomEventsAtEntry']
  simp [Set.finSetEvents']
  simp[Finset.nodup_toList]

lemma Behaviour.listBottomEventsAtEntry'_in_b (b : Behaviour n) (addr : Addr) (st : Struct n)
  : ∀ e ∈ Behaviour.listBottomEventsAtEntry' n b addr st, e.val ∈ b := by
  simp[listBottomEventsAtEntry']
  have h := b.bottomEventsAtEntry'_are_bottom n addr st
  intro e he_in_finsets
  have he_in_bottom : e ∈ bottomEventsAtEntry' n b addr st :=
    Set.finSetEvents'_e_in_result n (b.bottomEventsAtEntry' n addr st) (b.bottomEventsAtEntry_finite' n addr st)
      e he_in_finsets
  apply b.bottomEventsAtEntry'_in_b
  . case a =>
    exact he_in_bottom

lemma Behaviour.listBottomEventsAtEntry'_are_bottom (b : Behaviour n) (addr : Addr) (st : Struct n)
  : ∀ e ∈ Behaviour.listBottomEventsAtEntry' n b addr st, e.val.isBottomAtEntry n b st addr := by
  simp[listBottomEventsAtEntry']
  have h := b.bottomEventsAtEntry'_are_bottom n addr st
  intro e he_in_finsets
  have he_in_bottom : e ∈ bottomEventsAtEntry' n b addr st :=
    Set.finSetEvents'_e_in_result n (b.bottomEventsAtEntry' n addr st) (b.bottomEventsAtEntry_finite' n addr st)
      e he_in_finsets
  apply b.bottomEventsAtEntry'_are_bottom
  . case a =>
    exact he_in_bottom

noncomputable def Behaviour.listBottomEventsAtEntry (b : Behaviour n) (addr : Addr) (st : Struct n) : List (Event n) :=
  let e_at_centry := b.bottomEventsAtEntry n addr st
  Set.finSetEvents n e_at_centry (b.bottomEventsAtEntry_finite n addr st) |>.toList

lemma Behaviour.listBottomEventsAtEntry_complete (b : Behaviour n) (addr : Addr) (st : Struct n) :
  ∀ {e : Event n}, (e ∈ b.listBottomEventsAtEntry n addr st) ↔ (e ∈ b.es ∧ e.isBottomAtEntry n b st addr) := by
  simp [listBottomEventsAtEntry, Event.isBottomAtEntry, Set.finSetEvents]
  intro e; constructor <;> exact fun a ↦ a

def List.isOrdered {α} (l : List α) (r : α → α → Prop): Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

structure Behaviour.BottomPredecessor (b : Behaviour n) (e_pred e_succ : Event n) : Prop where
  sameEntry : Event.sameEntry n e_pred e_succ
  behavePred : Behaviour.Predecessor n b e_pred e_succ
  predBottom : b.IsBottomEvent n e_pred
  succBottom : b.IsBottomEvent n e_succ

instance : DecidableRel (Event.OrderedBefore n) := by
  unfold Event.OrderedBefore
  infer_instance

def Behaviour.sortedListBottomEventsAtEntry (b : Behaviour n) (addr : Addr) (st : Struct n) : Prop := b.listBottomEventsAtEntry n addr st |>.Sorted (b.BottomPredecessor n)

structure Behaviour.sortedListEventsAtEntry : Prop where
  bottom_sorted (b : Behaviour n) (addr : Addr) (st : Struct n) : b.sortedListBottomEventsAtEntry n addr st

def List.sortedListBottomEventsAtEntry (l : List (Event n)) (b : Behaviour n) : Prop := l |>.Sorted (b.BottomPredecessor n)

structure List.sortedListEventsAtEntry : Prop where
  bottom_sorted (l : List (Event n)) (b : Behaviour n) : l.sortedListBottomEventsAtEntry n b

noncomputable def Behaviour.sortedEventsAtEntry' (b : Behaviour n) (addr : Addr) (st : Struct n) : List (Event n) := b.listBottomEventsAtEntry n addr st |>.insertionSort (Event.OrderedBefore n)

instance EventAtEntry.encapOrOrderedBefore.instDecidableRel {b st addr} : DecidableRel (EventAtEntry.encapOrOrderedBefore n b st addr) := by
  simp[DecidableRel]
  intro e₁ e₂
  simp[encapOrOrderedBefore]
  simp[Event.EncapsulatedBy, Event.Encapsulates, Event.OrderedBefore]
  infer_instance

lemma DirectoryEvent.ordered_lift_event {b : Behaviour n} {st : Struct n} {addr : Addr}
  {de₁ de₂ : DirectoryEvent n} {e₁ e₂ : EventAtEntry n b st addr}
  (he₁ : e₁.val = Event.directoryEvent de₁) (he₂ : e₂.val = Event.directoryEvent de₂)
  (hde_ordered : DirectoryEvent.Ordered n de₁ de₂)
  : EventAtEntry.OrderedBefore n b st addr e₁ e₂ ∨ EventAtEntry.OrderedBefore n b st addr e₂ e₁ := by

  dsimp[Ordered] at hde_ordered
  dsimp[OrderedBefore] at hde_ordered
  cases hde_ordered
  . case inl hde₁_ordered_de₂ =>
    apply Or.intro_left
    dsimp[EventAtEntry.OrderedBefore, Event.OrderedBefore]
    rw[he₁, he₂]
    dsimp[Event.OrderedBefore, Event.oEnd, Event.oStart]
    exact hde₁_ordered_de₂
  . case inr hde₂_ordered_de₁ =>
    apply Or.intro_right
    dsimp[EventAtEntry.OrderedBefore, Event.OrderedBefore]
    rw[he₁, he₂]
    dsimp[Event.OrderedBefore, Event.oEnd, Event.oStart]
    exact hde₂_ordered_de₁

instance EventAtEntry.encapOrOrderedBefore.instIsTrans {b st addr} : IsTrans (EventAtEntry n b st addr) (EventAtEntry.encapOrOrderedBefore n b st addr) := by
  constructor
  intro e₁ e₂ e₃
  simp[encapOrOrderedBefore]
  intro he₁_eo_e₂ he₂_eo_e₃
  cases he₁_eo_e₂
  . case trans.inl hencap =>
    cases he₂_eo_e₃
    . case inl hencap₂ =>
      apply Or.intro_left
      calc e₁.val.EncapsulatedBy n e₂.val := hencap
        e₂.val.EncapsulatedBy n e₃.val := hencap₂
    . case inr horder₂ =>
      apply Or.intro_right
      calc e₁.val.EncapsulatedBy n e₂.val := hencap
        e₂.val.OrderedBefore n e₃.val := horder₂
  . case trans.inr horder =>
    cases he₂_eo_e₃
    . case inl he₂_encap_by_e₃ =>
      by_cases e₁.val.oEnd < e₃.val.oStart
      . case pos he₁_o_e₃ =>
        apply Or.intro_right
        exact he₁_o_e₃
      . case neg he₁_may_overlap_e₃ =>
        by_cases e₃.val.oStart < e₁.val.oStart
        . case pos he₃_encap_e₁ =>
          apply Or.intro_left
          apply And.intro
          . case h.left =>
            exact he₃_encap_e₁
          . case h.right =>
            calc e₁.val.oEnd n < e₂.val.oStart n := horder
              _ < e₂.val.oEnd n := e₂.val.oWellFormed
              _ < e₃.val.oEnd n := he₂_encap_by_e₃.right
        . case neg he₁_overlap_e₃ =>
          match he₁ : e₁.val, he₃ : e₃.val with
          | .cacheEvent ce₁, .cacheEvent ce₃ =>
            have hce_ordered := b.orderedAtEntry.cache_ordered ce₁ ce₃ |>.ordered
            simp[CacheEvent.AreOrdered] at hce_ordered
            have he_ordered := CacheEvent.encapsulate_or_ordered_lift_event n he₁ he₃ hce_ordered
            cases he_ordered
            . case inl he₁_eo_e₃ =>
              simp[encapOrOrderedBefore] at he₁_eo_e₃
              rw[← he₁, ← he₃]
              simp[he₁_eo_e₃]
            . case inr he₃_eo_e₁ =>
              simp[encapOrOrderedBefore] at he₃_eo_e₁
              have he₁_lt_e₃_end : e₁.val.oEnd < e₃.val.oEnd := by
                calc e₁.val.oEnd < e₂.val.oStart := horder
                  _ < e₂.val.oEnd := e₂.val.oWellFormed
                  _ < e₃.val.oEnd := he₂_encap_by_e₃.right
              cases he₃_eo_e₁
              . case inl he₃_encap_by_e₁ =>
                simp[Event.OrderedBefore] at horder
                simp[Event.EncapsulatedBy, Event.Encapsulates] at he₃_encap_by_e₁
                have he₃_lt_e₁_end := he₃_encap_by_e₁.right
                absurd he₃_encap_by_e₁.right
                simp
                rw[Nat.le_iff_lt_or_eq]
                apply Or.intro_left
                exact he₁_lt_e₃_end
              . case inr he₃_o_e₁ =>
                absurd he₁_lt_e₃_end
                simp
                rw[Nat.le_iff_lt_or_eq]
                apply Or.intro_left
                simp[Event.OrderedBefore] at he₃_o_e₁
                calc Event.oEnd n e₃.val < Event.oStart n e₁.val := he₃_o_e₁
                  _ < Event.oEnd n e₁.val := e₁.val.oWellFormed
          | .directoryEvent de₁, .directoryEvent de₃ =>
            have hde_ordered := b.orderedAtEntry.dir_ordered de₁ de₃ |>.ordered
            have he_ordered := DirectoryEvent.ordered_lift_event n he₁ he₃ hde_ordered
            cases he_ordered
            . case inl hde₁_o_de₃ =>
              apply Or.intro_right
              simp[EventAtEntry.OrderedBefore,] at hde₁_o_de₃
              rw[← he₁,← he₃]
              simp[hde₁_o_de₃]
            . case inr hde₃_o_de₁ =>
              have he₁_lt_e₃_end : e₁.val.oEnd < e₃.val.oEnd := by
                calc e₁.val.oEnd < e₂.val.oStart := horder
                  _ < e₂.val.oEnd := e₂.val.oWellFormed
                  _ < e₃.val.oEnd := he₂_encap_by_e₃.right
              absurd he₁_lt_e₃_end
              simp
              rw[Nat.le_iff_lt_or_eq]
              apply Or.intro_left
              simp[OrderedBefore] at hde₃_o_de₁
              calc e₃.val.oEnd n < e₁.val.oStart n := hde₃_o_de₁
                _ < e₁.val.oEnd n := e₁.val.oWellFormed
          | .directoryEvent de₁, .cacheEvent ce₃ =>
            have he₁_at_dir := e₁.prop.eAtStruct
            rw[he₁] at he₁_at_dir
            have he₃_at_cache := e₃.prop.eAtStruct
            rw[he₃] at he₃_at_cache
            rw[← he₃_at_cache] at he₁_at_dir
            simp[Event.struct] at he₁_at_dir
          | .cacheEvent ce₁, .directoryEvent de₃ =>
            have he₁_at_cache := e₁.prop.eAtStruct
            rw[he₁] at he₁_at_cache
            have he₃_at_dir := e₃.prop.eAtStruct
            rw[he₃] at he₃_at_dir
            rw[← he₃_at_dir] at he₁_at_cache
            simp[Event.struct] at he₁_at_cache
    . case inr he₂_order_e₃ =>
      apply Or.intro_right
      calc e₁.val.OrderedBefore n e₂.val := horder
        e₂.val.OrderedBefore n e₃.val := he₂_order_e₃

lemma Behaviour.eventsAtCacheEntry_total_order'' (b : Behaviour n) (addr : Addr) (st : Struct n) :
  let bes := b.listBottomEventsAtEntry' n addr st
  let es := bes.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)
  es |>.isOrdered (EventAtEntry.encapOrOrderedBefore n b st addr)
  := by
  intro bes es i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    simp
    apply List.Sorted.rel_get_of_le
    . case h =>
      exact bes.sorted_insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)
    . case hab =>
      simp
      apply Fin.le_of_lt
      exact hi_lt_j
  . case mpr =>
    intro hi_eo_j
    by_contra hneg_i_lt_j
    simp at hneg_i_lt_j
    have hgetj_eo_geti := List.Sorted.rel_get_of_le (bes.sorted_insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)) hneg_i_lt_j
    simp at hgetj_eo_geti
    subst es
    -- hi_eo_j contradict eachother hgetj_eo_geti
    absurd hi_eo_j
    simp
    simp[EventAtEntry.encapOrOrderedBefore, Event.EncapsulatedBy]
    cases hgetj_eo_geti
    . case inl hj_encap_by_i =>
      simp[Event.EncapsulatedBy] at hj_encap_by_i
      apply And.intro
      . case left =>
        dsimp[Event.Encapsulates]
        rw[not_and_or]
        apply Or.intro_left
        have hgeti_lt_getj_start := hj_encap_by_i.left
        simp
        simp[TimeStart]
        rw[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        exact hgeti_lt_getj_start
      . case right =>
        simp[Event.OrderedBefore]
        rw[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hjstart_lt_jend := (List.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr) bes)[j.val].val.oWellFormed
        have hj_lt_i_end := hj_encap_by_i.right
        exact Nat.lt_trans hjstart_lt_jend hj_lt_i_end
    . case inr hj_order_before_i =>
      apply And.intro
      . case left =>
        dsimp[Event.Encapsulates]
        rw[not_and_or]
        apply Or.intro_right
        simp
        rw[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        exact Nat.lt_trans hj_order_before_i (List.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr) bes)[i.val].val.oWellFormed
      . case right =>
        simp[Event.OrderedBefore]
        rw[Nat.le_iff_lt_or_eq]
        apply Or.intro_left
        have hj_start_lt_i_start := Nat.lt_trans (List.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr) bes)[j.val].val.oWellFormed (hj_order_before_i)
        exact Nat.lt_trans hj_start_lt_i_start (List.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr) bes)[i.val].val.oWellFormed

noncomputable def List.stateAfter (es : List (Event n)) (init : (EntryState n)) : EntryState n := match es with
  | [] => init
  | e :: es' => es'.stateAfter (e.SucceedingState n init)

-- def List.upToElement {α} [BEq α] (l : List α) (e : α) := (l.take (l.idxOf e))
/-- Get the list of events from the head upto (excluding) e. -/
def List.upToEvent (es : List (Event n)) (e : Event n) := (es.take (es.idxOf e))

noncomputable def List.stateAtEvent (es : List (Event n)) (e : Event n) (init : EntryState n) : EntryState n :=
  List.stateAfter n (es.upToEvent n e) init

noncomputable def Behaviour.eventsAtEntryOfListBottomEvents (b : Behaviour n) (st : Struct n) (addr : Addr) : List (EventAtEntry n b st addr) :=
  b.listBottomEventsAtEntry' n addr st |>.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)

lemma Behaviour.eventsAtEntryOfListBottomEvents_at_cache_all_cache (b : Behaviour n) (addr : Addr) (st : Struct n) (hst_cache : st.atCache)
  : ∀ e ∈ b.eventsAtEntryOfListBottomEvents n st addr, e.val.isCacheEvent := by
  simp[eventsAtEntryOfListBottomEvents]
  apply listBottomEventsAtEntry'_at_cache_all_cache
  . case hst_cache => exact hst_cache

lemma Behaviour.eventsAtEntryOfListBottomEvents_sorted (b : Behaviour n) (struct : Struct n) (addr : Addr) :
  (b.eventsAtEntryOfListBottomEvents n struct addr).Sorted (EventAtEntry.encapOrOrderedBefore n b struct addr) := by
  simp[eventsAtEntryOfListBottomEvents]
  simp[List.sorted_insertionSort]

instance EventAtEntry.encapOrOrderedBefore.instIsIrrefl {b st addr} : IsIrrefl (EventAtEntry n b st addr) (EventAtEntry.encapOrOrderedBefore n b st addr) :=
  by
  constructor
  . case irrefl =>
    intro e hencap_or_order_before
    simp[encapOrOrderedBefore] at hencap_or_order_before
    cases hencap_or_order_before
    . case inl hencap_by =>
      simp[Event.EncapsulatedBy, Event.Encapsulates] at hencap_by
    . case inr horder_before =>
      simp[Event.OrderedBefore] at horder_before
      have hstart_lt_end := e.val.oWellFormed
      absurd hstart_lt_end
      simp
      rw[Nat.le_iff_lt_or_eq]
      simp[horder_before]

lemma Behaviour.eventsAtEntryOfListBottomEvents_no_dups (b : Behaviour n) (struct : Struct n) (addr : Addr)
  : b.eventsAtEntryOfListBottomEvents n struct addr |>.Nodup := by
  have hsorted := b.eventsAtEntryOfListBottomEvents_sorted n struct addr
  apply List.Sorted.nodup hsorted

lemma Behaviour.bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents (b : Behaviour n) (st : Struct n) (addr : Addr) (e : Event n)
  (he_in_b : e ∈ b) (he_bottom : b.IsBottomEvent n e) (he_eq_st : e.struct = st) (he_eq_addr : e.addr = addr)
  -- (he_in_bottom_es : ⟨e, ⟨he_in_b, by simp, by simp⟩⟩ ∈ b.listBottomEventsAtEntry' n e.addr e.struct)
  : ⟨e, ⟨he_in_b, by simp[he_eq_st], by simp[he_eq_addr]⟩⟩ ∈ b.eventsAtEntryOfListBottomEvents n st addr := by
  simp[eventsAtEntryOfListBottomEvents]
  apply b.bottom_e_in_bottomEventsAtEntry'_impl_in_listBottomEventsAtEntry'
  . case he_in_b => exact he_in_b
  . case he_bottom => exact he_bottom
  . case he_eq_st => simp[he_eq_st]
  . case he_eq_addr => simp[he_eq_addr]

lemma Behaviour.eventsAtEntryOfListBottomEvents_in_b (b : Behaviour n) (st : Struct n) (addr : Addr) :
  ∀ e' ∈ b.eventsAtEntryOfListBottomEvents n st addr, e'.val ∈ b := by
  intro e' he'_in_bottom
  simp[eventsAtEntryOfListBottomEvents] at he'_in_bottom

  apply b.listBottomEventsAtEntry'_in_b
  . case a =>
    exact he'_in_bottom

lemma Behaviour.eventsAtEntryOfListBottomEvents_are_bottom (b : Behaviour n) (st : Struct n) (addr : Addr) :
  ∀ e' ∈ b.eventsAtEntryOfListBottomEvents n st addr, e'.val.isBottomAtEntry n b st addr := by
  intro e' he'_in_bottom
  simp[eventsAtEntryOfListBottomEvents] at he'_in_bottom
  apply b.listBottomEventsAtEntry'_are_bottom
  . case a =>
    exact he'_in_bottom

lemma Behaviour.bottomEventsAtEntry_sorted_ordered_before {st addr} {b : Behaviour n} {l : List (EventAtEntry n b st addr)}
  (h_all_bottom : ∀ e ∈ l, e.val.isBottomAtEntry n b st addr)
  (hsorted : l.Sorted (EventAtEntry.encapOrOrderedBefore n b st addr))
  : l.Sorted (EventAtEntry.OrderedBefore n b st addr) := by
  simp_all[List.Sorted,]
  unfold EventAtEntry.encapOrOrderedBefore at hsorted
  rw [List.pairwise_iff_forall_sublist] at hsorted
  rw [List.pairwise_iff_forall_sublist]
  intro e₁ e₂ h_sublist_l
  cases hsorted h_sublist_l
  . case inl he₁_encap_by_e₂ =>
    -- not possible, since they're bottom events.
    simp[Event.EncapsulatedBy] at he₁_encap_by_e₂
    have he₁_in_l : e₁ ∈ l := List.mem_of_cons_sublist h_sublist_l
    have he₁_bot := h_all_bottom e₁ he₁_in_l
    have he₁_is_bot := he₁_bot.isBottom
    simp[IsBottomEvent, IsNotEncapAtSameStruct,] at he₁_is_bot
    have he₁e₂_encap_same_entry := he₁_is_bot e₂.val e₂.prop.eInB
    exfalso
    apply he₁e₂_encap_same_entry
    constructor
    . case encap =>
      exact he₁_encap_by_e₂
    . case sameEntry =>
      constructor
      . case sameStruct =>
        simp [Event.sameStructure]
        simp[e₁.prop.eAtStruct, e₂.prop.eAtStruct]
      . case sameAddr =>
        simp [Event.sameAddr]
        simp[e₁.prop.eAtAddr, e₂.prop.eAtAddr]
  . case inr he₁_ordered_before_e₂ =>
    simp[EventAtEntry.OrderedBefore]
    exact he₁_ordered_before_e₂

lemma Behaviour.eventsAtEntryOfListBottomEvents_map_ordered_before_sorted (b : Behaviour n) (struct : Struct n) (addr : Addr)
  : (b.eventsAtEntryOfListBottomEvents n struct addr).Sorted (EventAtEntry.OrderedBefore n b struct addr) := by
  apply b.bottomEventsAtEntry_sorted_ordered_before
  . case h_all_bottom =>
    apply b.eventsAtEntryOfListBottomEvents_are_bottom n struct addr
  . case hsorted =>
    exact b.eventsAtEntryOfListBottomEvents_sorted n struct addr

noncomputable def Behaviour.eventsAtEventEntry (b : Behaviour n) (e : Event n) : List (Event n) :=
  b.eventsAtEntryOfListBottomEvents n e.struct e.addr |>.map (·.val)

lemma Behaviour.eventsAtEventEntry_at_cache_all_cache (b : Behaviour n) (e : Event n) (he_cache : e.isCacheEvent)
  : ∀ e' ∈ b.eventsAtEventEntry n e, e'.isCacheEvent := by
  simp[eventsAtEventEntry]
  apply eventsAtEntryOfListBottomEvents_at_cache_all_cache
  . case hst_cache =>
    simp[Event.struct]
    match e with
    | .cacheEvent _ => simp[Struct.atCache]
    | .directoryEvent _ => simp[Event.isCacheEvent] at he_cache

/-
lemma Behaviour.eventsAtEntryOfListBottomEvents_eq_same_entry (b : Behaviour n) (e₁ e₂ : Event n)
  (hsame_struct : e₁.struct n = e₂.struct n)
  (hsame_addr : e₁.addr n = e₂.addr n)
  : b.eventsAtEntryOfListBottomEvents n e₁.struct e₁.addr = b.eventsAtEntryOfListBottomEvents n e₂.struct e₂.addr := by
  simp[eventsAtEventEntry, eventsAtEntryOfListBottomEvents]
  have hsame_addr := hsame_entry.sameAddr
  have hsame_struct := hsame_entry.sameStruct
  simp[Event.sameAddr] at hsame_addr
  simp[Event.sameStructure] at hsame_struct
  rw [hsame_addr]
  rw [hsame_struct]
-/

structure Behaviour.listImmediateBottomPred (b : Behaviour n)
  (l : List (Event n)) (e_pred e_succ : Event n) where
  sameEntry : e_pred.sameEntry n e_succ
  noIntermediate : List.idxOf e_succ l = List.idxOf e_pred l + 1
  isBottomPred : b.IsBottomEvent n e_pred
  isBottomSucc : b.IsBottomEvent n e_succ
  predInB : e_pred ∈ b
  succInB : e_succ ∈ b

structure Behaviour.listImmediateBottomPredAtEntry {st addr} (b : Behaviour n)
  (l : List (EventAtEntry n b st addr)) (e_pred e_succ : EventAtEntry n b st addr) where
  -- behavePred : Behaviour.Predecessor n b e_pred e_succ
  noIntermediate : List.idxOf e_pred l + 1 = List.idxOf e_succ l
  isBottom : b.IsBottomEvent n e_pred.val

lemma Event.same_entry_impl_same_addr (e₁ e₂ : Event n) (hsame_entry : e₁.sameEntry n e₂)
  : Event.addr n e₁ = Event.addr n e₂ := by
  have hsame_addr := hsame_entry.sameAddr
  simp[Event.sameAddr] at hsame_addr
  simp[hsame_addr]

lemma Event.same_entry_impl_same_struct (e₁ e₂ : Event n) (hsame_entry : e₁.sameEntry n e₂)
  : Event.struct n e₁ = Event.struct n e₂ := by
  have hsame_struct := hsame_entry.sameStruct
  simp[Event.sameStructure] at hsame_struct
  simp[hsame_struct]

lemma List.idxOf_n_one_lt_idxOf_m_impl_intermediate' {α} [DecidableEq α]
  {l : List α} {n m : α} (hnodup : l.Nodup)
  (hn_in_l : idxOf n l < l.length) (hm_in_l : idxOf m l < l.length)
  (hidxn_one_lt_idxm : idxOf n l + 1 < idxOf m l)
  : ∃ e ∈ l, (idxOf e l = idxOf n l + 1) := by
  by_contra hexists_elem
  simp at hexists_elem
  let helem := l[idxOf n l + 1]
  have helem_in_l : helem ∈ l := by simp[helem]
  have helem_not_idxn_one := hexists_elem helem helem_in_l
  simp[helem,] at helem_not_idxn_one
  rw[List.idxOf_getElem] at helem_not_idxn_one
  apply helem_not_idxn_one
  rfl
  . case H => exact hnodup

lemma List.idxOf_n_one_lt_idxOf_m_impl_intermediate {α} {r : α → α → Prop} [DecidableEq α]
  (l : List α) (n m : α) (hsorted : l.Sorted r) (hnodup : l.Nodup)
  (hn_in_l : idxOf n l < l.length) (hm_in_l : idxOf m l < l.length)
  (hidxn_one_lt_idxm : idxOf n l + 1 < idxOf m l)
  : ∃ p ∈ l, r n p ∧ r p m := by
  by_contra hinter
  simp at hinter
  have helem : ∃ e ∈ l, (idxOf e l = idxOf n l + 1) := List.idxOf_n_one_lt_idxOf_m_impl_intermediate' hnodup hn_in_l hm_in_l hidxn_one_lt_idxm
  have hidxn_lt_idxelem : idxOf n l < idxOf helem.choose l := by simp[helem.choose_spec]
  have hidxelem_lt_idxm : idxOf helem.choose l < idxOf m l := by simp[helem.choose_spec, hidxn_one_lt_idxm]
  have hn_lt_elem : r n helem.choose := by
    simp[List.Sorted, List.pairwise_iff_getElem] at hsorted
    have helem_lt_len : idxOf helem.choose l < l.length := List.idxOf_lt_length_of_mem helem.choose_spec.left
    have horder := hsorted (idxOf n l) (idxOf helem.choose l) hn_in_l helem_lt_len hidxn_lt_idxelem
    simp[List.idxOf_getElem,] at horder
    exact horder
  have helem_lt_m : r helem.choose m := by
    simp[List.Sorted] at hsorted
    simp[List.pairwise_iff_getElem] at hsorted
    have helem_lt_len : idxOf helem.choose l < l.length := List.idxOf_lt_length_of_mem helem.choose_spec.left
    have horder := hsorted (idxOf helem.choose l) (idxOf m l) helem_lt_len hm_in_l hidxelem_lt_idxm
    simp[List.idxOf_getElem,] at horder
    exact horder
  have hcontra := hinter helem.choose helem.choose_spec.left hn_lt_elem
  absurd hcontra
  simp[helem_lt_m]

lemma List.contradiction_of_idxOf_imm_pred_eq_idxOf {α} [DecidableEq α] (l : List α) (n m : α)
  (hn_lt_len : idxOf n l < l.length)
  (hm_lt_len : idxOf m l < l.length)
  (hn_ne_m : n ≠ m) (hm_eq_n : idxOf m l = idxOf n l) : False := by
  have hgetelem_eq : l[idxOf m l] = l[idxOf n l] := by simp[hm_eq_n]
  have heq : m = n := by simp[List.idxOf_getElem] at hgetelem_eq ; exact hgetelem_eq
  absurd heq
  simp[Eq.comm, hn_ne_m]

lemma Behaviour.listBottomEventsAtEntry'_imm_pred_equiv
  {b : Behaviour n} (st : Struct n) (addr : Addr)
  (l : List (EventAtEntry n b st addr))

  (e_pred e : Event n) (hpred_in_b : e_pred ∈ b) (he_in_b : e ∈ b)
  (hpred_at_st : e_pred.struct = st) (hpred_at_addr : e_pred.addr = addr)
  (he_at_st : e.struct = st) (he_at_addr : e.addr = addr)

  (hall_in_b : ∀ e' ∈ l, e'.val ∈ b)
  (hall_bottom : ∀ e' ∈ l, e'.val.isBottomAtEntry n b st addr)

  (hsorted : l.Sorted (EventAtEntry.OrderedBefore n b st addr))
  (hnodup : l.Nodup)

  (e_pred_at : EventAtEntry n b st addr)
  (e_at      : EventAtEntry n b st addr)

  (he_pred : e_pred_at = ⟨e_pred, ⟨hpred_in_b, by simp[hpred_at_st], by simp[hpred_at_addr]⟩⟩)
  (he      : e_at = ⟨e, ⟨he_in_b, by simp[he_at_st], by simp[he_at_addr]⟩⟩)

  (hpred_lt_length : List.idxOf e_pred_at l < l.length)
  (he_lt_length : List.idxOf e_at l < l.length)

  (hb_imm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  :
    b.listImmediateBottomPredAtEntry n l
    e_pred_at
    e_at :=
  by
  constructor
  . case noIntermediate =>
    by_contra hnot_imm
    simp only [Nat.eq_iff_le_and_ge, not_and_or, Nat.not_le] at hnot_imm
    cases hnot_imm
    . case inl he_lt_pred_one =>
      /- Sorted means entries are ordered by Ordered Before. -/
      have hpred_to_e := hb_imm_bot_pred.isImmPred.isPred
      simp[Event.Predecessor, Event.OrderedBefore] at hpred_to_e
      have hpred_to_e_at : e_pred_at.val.oEnd < e_at.val.oStart := by simp[he_pred, he, hpred_to_e]

      simp[List.Sorted] at hsorted
      simp[List.pairwise_iff_getElem] at hsorted

      have hidx_e_lt_pred : List.idxOf e_at l < List.idxOf e_pred_at l := by
        rw[Nat.add_comm] at he_lt_pred_one
        rw[Nat.lt_one_add_iff] at he_lt_pred_one
        simp[Nat.le_iff_lt_or_eq] at he_lt_pred_one
        cases he_lt_pred_one
        . case inl hidxe_lt_idxpred => exact hidxe_lt_idxpred
        . case inr hidxe_eq_idxpred =>
          have hpred_ne_e : e_pred_at ≠ e_at := by
            have hpred_ob_e := hb_imm_bot_pred.isImmPred.isPred
            simp[Event.Predecessor, Event.OrderedBefore] at hpred_ob_e
            intro he_pred_eq_e
            have hpred_end_eq_e_end : e_pred_at.val.oEnd = e_at.val.oEnd := by rw [he_pred_eq_e];
            simp[he_pred, he] at hpred_end_eq_e_end
            rw[hpred_end_eq_e_end] at hpred_ob_e
            have hend_lt_end : e.oEnd < e.oEnd := by
              calc e.oEnd < e.oStart := hpred_ob_e
                _ < e.oEnd := e.oWellFormed
            simp at hend_lt_end
          exfalso
          apply l.contradiction_of_idxOf_imm_pred_eq_idxOf e_pred_at e_at hpred_lt_length he_lt_length hpred_ne_e hidxe_eq_idxpred

      have he_ob_pred := hsorted
        (List.idxOf e_at l)
        (List.idxOf e_pred_at l)
        he_lt_length hpred_lt_length
        hidx_e_lt_pred

      rw[List.getElem_idxOf (a:=e_pred_at) (l:=l) hpred_lt_length] at he_ob_pred
      rw[List.getElem_idxOf (a:=e_at) (l:=l) he_lt_length] at he_ob_pred

      simp[EventAtEntry.OrderedBefore] at he_ob_pred
      absurd he_ob_pred
      simp[Event.OrderedBefore]
      simp[Nat.le_iff_lt_or_eq]
      apply Or.intro_left
      simp [Event.OrderedBefore] at he_ob_pred
      calc e_pred_at.val.oStart < e_pred_at.val.oEnd := e_pred_at.val.oWellFormed
        _ < e_at.val.oStart := hpred_to_e_at
        _ < e_at.val.oEnd := e_at.val.oWellFormed
    . case inr hpred_lt_e_one =>
      have hintermediate : ∃ e_inter ∈ l, e_pred_at.OrderedBefore n b st addr e_inter ∧ e_inter.OrderedBefore n b st addr e_at :=
        List.idxOf_n_one_lt_idxOf_m_impl_intermediate l e_pred_at e_at hsorted hnodup hpred_lt_length he_lt_length hpred_lt_e_one
      absurd hintermediate
      simp
      intro x_at hx_in_l hpred_ob_x
      have hnot_intermediate := hb_imm_bot_pred.isImmPred.noIntermediate
      simp[NoIntermediatePredecessor] at hnot_intermediate
      simp[EventAtEntry.OrderedBefore]
      have hx_bottom_at := hall_bottom x_at hx_in_l
      have hbottom_same_entry : b.bottomSameEntry n x_at.val e := by
        constructor
        . case sameEntry =>
          constructor
          . case sameStruct => simp[Event.sameStructure, he_at_st, hx_bottom_at.atStruct]
          . case sameAddr => simp[Event.sameAddr, he_at_addr, hx_bottom_at.addr]
        . case isBottom => simp[hx_bottom_at.isBottom]
      have hno_order_between := hnot_intermediate x_at.val (hall_in_b x_at hx_in_l) hbottom_same_entry
      intro hx_ob_e
      apply hno_order_between
      constructor
      simp[autoParam]
      . case pred => /- List is sorted, so e_pred is before x_at -/
        simp[EventAtEntry.OrderedBefore, he_pred] at hpred_ob_x
        simp[hpred_ob_x]
      . case succ =>
        simp[he] at hx_ob_e
        simp[autoParam, hx_ob_e]
  . case isBottom => simp[he_pred, hb_imm_bot_pred.isBottomPred]

lemma Behaviour.eventsAtEventEntry_are_bottom (b : Behaviour n) (e : Event n)
  : ∀ e' ∈ b.eventsAtEventEntry n e, e'.isBottomAtEntry n b e.struct e.addr := by
  simp[eventsAtEventEntry]
  intro e' he'_in_es_at_entry
  apply eventsAtEntryOfListBottomEvents_are_bottom
  . case a => exact he'_in_es_at_entry

lemma Behaviour.bottom_e_in_b_impl_in_eventsAtEventEntry (b : Behaviour n) (e : Event n)
  (he_in_b : e ∈ b) (he_bottom : b.IsBottomEvent n e)
  : e ∈ b.eventsAtEventEntry n e := by
  simp[eventsAtEventEntry]
  apply Exists.intro
  apply And.intro
  . case h.left =>
    apply Behaviour.bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents
    . case he_in_b => exact he_in_b
    . case he_bottom => exact he_bottom
    . case he_eq_st => rfl
    . case he_eq_addr => rfl
  . case h.right => simp

lemma List.sublist_tail_mem {α} {x₁ x₂ : α} {l} : [x₁, x₂].Sublist l → x₂ ∈ l := by
  intro hsublist_l
  have hx₂_sublist_l : [x₂].Sublist l := List.sublist_of_cons_sublist hsublist_l
  simp at hx₂_sublist_l
  exact hx₂_sublist_l

lemma Behaviour.eventsAtEventEntry_at_e_entry (b : Behaviour n) (e : Event n) :
  ∀ e' ∈ b.eventsAtEventEntry n e, b.eventAtEntry n e' e.struct e.addr := by
  intro e' he'_at_entry
  simp[eventsAtEventEntry] at he'_at_entry
  obtain ⟨e_at_entry, hin_es_and_is_e'⟩ := he'_at_entry
  obtain ⟨he_in_es, he_is_e'⟩ := hin_es_and_is_e'
  subst he_is_e'
  constructor
  . case intro.intro.eInB =>
    exact e_at_entry.prop.eInB
  . case intro.intro.eAtStruct =>
    exact e_at_entry.prop.eAtStruct
  . case intro.intro.eAtAddr =>
    exact e_at_entry.prop.eAtAddr

instance EventAtEntry.instGetValInjective {b st addr} : Function.Injective (λ e : EventAtEntry n b st addr => e.val) := by
  simp[Function.Injective]
  intro e₁ e₂ he₁_eq_e₂
  apply Subtype.eq
  exact he₁_eq_e₂

lemma Behaviour.eventsAtEventEntry_no_dups (b : Behaviour n) (e : Event n)
  : b.eventsAtEventEntry n e |>.Nodup := by
  simp[eventsAtEventEntry]
  rw [List.nodup_map_iff]
  . exact b.eventsAtEntryOfListBottomEvents_no_dups n e.struct e.addr
  . exact EventAtEntry.instGetValInjective n

lemma Behaviour.eventsAtEventEntry_sublist_impl_eventsAtEntryOfListBottomEvents {b e}
  {e₁ e₂ : Event n} (he₁_at_e : b.eventAtEntry n e₁ e.struct e.addr) (he₂_at_e : b.eventAtEntry n e₂ e.struct e.addr)
  : [e₁, e₂].Sublist (eventsAtEventEntry n b e) → [⟨e₁, he₁_at_e⟩, ⟨e₂, he₂_at_e⟩].Sublist (eventsAtEntryOfListBottomEvents n b e.struct e.addr) := by
  simp[eventsAtEventEntry]
  simp[List.sublist_map_iff]
  intro he_at_entry he_at_entry_sublist he_is_sublist
  cases he_at_entry
  . case nil => simp at he_is_sublist
  . case cons head tail =>
    by_cases hhead_good : head = ⟨e₁, he₁_at_e⟩
    . case pos =>
      cases tail
      . case nil => simp at he_is_sublist
      . case cons head' tail' =>
        by_cases hhead'_good : head' = ⟨e₂, he₂_at_e⟩
        . case pos =>
          subst head head'
          cases tail'
          . case nil => exact he_at_entry_sublist
          . case cons head'' tail'' => simp at he_is_sublist
        . case neg =>
          subst head
          simp at he_is_sublist
          have he₂_not_head' : e₂ ≠ head'.val := by
            simp [hhead'_good]
            by_contra h_e₂_is_head
            apply hhead'_good
            subst h_e₂_is_head
            simp
          absurd he₂_not_head'
          exact he_is_sublist.left
    . case neg =>
      simp at he_is_sublist
      have he₁_not_head : e₁ ≠ head.val := by
        simp [hhead_good]
        by_contra h_e₁_is_head
        apply hhead_good
        subst h_e₁_is_head
        simp
      absurd he₁_not_head
      exact he_is_sublist.left

lemma Behaviour.eventsAtEventEntry_ordered_before_sorted (b : Behaviour n) (e : Event n)
  : (b.eventsAtEventEntry n e).Sorted (Event.OrderedBefore n) := by
  simp[List.Sorted]
  rw[List.pairwise_iff_forall_sublist]
  intro e₁ e₂ hsublist
  have he₁_in_es_at_entry : e₁ ∈ eventsAtEventEntry n b e := List.mem_of_cons_sublist hsublist
  have he₁_at_entry : b.eventAtEntry n e₁ e.struct e.addr := b.eventsAtEventEntry_at_e_entry n e e₁ he₁_in_es_at_entry
  have he₂_in_es_at_entry : e₂ ∈ eventsAtEventEntry n b e := List.sublist_tail_mem hsublist
  have he₂_at_entry : b.eventAtEntry n e₂ e.struct e.addr := b.eventsAtEventEntry_at_e_entry n e e₂ he₂_in_es_at_entry

  have hbottom_sorted := b.eventsAtEntryOfListBottomEvents_map_ordered_before_sorted n e.struct e.addr
  simp[List.Sorted] at hbottom_sorted
  simp[List.pairwise_iff_forall_sublist] at hbottom_sorted
  have he_at_entry_sublist := b.eventsAtEventEntry_sublist_impl_eventsAtEntryOfListBottomEvents n he₁_at_entry he₂_at_entry hsublist
  have he_at_entry_ordered_before := hbottom_sorted he_at_entry_sublist
  simp[EventAtEntry.OrderedBefore] at he_at_entry_ordered_before
  exact he_at_entry_ordered_before

-- def GenericSubtype {β : Type} {p : β → Prop} : Type := {x : β // p x}

lemma List.idxOf_subtype_eq_idxOf_subtype_val {b st addr}
  (l : List (EventAtEntry n b st addr)) (n : (EventAtEntry n b st addr)) : idxOf n l = idxOf n.val (l.map (·.val)) := by
  induction l with
  | nil => simp
  | cons head rest ih =>
    simp only [List.idxOf_cons]
    by_cases hhead_is_n : head == n
    . case pos =>
      have hval_eq : head.val = n.val := by
        simp at hhead_is_n
        simp[hhead_is_n]
      simp[hhead_is_n, hval_eq]
    . case neg =>
      have hval_neq : ¬ head.val == n.val := by
        simp at hhead_is_n
        simp[hhead_is_n,]
        rw[← Subtype.eq_iff,]
        simp[hhead_is_n]
      simp only [map_cons, idxOf_cons, ]
      simp only [hval_neq, hhead_is_n, cond_false]
      simp only [ih]

lemma List.test {b st addr} (e : EventAtEntry n b st addr) (l : List (EventAtEntry n b st addr)) : idxOf e l = idxOf e.val (l.map (·.val)) := by
  have h := idxOf_subtype_eq_idxOf_subtype_val n l e
  exact h

lemma Behaviour.eventsAtEventEntry_imm_pred_equiv
  {b : Behaviour n} (st : Struct n) (addr : Addr)

  {e_pred e : Event n} (hpred_in_b : e_pred ∈ b) (he_in_b : e ∈ b)
  (hpred_at_st : e_pred.struct = st) (hpred_at_addr : e_pred.addr = addr)
  (he_at_st : e.struct = st) (he_at_addr : e.addr = addr)

  (hb_imm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  :
    b.listImmediateBottomPred n (b.eventsAtEventEntry n e)
    e_pred
    e :=
  by

  have hpred_at_e_struct := hb_imm_bot_pred.isImmPred.bPred.sameEntry.sameStruct
  simp[Event.sameStructure] at hpred_at_e_struct
  have hpred_at_e_addr := hb_imm_bot_pred.isImmPred.bPred.sameEntry.sameAddr
  simp[Event.sameAddr] at hpred_at_e_addr

  have he_at_e_struct : e.struct = e.struct := by rfl
  have he_at_e_addr : e.addr = e.addr := by rfl

  have he_in_l_in_b := b.eventsAtEntryOfListBottomEvents_in_b n st addr
  have he_in_l_bottom := b.eventsAtEntryOfListBottomEvents_are_bottom n st addr

  have hentry_es_sorted := b.eventsAtEntryOfListBottomEvents_map_ordered_before_sorted n st addr
  have hentry_es_nodup := b.eventsAtEntryOfListBottomEvents_no_dups n st addr

  let e_pred_at : EventAtEntry n b st addr := ⟨e_pred,⟨hb_imm_bot_pred.isImmPred.predInB, hpred_at_st, hpred_at_addr⟩⟩
  let e_at      : EventAtEntry n b st addr := ⟨e,⟨he_in_b,he_at_st,he_at_addr⟩⟩

  have he_pred : e_pred_at = ⟨e_pred,⟨hb_imm_bot_pred.isImmPred.predInB, hpred_at_st, hpred_at_addr⟩⟩ := by simp[e_pred_at]
  have he      : e_at      = ⟨e,⟨he_in_b, he_at_st, he_at_addr⟩⟩ := by simp[e_at]

  have hpred_in_l := b.bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents n st addr e_pred hb_imm_bot_pred.isImmPred.predInB hb_imm_bot_pred.isBottomPred hpred_at_st hpred_at_addr
  have he_in_l := b.bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents n st addr e he_in_b hb_imm_bot_pred.isBottomSucc he_at_st he_at_addr

  have hidxOf_pred_in_l := List.idxOf_lt_length_of_mem hpred_in_l
  have hidxOf_e_in_l := List.idxOf_lt_length_of_mem he_in_l
  have hlist_bottom_pred_at := b.listBottomEventsAtEntry'_imm_pred_equiv n st addr
    (b.eventsAtEntryOfListBottomEvents n st addr)
    e_pred e
    hpred_in_b he_in_b hpred_at_st hpred_at_addr
    he_at_st he_at_addr he_in_l_in_b he_in_l_bottom
    hentry_es_sorted hentry_es_nodup
    e_pred_at e_at
    he_pred he
    hidxOf_pred_in_l hidxOf_e_in_l
    hb_imm_bot_pred
  constructor
  . case sameEntry => exact hb_imm_bot_pred.isImmPred.bPred.sameEntry
  . case noIntermediate =>
    apply Eq.symm
    have h := hlist_bottom_pred_at.noIntermediate
    simp[eventsAtEventEntry]
    rw[List.idxOf_subtype_eq_idxOf_subtype_val n (eventsAtEntryOfListBottomEvents n b st addr) e_pred_at] at h
    rw[List.idxOf_subtype_eq_idxOf_subtype_val n (eventsAtEntryOfListBottomEvents n b st addr) e_at] at h
    simp[he_pred, he] at h

    rw[he_at_st]
    rw[he_at_addr]
    exact h
  . case isBottomPred => exact hb_imm_bot_pred.isBottomPred
  . case isBottomSucc => exact hb_imm_bot_pred.isBottomSucc
  . case predInB => exact hb_imm_bot_pred.isImmPred.predInB
  . case succInB => exact he_in_b

noncomputable def Behaviour.eventsUpToEvent (b : Behaviour n) (e : Event n) : List (Event n) :=
  b.eventsAtEventEntry n e |>.upToEvent n e

lemma Behaviour.eventsUpToEvent_at_cache_all_cache (b : Behaviour n) (e : Event n) (he_cache : e.isCacheEvent)
  : ∀ e' ∈ b.eventsUpToEvent n e, e'.isCacheEvent := by
  simp[eventsUpToEvent]
  simp[List.upToEvent]
  intro e' he'_in_l
  have he'_in_es_at_entry := List.mem_of_mem_take he'_in_l
  apply eventsAtEventEntry_at_cache_all_cache
  . case he_cache => exact he_cache
  . case a => exact he'_in_es_at_entry

lemma Behaviour.eventsUpToEvent_are_bottom (b : Behaviour n) (e : Event n)
  : ∀ e' ∈ b.eventsUpToEvent n e, e'.isBottomAtEntry n b e.struct e.addr := by
  simp[eventsUpToEvent]
  simp[List.upToEvent]
  intro e' he'_in_es_upto_event
  apply b.eventsAtEventEntry_are_bottom n e
  . case a => exact List.mem_of_mem_take he'_in_es_upto_event

lemma Behaviour.eventsUpToEvent_no_dups (b : Behaviour n) (e : Event n)
  : b.eventsUpToEvent n e |>.Nodup := by
  simp[eventsUpToEvent]
  simp[List.upToEvent]
  apply List.Nodup.sublist
  . case a => exact List.take_sublist (List.idxOf e (eventsAtEventEntry n b e)) (eventsAtEventEntry n b e)
  . case a => exact b.eventsAtEventEntry_no_dups n e

lemma Behaviour.eventsUpToEntry_at_e_entry (b : Behaviour n) (e : Event n) :
  ∀ e' ∈ b.eventsUpToEvent n e, b.eventAtEntry n e' e.struct e.addr := by
  intro e' he'_in_up_to
  apply eventsAtEventEntry_at_e_entry
  . case a =>
    simp[eventsUpToEvent] at he'_in_up_to
    simp[List.upToEvent] at he'_in_up_to
    apply List.mem_of_mem_take
    . case h =>
      exact he'_in_up_to

lemma Behaviour.eventsAtEventEntry_eq_same_entry (b : Behaviour n) (e₁ e₂ : Event n) (hsame_entry : e₁.sameEntry n e₂)
  : b.eventsAtEventEntry n e₁ = b.eventsAtEventEntry n e₂ := by
  simp[eventsAtEventEntry, eventsAtEntryOfListBottomEvents]
  have hsame_addr := hsame_entry.sameAddr
  have hsame_struct := hsame_entry.sameStruct
  simp[Event.sameAddr] at hsame_addr
  simp[Event.sameStructure] at hsame_struct
  rw [hsame_addr]
  rw [hsame_struct]

lemma Behaviour.listImmediateBottomPred_of_eventsAtEventEntry_IsImmediateBottomPred {b : Behaviour n}
  {e_pred e : Event n} (hb_imm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : b.listImmediateBottomPred n (eventsAtEventEntry n b e) e_pred e := by
  apply b.eventsAtEventEntry_imm_pred_equiv n (e.struct n) (e.addr n)
  . case hpred_in_b => exact hb_imm_bot_pred.isImmPred.bPred.predInB
  . case he_in_b => exact hb_imm_bot_pred.isImmPred.bPred.succInB
  . case hpred_at_st =>
    have hpred_at_e_struct := hb_imm_bot_pred.isImmPred.bPred.sameEntry.sameStruct
    simp[Event.sameStructure] at hpred_at_e_struct
    simp[hpred_at_e_struct]
  . case hpred_at_addr =>
    have hpred_at_e_addr := hb_imm_bot_pred.isImmPred.bPred.sameEntry.sameAddr
    simp[Event.sameAddr] at hpred_at_e_addr
    simp[hpred_at_e_addr]
  . case he_at_st => rfl
  . case he_at_addr => rfl
  . case hb_imm_bot_pred => exact hb_imm_bot_pred

lemma Behaviour.upTo_immediatePredecessor_eq {b : Behaviour n} {e_pred e : Event n}
  (hb_imm_bot_pred : b.IsImmediateBottomPred n e_pred e)
  : b.eventsUpToEvent n e = b.eventsUpToEvent n e_pred ++ [e_pred] := by
  have hn_imm_pred_m : b.listImmediateBottomPred n (eventsAtEventEntry n b e) e_pred e :=
    b.listImmediateBottomPred_of_eventsAtEventEntry_IsImmediateBottomPred n hb_imm_bot_pred
  simp[eventsUpToEvent]
  rw[b.eventsAtEventEntry_eq_same_entry n e_pred e hn_imm_pred_m.sameEntry]
  simp[List.upToEvent]

  apply Eq.symm
  have hidxm_eq_idxn_one : List.idxOf e (eventsAtEventEntry n b e) = List.idxOf e_pred (eventsAtEventEntry n b e) + 1 :=
    hn_imm_pred_m.noIntermediate
  rw[hidxm_eq_idxn_one]

  have he_pred_in_eventsAtEventEntry := b.bottom_e_in_b_impl_in_eventsAtEventEntry n e_pred hn_imm_pred_m.predInB hn_imm_pred_m.isBottomPred
  have he_in_eventsAtEventEntry      := b.bottom_e_in_b_impl_in_eventsAtEventEntry n e hn_imm_pred_m.succInB hn_imm_pred_m.isBottomSucc

  rw[b.eventsAtEventEntry_eq_same_entry n e_pred e hn_imm_pred_m.sameEntry] at he_pred_in_eventsAtEventEntry

  have hn_lt_len : List.idxOf e_pred (eventsAtEventEntry n b e) < (eventsAtEventEntry n b e).length :=
    List.idxOf_lt_length_of_mem he_pred_in_eventsAtEventEntry
  have heventsAtEventEntry_nodup := b.eventsAtEventEntry_no_dups n e
  have hn : [(eventsAtEventEntry n b e)[List.idxOf e_pred (eventsAtEventEntry n b e)]] = [e_pred] := by
    simp[List.idxOf_getElem heventsAtEventEntry_nodup (List.idxOf e_pred (eventsAtEventEntry n b e)) hn_lt_len]
  rw[← hn]

  apply List.take_append_getElem hn_lt_len

lemma List.idx_in_take_lt_take_idx {α} [DecidableEq α]
  (l : List α) (e : α) (hl_nodup : l.Nodup)
  : ∀ e' ∈ take (idxOf e l) l, idxOf e' l < idxOf e l := by
  intro e' he'_in_take
  have he'_in_l_somewhere := List.mem_take_iff_getElem.mp he'_in_take
  obtain ⟨he'_lt_min, hget_e'_from_l⟩ := he'_in_l_somewhere.choose_spec
  have he'_lt_l_length : he'_in_l_somewhere.choose < l.length := by
    unfold min at he'_lt_min
    unfold instMinNat minOfLe at he'_lt_min
    simp at he'_lt_min

    /- Also unfold and simp the definitions in the goal; Needed to have the types of
    the ...choose be the same. -/
    unfold min instMinNat minOfLe
    simp
    by_cases idxOf e l ≤ l.length
    . case pos he_is_le_length =>
      simp [he_is_le_length, reduceIte] at he'_lt_min
      /- Simp the exist-choose in the def as well. -/
      simp [he_is_le_length, reduceIte]
      exact Nat.lt_of_lt_of_le he'_lt_min he_is_le_length
    . case neg he_not_le_length =>
      simp[he_not_le_length] at he'_lt_min
      /- Simp the exist-choose in the def as well. -/
      simp[he_not_le_length]
      exact he'_lt_min

  have he'_lt_idx_of_e : he'_in_l_somewhere.choose < idxOf e l := by
    unfold min at he'_lt_min
    unfold instMinNat minOfLe at he'_lt_min
    simp at he'_lt_min

    /- Simp the exist-choose in the def as well. -/
    unfold min instMinNat minOfLe
    simp

    by_cases idxOf e l ≤ l.length
    . case pos he_is_le_length =>
      simp [he_is_le_length, reduceIte] at he'_lt_min
      /- Simp the exist-choose in the def as well. -/
      simp [he_is_le_length, reduceIte]
      exact he'_lt_min
    . case neg he_not_le_length =>
      simp[he_not_le_length] at he'_lt_min
      /- Simp the exist-choose in the def as well. -/
      simp[he_not_le_length]

      simp at he_not_le_length
      exact Nat.lt_trans he'_lt_min he_not_le_length

  /- Can't use `lt_min_iff`, it uses `instDistribLatticeOfLinearOrder.toSemilatticeInf.toLT`
  instead of `instLTNat` -/
  -- obtain ⟨he'_lt_idx_of_e, he'_lt_l_length⟩ := lt_min_iff.mp he'_lt_min
  have tidx_of_e' := List.idxOf_getElem hl_nodup he'_in_l_somewhere.choose he'_lt_l_length
  rw[hget_e'_from_l] at tidx_of_e'
  rw[← tidx_of_e'] at he'_lt_idx_of_e
  . case intro =>
    simp [he'_lt_idx_of_e]


lemma List.upToEvent_e'_in_list_before_e
  (l : List (Event n)) (e : Event n) (hl_nodup : l.Nodup)
  : ∀ e' ∈ upToEvent n l e, l.idxOf e' < l.idxOf e := by
  simp [upToEvent, ]
  intro e' he'_in_up_to
  apply idx_in_take_lt_take_idx
  . case hl_nodup => exact hl_nodup
  . case a => exact he'_in_up_to

lemma List.upToEvent_ordered_before_e
(l : List (Event n)) (e : Event n)
(he_in_l : e ∈ l) (hl_nodup : l.Nodup)
(hl_sorted : List.Sorted (Event.OrderedBefore n) l)
  : ∀ e' ∈ List.upToEvent n l e, e'.OrderedBefore n e := by
  intro e' he'_in_up_to
  simp[Sorted] at hl_sorted
  rw[List.pairwise_iff_get] at hl_sorted
  -- by `he'_in_up_to`, we know `e'` must be before `e` (i.e. `idxOf e' < idxOf e`).

  let hidx_e' := l.idxOf e'
  let hidx_e  := l.idxOf e

  let hidx_e'_le_length : hidx_e' < l.length := by
    apply List.idxOf_lt_length_of_mem
    . case h =>
      apply List.mem_of_mem_take
      simp[upToEvent] at he'_in_up_to
      exact he'_in_up_to
  let hidx_e_le_length  : hidx_e < l.length  := List.idxOf_lt_length_of_mem he_in_l

  let hidx_e'_fin : Fin l.length := ⟨hidx_e', hidx_e'_le_length⟩
  let hidx_e_fin  : Fin l.length := ⟨hidx_e, hidx_e_le_length⟩

  have hlt_idx_impl_ordered_before := hl_sorted hidx_e'_fin hidx_e_fin
  repeat rw [List.idxOf_get] at hlt_idx_impl_ordered_before

  apply hlt_idx_impl_ordered_before
  apply upToEvent_e'_in_list_before_e
  . case hl_nodup => exact hl_nodup
  . case a => exact he'_in_up_to

lemma Behaviour.eventsUpToEvent_are_pred_to_e (b : Behaviour n) (e : Event n)
  (he_in_b : e ∈ b) (he_bottom : b.IsBottomEvent n e)
  : ∀ e' ∈ b.eventsUpToEvent n e, b.Predecessor n e' e := by
  intro e' he'_up_to_e
  have he'_at_entry := b.eventsUpToEntry_at_e_entry n e
  have he'_at_e := he'_at_entry e' he'_up_to_e

  simp[eventsUpToEvent] at he'_up_to_e
  have he'_in_upto_e_of_es_at_entry := he'_up_to_e

  constructor
  . case sameEntry =>
    constructor
    . case sameStruct =>
      exact he'_at_e.eAtStruct
    . case sameAddr =>
      exact he'_at_e.eAtAddr
  . case isPred =>
    apply List.upToEvent_ordered_before_e
    . case he_in_l =>
      apply Behaviour.bottom_e_in_b_impl_in_eventsAtEventEntry
      . case he_in_b => exact he_in_b
      . case he_bottom => exact he_bottom
    . case hl_nodup => exact b.eventsAtEventEntry_no_dups n e
    . case hl_sorted =>
      apply eventsAtEventEntry_ordered_before_sorted
    . case a => exact he'_in_upto_e_of_es_at_entry
  . case predInB =>
    exact he'_at_e.eInB
  . case succInB =>
    exact he_in_b

/- Def 2.33 Behaviour.StateBefore -/
noncomputable def Behaviour.stateBefore (b : Behaviour n) (init : EntryState n) (e : Event n) : EntryState n :=
  b.eventsUpToEvent n e |>.stateAfter n init

noncomputable def Behaviour.stateAfter (b : Behaviour n) (init : EntryState n) (e : Event n) : EntryState n :=
  b.eventsUpToEvent n e ++ [e] |>.stateAfter n init

lemma Behaviour.eventsUpToEvent_at_e_entry (b : Behaviour n) (e : Event n) :
  ∀ e' ∈ b.eventsUpToEvent n e, e' ∈ b.eventsAtEventEntry n e := by
  let es := eventsAtEventEntry n b e
  intro e' he'_in_es
  simp[eventsUpToEvent] at he'_in_es
  induction hind : (eventsAtEventEntry n b e) with
  | nil =>
    rw[ hind] at he'_in_es
    simp[List.upToEvent] at he'_in_es
  | cons head l_tail ih =>
    rw[hind] at he'_in_es
    simp
    by_cases he'_is_head : e' = head
    . case pos =>
      apply Or.intro_left
      exact he'_is_head
    . case neg =>
      apply Or.intro_right
      simp[List.upToEvent] at he'_in_es
      rw[List.take_cons] at he'_in_es
      rw[List.idxOf_cons] at he'_in_es
      simp at he'_in_es
      by_cases hhead_is_e : head = e
      . case pos =>
        have he'_in_rest := Or.resolve_left he'_in_es he'_is_head
        simp[hhead_is_e] at he'_in_rest
      . case neg =>
        have he'_in_rest := Or.resolve_left he'_in_es he'_is_head
        simp at he'_in_rest
        simp[hhead_is_e] at he'_in_rest

        have he'_in_tail := List.mem_of_mem_take he'_in_rest
        exact he'_in_tail

      . case h =>
        by_cases hhead_is_e : head = e
        . case pos =>
          rw[List.idxOf_cons] at he'_in_es
          simp[BEq.beq] at he'_in_es
          rw[hhead_is_e] at he'_in_es
          simp[BEq.rfl] at he'_in_es
        . case neg =>
          simp[List.idxOf_cons]
          simp[hhead_is_e]

lemma Behaviour.eventsUpToEvent_are_at_entry (b : Behaviour n) (e :Event n) :
  ∀ e' ∈ b.eventsUpToEvent n e, b.eventAtEntry n e' e.struct e.addr := by
  intro e' he'_in_up_to
  apply Behaviour.eventsAtEventEntry_at_e_entry n b e
  apply Behaviour.eventsUpToEvent_at_e_entry n b e e' he'_in_up_to

def CacheEvent.stateUpgradeMayEncapsulate (e₁ e₂ : CacheEvent n) (s₁ : State) : Prop :=
  e₁.WithoutCoherentPermissions n s₁ ∧ e₂.External → (e₁.Ordered n e₂ ∨ e₁.Encapsulates n e₂)

inductive CacheEvent.OrderedOrEncapsulates (e₁ e₂ : CacheEvent n) (b : Behaviour n) (init : EntryState n) : Prop
| orderedOrEncapsulates (s₁ s₂ : State) :
  e₁.stateUpgradeMayEncapsulate n e₂ (b.stateBefore n init (Event.cacheEvent e₁)).cache ∨
  e₂.stateUpgradeMayEncapsulate n e₁ (b.stateBefore n init (Event.cacheEvent e₂)).cache →
  CacheEvent.OrderedOrEncapsulates e₁ e₂ b init
| ordered : e₁.Ordered n e₂ → CacheEvent.OrderedOrEncapsulates e₁ e₂ b init

/-- Axiom 2 (Second half) Certain Request Events may encapusulate External Events. -/
structure CacheEvent.EncapAnother (e₁ e₂ : CacheEvent n) (b : Behaviour n) (init : EntryState n) : Prop where
  sameCacheEntry : e₁.sameCacheEntry n e₂
  orderOrEncap : CacheEvent.OrderedOrEncapsulates n e₁ e₂ b init
