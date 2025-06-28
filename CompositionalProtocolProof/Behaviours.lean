import CompositionalProtocolProof.EventRelations
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib
import Canonical

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

def Behaviour.NoIntermediatePredecessor (b : Behaviour n) (e_pred e_succ : Event n) : Prop :=
  ∀ e ∈ b, ¬ (e.OrderedBetween n e_pred e_succ)

structure Behaviour.Predecessor (b : Behaviour n) (e_pred e_succ : Event n) where
  sameEntry : Event.sameEntry n e_pred e_succ
  isPred : e_pred.Predecessor n e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

structure Behaviour.EntryImmediatePredecessor (b : Behaviour n) (e_pred e_succ : Event n) where
  sameEntry : Event.sameEntry n e_pred e_succ
  behavePred : Behaviour.Predecessor n b e_pred e_succ
  noIntermediate : b.NoIntermediatePredecessor n e_pred e_succ

/- Access properties nested deeper in Behaviour.ImmediatePredecessor -/
def Behaviour.EntryImmediatePredecessor.isPred {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred.Predecessor n e_succ := hb_imm_pred.behavePred.isPred
def Behaviour.EntryImmediatePredecessor.predInB {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred ∈ b.es := hb_imm_pred.behavePred.predInB
def Behaviour.EntryImmediatePredecessor.sameStructure {b : Behaviour n} {e_pred e_succ : Event n} (hb_imm_pred : Behaviour.EntryImmediatePredecessor n b e_pred e_succ)
: e_pred.sameStructure n e_succ := hb_imm_pred.behavePred.sameEntry.sameStruct
structure Event.EncapAtSameStructure (e_bottom e : Event n) : Prop where
  encap : e_bottom.Encapsulates n e
  sameEntry : Event.sameEntry n e_bottom e

abbrev Behaviour.IsNotEncapAtSameStruct (b : Behaviour n) (e : Event n) : Prop := ∀ e' ∈ b.es, ¬ e'.EncapAtSameStructure n e

def Behaviour.IsBottomEvent (b : Behaviour n) (e : Event n) : Prop := b.IsNotEncapAtSameStruct n e
structure Behaviour.bottomEvent : Prop where
  isBottom : ∀ b : Behaviour n, ∀ e : Event n, b.IsBottomEvent n e

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
  isBottom : b.IsBottomEvent n e_pred

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

    apply he₁_no_intermediate_to_e_suc
    apply he₂_b.isImmPred.predInB
    constructor
    unfold autoParam
    . case a.pred =>
      exact es₁_ordered_es₂
    . case a.succ =>
      unfold autoParam

      have e₂_o_e_succ := he₂_b.isImmPred.isPred
      unfold Event.Predecessor at e₂_o_e_succ
      exact e₂_o_e_succ
  . case inr es₂_ordered_es₁ =>
    have he₂_no_intermediate_to_e_suc := he₂_b.isImmPred.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₂_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₂_no_intermediate_to_e_suc

    apply he₂_no_intermediate_to_e_suc
    apply he₁_b.isImmPred.predInB
    constructor
    unfold autoParam
    . case a.pred =>
      exact es₂_ordered_es₁
    . case a.succ =>
      unfold autoParam

      have e₁_o_e_succ := he₁_b.isImmPred.isPred
      unfold Event.Predecessor at e₁_o_e_succ
      exact e₁_o_e_succ

lemma CacheEvent.encap_then_event_encap (ce₁ ce₂ : CacheEvent n) (hencap : ce₁.Encapsulates n ce₂) :
  (Event.cacheEvent ce₁).Encapsulates n (Event.cacheEvent ce₂) := by
  unfold Event.Encapsulates Event.oStart Event.oEnd
  simp[CacheEvent.Encapsulates] at hencap
  exact hencap

lemma Event.same_entry_symm (e₁ e₂ : Event n) (hsame_entry : e₁.sameEntry n e₂) : e₂.sameEntry n e₁ := by
  constructor
  . case sameStruct =>
    constructor
    simp[hsame_entry.sameStruct.sameStruct]
  . case sameAddr =>
    constructor
    simp[hsame_entry.sameAddr.sameStruct]

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
    have he₁_struct_e := he₁_entry_e.sameStruct.sameStruct
    have he₂_struct_e := he₂_entry_e.sameStruct.sameStruct
    rw[← he₂_struct_e] at he₁_struct_e
    constructor
    exact he₁_struct_e
  . case sameAddr =>
    have he₁_addr_e := he₁_entry_e.sameAddr.sameStruct
    have he₂_addr_e := he₂_entry_e.sameAddr.sameStruct
    constructor
    rw[← he₂_addr_e] at he₁_addr_e
    exact he₁_addr_e

lemma Event.same_entry_trans' {e₁ e₂ e : Event n} (he_entry_e₁ : e.sameEntry n e₁) (he_entry_e₂ : e.sameEntry n e₂)
  : e₁.sameEntry n e₂ := by
  constructor
  . case sameStruct =>
    have he_struct_e₁ := he_entry_e₁.sameStruct.sameStruct
    have he_struct_e₂ := he_entry_e₂.sameStruct.sameStruct
    rw[he_struct_e₁] at he_struct_e₂
    constructor
    exact he_struct_e₂
  . case sameAddr =>
    have he_addr_e₁ := he_entry_e₁.sameAddr.sameStruct
    have he_addr_e₂ := he_entry_e₂.sameAddr.sameStruct
    constructor
    rw[he_addr_e₁] at he_addr_e₂
    exact he_addr_e₂

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
      have hpred₁_pred₂_same_entry := Event.same_entry_trans n he₁_b.isImmPred.behavePred.sameEntry he₂_b.isImmPred.behavePred.sameEntry
      have ce₁_ce₂_ordered := orderedBottomCacheEntries n b ce₁ ce₂ he₁_b.isImmPred.predInB he₂_b.isImmPred.predInB
        he₁_b.isBottom he₂_b.isBottom hpred₁_pred₂_same_entry

      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction n he₁_b he₂_b ce₁_ce₂_ordered
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmPred.sameStructure
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_cache.sameStruct
        unfold Event.struct at e₂_same_struct_e_succ
        simp at e₂_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_dir.sameStruct
        unfold Event.struct at e₁_same_struct_e_succ
        simp at e₁_same_struct_e_succ
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure
      match hsucc : e_succ with
      | .directoryEvent de_succ =>
        subst hsucc
        have e₁_same_struct_e_succ := h_e_succ_is_cache.sameStruct
        unfold Event.struct at e₁_same_struct_e_succ
        simp at e₁_same_struct_e_succ
      | .cacheEvent ce_succ =>
        subst hsucc
        have e₂_same_struct_e_succ := h_e_succ_is_dir.sameStruct
        unfold Event.struct at e₂_same_struct_e_succ
        simp at e₂_same_struct_e_succ

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

/- Add constraint `p` on predecessor -/

def Event.PropOnEvent (e : Event n) (p : Event n → Prop) : Prop := p e

structure Behaviour.IsImmediateBottomPredSatisfyingProp (b : Behaviour n) (e_pred e_succ : Event n) (p : Event n → Prop) where
  isImmBottomPred : b.IsImmediateBottomPred n e_pred e_succ
  satisfyP : e_pred.PropOnEvent n p

def Behaviour.ImmediateBottomPredSatisfyingProp : Behaviour n → Event n → Event n → (Event n → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomPredSatisfyingProp n e_pred e_succ p

def Behaviour.ImmBottomPredecessorsSatisfyingP : Behaviour n → Event n → (Event n → Prop) → Set (Event n)
| b, e_succ, p => {e_pred ∈ b.es | b.ImmediateBottomPredSatisfyingProp n e_pred e_succ p}

lemma Behaviour.immediate_bottom_predecessor_satisfying_p_unique (b : Behaviour n) (e_succ : Event n)
  (e_pred₁ e_pred₂ : Event n) (p : Event n → Prop)
  (he₁_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₁ e_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp n e_pred₂ e_succ p) :
  e_pred₁ = e_pred₂ := by
    have he₁_b' : b.IsImmediateBottomPred n e_pred₁ e_succ := by
      constructor
      exact he₁_b.isImmBottomPred.isImmPred
      exact he₁_b.isImmBottomPred.isBottom
    have he₂_b' : b.IsImmediateBottomPred n e_pred₂ e_succ := by
      constructor
      exact he₂_b.isImmBottomPred.isImmPred
      exact he₂_b.isImmBottomPred.isBottom

    apply Behaviour.immediate_bottom_predecessor_unique n b e_succ e_pred₁ e_pred₂ he₁_b' he₂_b'

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
      apply Behaviour.immediate_bottom_predecessor_satisfying_p_unique n b e_succ e₁ e₂ p
      exact And.right he₁
      exact And.right he₂
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

lemma Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction {e_pred e_succ₁ e_succ₂ : Event n} {b : Behaviour n}
(he₁_b : b.IsImmediateBottomSucc n e_pred e_succ₁) (he₂_b : b.IsImmediateBottomSucc n e_pred e_succ₂)
(hes₁_ordered_es₂ : e_succ₁.OrderedBefore n e_succ₂ ∨ e_succ₂.OrderedBefore n e_succ₁)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he_no_intermediate_to_e_suc₂ := he₂_b.isImmSucc.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he_no_intermediate_to_e_suc₂
    unfold Behaviour.NoIntermediatePredecessor at he_no_intermediate_to_e_suc₂
    have e_pred_o_e_succ₁ := he₁_b.isImmSucc.isSucc
    unfold Event.Predecessor at e_pred_o_e_succ₁
    unfold Event.Successor at e_pred_o_e_succ₁
    simp at e_pred_o_e_succ₁

    apply he_no_intermediate_to_e_suc₂
    apply he₁_b.isImmSucc.succInB
    constructor
    unfold autoParam
    . case a.pred =>
      unfold Event.Predecessor at e_pred_o_e_succ₁
      simp at e_pred_o_e_succ₁
      unfold Event.OrderedBefore
      exact e_pred_o_e_succ₁
    . case a.succ =>
      unfold autoParam
      exact es₁_ordered_es₂
  . case inr es₂_ordered_es₁ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmSucc.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₁_no_intermediate_to_e_suc
    have e_pred_o_e_succ₂ := he₂_b.isImmSucc.isSucc
    unfold Event.Successor at e_pred_o_e_succ₂
    simp at e_pred_o_e_succ₂

    apply he₁_no_intermediate_to_e_suc
    apply he₂_b.isImmSucc.succInB
    constructor
    unfold autoParam
    . case a.pred =>
      unfold Event.Predecessor at e_pred_o_e_succ₂
      simp at e_pred_o_e_succ₂
      unfold Event.OrderedBefore
      exact e_pred_o_e_succ₂
    . case a.succ =>
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
      have h_e_succ_is_dir   := he₁_b.isImmSucc.sameEntry.sameStruct.sameStruct
      have h_e_succ_is_cache := he₂_b.isImmSucc.sameEntry.sameStruct.sameStruct
      simp [Event.struct] at h_e_succ_is_dir h_e_succ_is_cache

      match hsucc : e_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmSucc.sameEntry.sameStruct.sameStruct
      have h_e_succ_is_dir   := he₂_b.isImmSucc.sameEntry.sameStruct.sameStruct
      simp [Event.struct] at h_e_succ_is_dir h_e_succ_is_cache

      match hsucc : e_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir

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

def Event.atStruct (e : (Event n)) (st : (Struct n)) : Prop :=
  match st with
  | .directory => e.isDirectoryEvent
  | .cache cid => e.isCacheEventAtCid n cid

structure Event.isBottomAtEntry (b : Behaviour n) (st : Struct n) (addr : Addr) (e : Event n) where
  addr : e.addr = addr
  atStruct : e.atStruct n st
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

noncomputable def Set.finSetEvents' {b} {st} {addr} (es : Set (EventAtEntry n b st addr)) (hes_fin : Finite es) : Finset (EventAtEntry n b st addr) := Set.Finite.toFinset hes_fin

lemma Subtype.equiv_fin_impl_equiv_fin' {α} {n} {p q : α → Prop} (himpl : ∀ x, q x → p x)
  (f : { x // p x} ≃ Fin n) : ∃ m, m ≤ n ∧ Nonempty ({x // q x} ≃ Fin m) := by
    sorry

lemma Subtype.impl_finite {α} {p q : α → Prop} (himpl : ∀ x, q x → p x)
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

/-- state the Set of EventAtState from bottom events at an entry is a finite set. -/
theorem Behaviour.bottomEventsAtEntry_finite'' (b : Behaviour n) (addr : Addr) (st : Struct n) (fin_bots : Finite (b.bottomEventsAtEntry n addr st))
  : Finite (b.bottomEventsAtEntry' n addr st) := by
  cases st <;> simp [Behaviour.bottomEventsAtEntry']
  · case directory =>
      have _ : Finite b.es := b.finite
      have h := fin_bots.image -- can I map from the finite set of Events to EventAtEntry?
      apply Finite.Set.finite_inter_of_left
  · case cache _ =>
      have _ : Finite b.es := b.finite
      apply Finite.Set.finite_inter_of_left

noncomputable def Behaviour.listBottomEventsAtEntry' (b : Behaviour n) (addr : Addr) (st : Struct n) : List (EventAtEntry n b st addr) :=
  let e_at_centry := b.bottomEventsAtEntry' n addr st
  Set.finSetEvents' n e_at_centry (b.bottomEventsAtEntry_finite n addr st) |>.toList

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

/-
def Event.isBottomEvent (e : Event) : Prop := ¬ ∃ e' : Event, e'.Encapsulates e

structure Event.BottomPredecessor (e_pred e_succ : Event) : Prop where
  sameEntry : Event.sameEntry
  behavePred : e_pred.Predecessor e_succ
  predBottom : e_pred.isBottomEvent
  succBottom : e_succ.isBottomEvent
-/

instance : DecidableRel (Event.OrderedBefore n) := by
  unfold Event.OrderedBefore
  infer_instance

/- NOTE: This requires assumptions (b, hsame_entry, and so on..) that means instance isn't used by IsTotal Event Event.OrderedBefore. -/
/-
instance Event.OrderedBefore.instIsTotal (b : Behaviour n) (hsame_entry : Event.sameEntry n) (hentry_ordered : Event.AtEntryOrdered n) : IsTotal (Event n) (Event.OrderedBefore n) := by
  unfold Event.OrderedBefore
  constructor
  intro e₁ e₂
  . case total =>
    have h := hsame_entry.sameStruct e₁ e₂
    -- simp[Event.sameStructure] at h
    have hsame_struct := h.sameStruct
    match he₁ : e₁, he₂ : e₂ with
    | .cacheEvent ce₁ , .cacheEvent ce₂ =>
      apply hentry_ordered.cache_ordered ce₁ ce₂ b |>.ordered
    | .directoryEvent de₁ , .directoryEvent de₂ =>
      apply hentry_ordered.dir_ordered de₁ de₂ |>.ordered
    | .cacheEvent ce₁ , .directoryEvent de₂ =>
      simp[Event.struct, he₁, he₂] at hsame_struct
    | .directoryEvent de₁ , .cacheEvent ce₂ =>
      simp[Event.struct, he₁, he₂] at hsame_struct
-/

/- NOTE: To be an instance of IsTotal, there can't be any assumptions, like the following below. -/
instance Event.OrderedBefore.instIsTotal' : IsTotal (Event n) (Event.OrderedBefore n) := by sorry


/- NOTE: Likewise, this is also not a valid instance of IsTotal. -/
/-
instance Behaviour.BottomPredecessor.instIsTotal (b : Behaviour n) (hbottom : Behaviour.bottomEvent n) (hpred : Behaviour.Predecessor n) (hsame_entry : (Event.sameEntry n)) : IsTotal (Event n) (b.BottomPredecessor n) := by
  constructor
  intro e₁ e₂
  . case total =>
    constructor
    . case h =>
      constructor
      . case sameEntry =>
        exact hsame_entry
      . case behavePred =>
        exact hpred
      . case predBottom =>
        exact hbottom.isBottom b e₁
      . case succBottom =>
        exact hbottom.isBottom b e₂
-/

/- NOTE: BottomPredecessor is a structure, so can't be a DecidableRel. -/
instance Behaviour.BottomPredecessor.instDecidableRel (b : Behaviour n) : DecidableRel (b.BottomPredecessor n) := by
  unfold DecidableRel
  intro e₁ e₂
  -- infer_instance
  sorry

def Behaviour.sortedListBottomEventsAtEntry (b : Behaviour n) (addr : Addr) (st : Struct n) : Prop := b.listBottomEventsAtEntry n addr st |>.Sorted (b.BottomPredecessor n)

structure Behaviour.sortedListEventsAtEntry : Prop where
  bottom_sorted (b : Behaviour n) (addr : Addr) (st : Struct n) : b.sortedListBottomEventsAtEntry n addr st

def List.sortedListBottomEventsAtEntry (l : List (Event n)) (b : Behaviour n) : Prop := l |>.Sorted (b.BottomPredecessor n)

structure List.sortedListEventsAtEntry : Prop where
  bottom_sorted (l : List (Event n)) (b : Behaviour n) : l.sortedListBottomEventsAtEntry n b

noncomputable def Behaviour.sortedEventsAtEntry' (b : Behaviour n) (addr : Addr) (st : Struct n) : List (Event n) := b.listBottomEventsAtEntry n addr st |>.insertionSort (Event.OrderedBefore n)

lemma Behaviour.eventsAtCacheEntry_total_order (b : Behaviour n) (addr : Addr) (st : Struct n)
  (hbottom_sorted : List.sortedListEventsAtEntry n) :
  -- b.listBottomEventsAtEntry addr st |>.isOrdered (Event.OrderedBefore)
  let bes := b.listBottomEventsAtEntry n addr st
  let es := bes.insertionSort (Event.OrderedBefore n)
  es |>.isOrdered (b.BottomPredecessor n)
  -- probably `Event.OrderedBefore` is not the right order though! or is it? not sure you've define the order on events that these are ordered by?
:= by
  unfold List.isOrdered
  intro bes es i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    -- have h := List.sorted_insertionSort b.BottomPredecessor es
    constructor
    . case sameEntry =>
      -- unfold sortedListEventsAtEntry at hlist_sorted
      sorry
    . case behavePred =>
      constructor
      . case sameEntry =>
        sorry
      . case isPred =>
        have hlist_sorted := hbottom_sorted.bottom_sorted es b
        unfold sortedListBottomEventsAtEntry at hlist_sorted
        simp[es] at hlist_sorted
        sorry
      . case predInB =>
        sorry
      . case succInB =>
        sorry
    . case predBottom =>
      sorry
    . case succBottom =>
      sorry
  . case mpr =>
    intro hi_bottom_pred_j
    sorry

lemma Behaviour.eventsAtCacheEntry_total_order' (b : Behaviour n) (addr : Addr) (st : Struct n)
  (hbottom_sorted : Behaviour.sortedListEventsAtEntry n) :
  let bes := b.listBottomEventsAtEntry n addr st
  let es := bes.insertionSort (Event.OrderedBefore n)
  es |>.isOrdered (Event.OrderedBefore n)
  -- b.listBottomEventsAtEntry addr st |>.isOrdered (b.BottomPredecessor)
  -- probably `Event.OrderedBefore` is not the right order though! or is it? not sure you've define the order on events that these are ordered by?
:= by
  unfold List.isOrdered
  intro bes es i j
  apply Iff.intro
  . case mp =>
    simp[List.sorted_insertionSort (Event.OrderedBefore n) bes] -- at es
    have h := List.sorted_insertionSort (Event.OrderedBefore n) es
    intro hi_lt_j
    -- unfold Event.OrderedBefore
    have hlist_sorted := hbottom_sorted.bottom_sorted b addr st
    unfold Behaviour.sortedListBottomEventsAtEntry at hlist_sorted
    unfold List.Sorted at hlist_sorted
    have t := hlist_sorted
    -- unfold List.Pairwise at hlist_sorted
    sorry
  . case mpr =>
    intro hi_bottom_pred_j
    sorry

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

    -- [TODO] implement is instance of: IsTrans (EventAtEntry n b st addr) (EventAtEntry.encapOrOrderedBefore n b st addr)
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

lemma Behaviour.eventsAtCacheEntry_total_order'' (b : Behaviour n) (addr : Addr) (st : Struct n)
  -- (hbottom_sorted : Behaviour.sortedListEventsAtEntry n)
  :
  let bes := b.listBottomEventsAtEntry' n addr st
  let es := bes.insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)
  es |>.isOrdered (EventAtEntry.encapOrOrderedBefore n b st addr)
  -- b.listBottomEventsAtEntry addr st |>.isOrdered (b.BottomPredecessor)
  -- probably `Event.OrderedBefore` is not the right order though! or is it? not sure you've define the order on events that these are ordered by?
  := by
  --
  intro bes es i j
  apply Iff.intro
  . case mp =>
    -- intro hi_lt_j
    -- [TODO] implement is instance of: IsTrans (EventAtEntry n b st addr) (EventAtEntry.encapOrOrderedBefore n b st addr)
    have hsorted := List.sorted_insertionSort (EventAtEntry.encapOrOrderedBefore n b st addr)
    simp
    simp[List.Sorted, List.Pairwise, List.insertionSort] at hsorted
    -- simp[hsorted] -- How do I use `List.sorted_insertionSort` to close the goal? it should be very similar to the goal in theory?
    sorry
  . case mpr =>
    sorry

def List.stateAfter (es : List (Event n)) (init : (EntryState n)) : EntryState n := match es with
  | [] => init
  | e :: es' => es'.stateAfter (e.SucceedingState n init)

def List.stateAtE (es : List (Event n)) (e : Event n) (init : EntryState n) : EntryState n :=
  List.stateAfter n (es.splitAt (es.indexesOf e).head!).1 init

/- Def 2.33 Behaviour.StateBefore -/
noncomputable def Behaviour.stateBefore (b : Behaviour n) (init : EntryState n) (e : Event n) : EntryState n :=
  b.listBottomEventsAtEntry n e.addr e.struct |>.insertionSort (Event.OrderedBefore n) |>.stateAtE n e init

noncomputable def Behaviour.stateAfter (b : Behaviour n) (init : EntryState n) (e : Event n) : EntryState n :=
  e.SucceedingState n (b.stateBefore n init e)

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
