import CompositionalProtocolProof.EventRelations
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib
import Canonical

structure Behaviour where
  es : Set Event
  -- es : Finset Event
  finite : Finite es

instance : Membership Event Behaviour := ⟨fun b e => e ∈ b.es⟩

def Behaviour.OrderedBetween : Behaviour → Event → Event → Set Event
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween e_pred e_succ}

/-
def Behaviour.NoIntermediatePredecessor' (b : Behaviour) (e_pred e_succ : Event) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅
-/

def Behaviour.NoIntermediatePredecessor (b : Behaviour) (e_pred e_succ : Event) : Prop :=
  ∀ e ∈ b, ¬ (e.OrderedBetween e_pred e_succ)

structure Behaviour.Predecessor where
  sameEntry : Event.sameEntry
  isPred : ∀ e_pred e_succ : Event, e_pred.Predecessor e_succ
  predInB : ∀ b : Behaviour, ∀ e_pred : Event, e_pred ∈ b.es
  succInB : ∀ b : Behaviour, ∀ e_succ : Event, e_succ ∈ b.es

structure Behaviour.EntryImmediatePredecessor (b : Behaviour) (e_pred e_succ : Event) where
  sameEntry : Event.sameEntry
  behavePred : Behaviour.Predecessor
  noIntermediate : b.NoIntermediatePredecessor e_pred e_succ

/- Access properties nested deeper in Behaviour.ImmediatePredecessor -/
def Behaviour.EntryImmediatePredecessor.isPred {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred.Predecessor e_succ := hb_imm_pred.behavePred.isPred e_pred e_succ
def Behaviour.EntryImmediatePredecessor.predInB {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred ∈ b.es := hb_imm_pred.behavePred.predInB b e_pred
def Behaviour.EntryImmediatePredecessor.sameStructure {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred.sameStructure e_succ := hb_imm_pred.behavePred.sameEntry.sameStruct e_pred e_succ
structure Event.EncapAtSameStructure (e_bottom e : Event) : Prop where
  encap : e_bottom.Encapsulates e
  sameEntry : Event.sameEntry

abbrev Behaviour.IsNotEncapAtSameStruct (b : Behaviour) (e : Event) : Prop := ∀ e' ∈ b.es, ¬ e'.EncapAtSameStructure e

def Behaviour.IsBottomEvent (b : Behaviour) (e : Event) : Prop := b.IsNotEncapAtSameStruct e
structure Behaviour.bottomEvent : Prop where
  isBottom : ∀ b : Behaviour, ∀ e : Event, b.IsBottomEvent e

structure CacheEvent.BottomAreOrdered (e₁ e₂ : CacheEvent) (b : Behaviour) : Prop where
  sameCacheEntry : e₁.sameCacheEntry e₂
  e₁Bottom : b.IsBottomEvent (Event.cacheEvent e₁)
  e₂Bottom : b.IsBottomEvent (Event.cacheEvent e₂)
  ordered : e₁.Ordered e₂

structure Behaviour.IsImmediateBottomPred (b : Behaviour) (e_pred e_succ : Event) where
  isImmPred : b.EntryImmediatePredecessor e_pred e_succ
  isBottom : b.IsBottomEvent e_pred

/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour → Event → Event → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour → Event → Set Event
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

structure Event.AtEntryOrdered where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent), DirectoryEvent.AreOrdered e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent), ∀ (b : Behaviour), CacheEvent.BottomAreOrdered e₁ e₂ b

lemma Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction {e_pred₁ e_pred₂ e_succ : Event} {b : Behaviour}
(he₁_b : b.IsImmediateBottomPred e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred e_pred₂ e_succ)
(hes₁_ordered_es₂ : e_pred₁.Ordered e_pred₂)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmPred.noIntermediate
    unfold Behaviour.EntryImmediatePredecessor at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediatePredecessor at he₁_no_intermediate_to_e_suc
    have e₁_o_e_succ := he₁_b.isImmPred.isPred
    unfold Event.Predecessor at e₁_o_e_succ
    simp at e₁_o_e_succ

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
    have e₂_o_e_succ := he₂_b.isImmPred.isPred
    unfold Event.Predecessor at e₂_o_e_succ
    simp at e₂_o_e_succ

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

lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (e_succ : Event)
  (e_pred₁ e_pred₂ : Event) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomPred e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred e_pred₂ e_succ) :
  e_pred₁ = e_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b's NoIntermediatePredecessor.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : e_pred₁, h_pred₂ : e_pred₂ with
    | .directoryEvent de₁, .directoryEvent de₂ => -- Use dir_ordered to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b de₁_de₂_ordered_prop.ordered
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      have hce₁_o_ce₂ := haddress_ordered.cache_ordered ce₁ ce₂ b
      have ce₁_ce₂_ordered := hce₁_o_ce₂.ordered

      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b ce₁_ce₂_ordered
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
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (e_succ : Event)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_preds := b.ImmBottomPredecessors e_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique b e_succ e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Add constraint `p` on predecessor -/

def Event.PropOnEvent (e : Event) (p : Event → Prop) : Prop := p e

structure Behaviour.IsImmediateBottomPredSatisfyingProp (b : Behaviour) (e_pred e_succ : Event) (p : Event → Prop) where
  isImmBottomPred : b.IsImmediateBottomPred e_pred e_succ
  satisfyP : e_pred.PropOnEvent p

def Behaviour.ImmediateBottomPredSatisfyingProp : Behaviour → Event → Event → (Event → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomPredSatisfyingProp e_pred e_succ p

def Behaviour.ImmBottomPredecessorsSatisfyingP : Behaviour → Event → (Event → Prop) → Set Event
| b, e_succ, p => {e_pred ∈ b.es | b.ImmediateBottomPredSatisfyingProp e_pred e_succ p}

lemma Behaviour.immediate_bottom_predecessor_satisfying_p_unique (b : Behaviour) (e_succ : Event)
  (e_pred₁ e_pred₂ : Event) (p : Event → Prop) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomPredSatisfyingProp e_pred₁ e_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp e_pred₂ e_succ p) :
  e_pred₁ = e_pred₂ := by
    have he₁_b' : b.IsImmediateBottomPred e_pred₁ e_succ := by
      constructor
      exact he₁_b.isImmBottomPred.isImmPred
      exact he₁_b.isImmBottomPred.isBottom
    have he₂_b' : b.IsImmediateBottomPred e_pred₂ e_succ := by
      constructor
      exact he₂_b.isImmBottomPred.isImmPred
      exact he₂_b.isImmBottomPred.isBottom

    apply Behaviour.immediate_bottom_predecessor_unique b e_succ e_pred₁ e_pred₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 1, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_predecessor_satisfying_p_empty_or_unique (b : Behaviour) (e_succ : Event) (p : Event → Prop)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_preds := b.ImmBottomPredecessorsSatisfyingP e_succ p; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_satisfying_p_unique b e_succ e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Now define the immediate bottom successor. -/

structure Behaviour.ImmediateSuccessorConstraint (b : Behaviour) (e_pred e_succ : Event) where
  isSucc : e_pred.Successor e_succ
  noIntermediate : b.NoIntermediatePredecessor e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

structure Behaviour.IsImmediateBottomSucc (b : Behaviour) (e_pred e_succ : Event) where
  isImmSucc : b.ImmediateSuccessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_succ

def Behaviour.ImmediateBottomSuccessor : Behaviour → Event → Event → Prop
| b, e_pred, e_succ => b.IsImmediateBottomSucc e_pred e_succ

def Behaviour.ImmBottomSuccessors : Behaviour → Event → Set Event
| b, e_pred => {e_succ ∈ b.es | b.ImmediateBottomSuccessor e_pred e_succ}

lemma Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction {e_pred e_succ₁ e_succ₂ : Event} {b : Behaviour}
(he₁_b : b.IsImmediateBottomSucc e_pred e_succ₁) (he₂_b : b.IsImmediateBottomSucc e_pred e_succ₂)
(hes₁_ordered_es₂ : e_succ₁.OrderedBefore e_succ₂ ∨ e_succ₂.OrderedBefore e_succ₁)
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

lemma Behaviour.immediate_bottom_successor_unique (b : Behaviour) (e_pred : Event)
  (e_succ₁ e_succ₂ : Event) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomSucc e_pred e_succ₁) (he₂_b : b.IsImmediateBottomSucc e_pred e_succ₂) :
  e_succ₁ = e_succ₂ := by
    by_contra h_e_pred_diff
    match h_succ₁ : e_succ₁, h_succ₂ : e_succ₂ with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b de₁_de₂_ordered_prop.ordered
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      /- Part 1. Use OrderedCacheEvents to show that ce₁ and ce₂ (which are bottom predecessors to e_succ)
      are always ordered. Part 2. This is a contradiction with ImmediateBottomPred's NoIntermediatePred. -/
      have hce₁_o_ce₂ := haddress_ordered.cache_ordered ce₁ ce₂ b
      apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b hce₁_o_ce₂.ordered
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmSucc.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmSucc.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : e_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmSucc.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmSucc.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : e_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir

lemma Behaviour.immediate_bottom_successor_empty_or_unique (b : Behaviour) (e_pred : Event)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_succs := b.ImmBottomSuccessors e_pred; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_unique b e_pred e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Verision of Immediate Bottom Successor that also satisfies Prop `p`. -/

structure Behaviour.IsImmediateBottomSuccSatisfyingProp (b : Behaviour) (e_pred e_succ : Event) (p : Event → Prop) where
  isImmBottomSucc : b.IsImmediateBottomSucc e_pred e_succ
  satisfyP : e_succ.PropOnEvent p

def Behaviour.ImmediateBottomSuccSatisfyingProp : Behaviour → Event → Event → (Event → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomSuccSatisfyingProp e_pred e_succ p

def Behaviour.ImmBottomSuccessorsSatisfyingP : Behaviour → Event → (Event → Prop) → Set Event
| b, e_pred, p => {e_succ ∈ b.es | b.ImmediateBottomSuccSatisfyingProp e_pred e_succ p}

lemma Behaviour.immediate_bottom_successor_satisfying_p_unique (b : Behaviour) (e_pred : Event)
  (e_succ₁ e_succ₂ : Event) (p : Event → Prop) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomSuccSatisfyingProp e_pred e_succ₁ p) (he₂_b : b.IsImmediateBottomSuccSatisfyingProp e_pred e_succ₂ p) :
  e_succ₁ = e_succ₂ := by
    have he₁_b' : b.IsImmediateBottomSucc e_pred e_succ₁ := by
      constructor
      exact he₁_b.isImmBottomSucc.isImmSucc
      exact he₁_b.isImmBottomSucc.isBottom
    have he₂_b' : b.IsImmediateBottomSucc e_pred e_succ₂ := by
      constructor
      exact he₂_b.isImmBottomSucc.isImmSucc
      exact he₂_b.isImmBottomSucc.isBottom

    apply Behaviour.immediate_bottom_successor_unique b e_pred e_succ₁ e_succ₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 2, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_successor (b : Behaviour) (e_pred : Event) (p : Event → Prop)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_succs := b.ImmBottomSuccessorsSatisfyingP e_pred p; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_satisfying_p_unique b e_pred e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Def 2.32 Behaviour.PreviousEvent -/
open scoped Classical in
noncomputable def Behaviour.PreviousEvent (b : Behaviour) (e : Event) (haddress_ordered : Event.AtEntryOrdered) : Option Event :=
  by classical exact
  -- Not clear how to open up `preds_empty_or_singleton` and use the `empty or singleton` statement inside?
  let preds_empty_or_singleton := b.ImmBottomPredecessors e -- haddress_ordered
  have h_empty_or_unique := b.immediate_bottom_predecessor_empty_or_unique e haddress_ordered
  if he : preds_empty_or_singleton = ∅ then -- Can't synthesize?
    none
  else
    (h_empty_or_unique.resolve_left he).choose

noncomputable def Set.finSetEvents (es : Set Event) (hes_fin : Finite es) : Finset Event := Set.Finite.toFinset hes_fin

def Event.atStruct (e : Event) (st : Struct) : Prop :=
  match st with
  | .directory => e.isDirectoryEvent
  | .cache cid => e.isCacheEventAtCid cid

structure Event.isBottomAtEntry (addr : Addr) (st : Struct) (e : Event) (b : Behaviour) where
  addr : e.addr = addr
  atStruct : e.atStruct st
  isBottom : b.IsBottomEvent e

def Behaviour.bottomEventsAtEntry (b : Behaviour) (addr : Addr) (st : Struct) : Set Event :=
  {e ∈ b.es | e.isBottomAtEntry addr st b}

theorem Behaviour.bottomEventsAtEntry_finite (b : Behaviour) (addr : Addr) (st : Struct) : Finite (b.bottomEventsAtEntry addr st) := by
  cases st <;> simp [Behaviour.bottomEventsAtEntry]
  · case directory =>
      have _ : Finite b.es := b.finite
      apply Finite.Set.finite_inter_of_left
  · case cache _ =>
      have _ : Finite b.es := b.finite
      apply Finite.Set.finite_inter_of_left

lemma Behaviour.bottomEventsAtEntry_complete (b : Behaviour) (addr : Addr) (st : Struct) :
  ∀ {e : Event}, (e ∈ b.bottomEventsAtEntry addr st) ↔ (e ∈ b.es ∧ e.isBottomAtEntry addr st b) := by
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

noncomputable def Behaviour.listBottomEventsAtEntry (b : Behaviour) (addr : Addr) (st : Struct) : List Event :=
  let e_at_centry := b.bottomEventsAtEntry addr st
  Set.finSetEvents e_at_centry (b.bottomEventsAtEntry_finite addr st) |>.toList

lemma Behaviour.listBottomEventsAtEntry_complete (b : Behaviour) (addr : Addr) (st : Struct) :
  ∀ {e : Event}, (e ∈ b.listBottomEventsAtEntry addr st) ↔ (e ∈ b.es ∧ e.isBottomAtEntry addr st b) := by
  simp [listBottomEventsAtEntry, Event.isBottomAtEntry, Set.finSetEvents]
  intro e; constructor <;> exact fun a ↦ a

def List.isOrdered {α} (l : List α) (r : α → α → Prop): Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

structure Behaviour.BottomPredecessor (b : Behaviour) (e_pred e_succ : Event) : Prop where
  sameEntry : Event.sameEntry
  behavePred : Behaviour.Predecessor
  predBottom : b.IsBottomEvent e_pred
  succBottom : b.IsBottomEvent e_succ

/-
def Event.isBottomEvent (e : Event) : Prop := ¬ ∃ e' : Event, e'.Encapsulates e

structure Event.BottomPredecessor (e_pred e_succ : Event) : Prop where
  sameEntry : Event.sameEntry
  behavePred : e_pred.Predecessor e_succ
  predBottom : e_pred.isBottomEvent
  succBottom : e_succ.isBottomEvent
-/

instance : DecidableRel Event.OrderedBefore := by
  unfold Event.OrderedBefore
  infer_instance

/- NOTE: This requires assumptions (b, hsame_entry, and so on..) that means instance isn't used by IsTotal Event Event.OrderedBefore. -/
instance Event.OrderedBefore.instIsTotal (b : Behaviour) (hsame_entry : Event.sameEntry) (hentry_ordered : Event.AtEntryOrdered) : IsTotal Event Event.OrderedBefore := by
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

/- NOTE: To be an instance of IsTotal, there can't be any assumptions, like the following below. -/
instance Event.OrderedBefore.instIsTotal' : IsTotal Event Event.OrderedBefore := by sorry

/- NOTE: Likewise, this is also not a valid instance of IsTotal. -/
instance Behaviour.BottomPredecessor.instIsTotal (b : Behaviour) (hbottom : Behaviour.bottomEvent) (hpred : Behaviour.Predecessor) (hsame_entry : Event.sameEntry) : IsTotal Event (b.BottomPredecessor) := by
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

/- NOTE: BottomPredecessor is a structure, so can't be a DecidableRel. -/
instance Behaviour.BottomPredecessor.instDecidableRel (b : Behaviour) : DecidableRel (b.BottomPredecessor) := by
  unfold DecidableRel
  intro e₁ e₂
  -- infer_instance
  sorry

def Behaviour.sortedListBottomEventsAtEntry (b : Behaviour) (addr : Addr) (st : Struct) : Prop := b.listBottomEventsAtEntry addr st |>.Sorted b.BottomPredecessor

structure Behaviour.sortedListEventsAtEntry : Prop where
  bottom_sorted (b : Behaviour) (addr : Addr) (st : Struct) : b.sortedListBottomEventsAtEntry addr st

def List.sortedListBottomEventsAtEntry (l : List Event) (b : Behaviour) : Prop := l |>.Sorted b.BottomPredecessor

structure List.sortedListEventsAtEntry : Prop where
  bottom_sorted (l : List Event) (b : Behaviour) : l.sortedListBottomEventsAtEntry b

noncomputable def Behaviour.sortedEventsAtEntry' (b : Behaviour) (addr : Addr) (st : Struct) : List Event := b.listBottomEventsAtEntry addr st |>.insertionSort Event.OrderedBefore

lemma Behaviour.eventsAtCacheEntry_total_order (b : Behaviour) (addr : Addr) (st : Struct)
  (hbottom_sorted : List.sortedListEventsAtEntry) :
  -- b.listBottomEventsAtEntry addr st |>.isOrdered (Event.OrderedBefore)
  let bes := b.listBottomEventsAtEntry addr st
  let es := bes.insertionSort Event.OrderedBefore
  es |>.isOrdered (b.BottomPredecessor)
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

lemma Behaviour.eventsAtCacheEntry_total_order' (b : Behaviour) (addr : Addr) (st : Struct)
  (hbottom_sorted : Behaviour.sortedListEventsAtEntry) :
  let bes := b.listBottomEventsAtEntry addr st
  let es := bes.insertionSort Event.OrderedBefore
  es |>.isOrdered (Event.OrderedBefore)
  -- b.listBottomEventsAtEntry addr st |>.isOrdered (b.BottomPredecessor)
  -- probably `Event.OrderedBefore` is not the right order though! or is it? not sure you've define the order on events that these are ordered by?
:= by
  unfold List.isOrdered
  intro bes es i j
  apply Iff.intro
  . case mp =>
    simp[List.sorted_insertionSort Event.OrderedBefore bes] -- at es
    have h := List.sorted_insertionSort Event.OrderedBefore es
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

def List.stateAfter (es : List Event) (init : EntryState) : EntryState := match es with
  | [] => init
  | e :: es' => es'.stateAfter (e.SucceedingState init)

def List.stateAtE (es : List Event) (e : Event) (init : EntryState) : EntryState :=
  List.stateAfter (es.splitAt (es.indexesOf e).head!).1 init

/- Def 2.33 Behaviour.StateBefore -/
noncomputable def Behaviour.stateBefore (b : Behaviour) (e : Event) (init : EntryState): EntryState :=
  b.listBottomEventsAtEntry e.addr e.struct |>.insertionSort Event.OrderedBefore |>.stateAtE e init

noncomputable def Behaviour.stateAfter (b : Behaviour) (e : Event) (init : EntryState): EntryState :=
  e.SucceedingState (b.stateBefore e init)

/-
noncomputable def Behaviour.StateBefore (b : Behaviour) (e : Event) (haddress_ordered : Event.AtEntryOrdered) (s_i : EntryState)
: EntryState :=
  let e_pred? := b.PreviousEvent e haddress_ordered
  match e_pred? with
  | .none => s_i
  | .some e_pred =>
    let entry_state_pred_pred := b.StateBefore e_pred haddress_ordered s_i
    e_pred.SucceedingState entry_state_pred_pred
-/

def CacheEvent.stateUpgradeMayEncapsulate (e₁ e₂ : CacheEvent) (s₁ : State) : Prop :=
  e₁.WithoutCoherentPermissions s₁ ∧ e₂.External → (e₁.Ordered e₂ ∨ e₁.Encapsulates e₂)

inductive CacheEvent.OrderedOrEncapsulates (e₁ e₂ : CacheEvent) (b : Behaviour) (init : EntryState) : Prop
| orderedOrEncapsulates (s₁ s₂ : State) :
  e₁.stateUpgradeMayEncapsulate e₂ (b.stateBefore (Event.cacheEvent e₁) init).cache ∨
  e₂.stateUpgradeMayEncapsulate e₁ (b.stateBefore (Event.cacheEvent e₂) init).cache →
  CacheEvent.OrderedOrEncapsulates e₁ e₂ b init
| ordered : e₁.Ordered e₂ → CacheEvent.OrderedOrEncapsulates e₁ e₂ b init

/-- Axiom 2 (Second half) Certain Request Events may encapusulate External Events. -/
structure CacheEvent.EncapAnother (e₁ e₂ : CacheEvent) (b : Behaviour) (init : EntryState) : Prop where
  sameCacheEntry : e₁.sameCacheEntry e₂
  orderOrEncap : CacheEvent.OrderedOrEncapsulates e₁ e₂ b init
