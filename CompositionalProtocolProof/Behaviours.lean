import CompositionalProtocolProof.EventRelations
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Canonical

structure Behaviour where
  es : Set Event
  finite : Finite es
  -- es : Finset Event

def Behaviour.OrderedBetween : Behaviour → Event → Event → Set Event
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween e_pred e_succ}

def Behaviour.NoIntermediateEvent (b : Behaviour) (e_pred e_succ : Event) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅

structure Behaviour.ImmediatePredecessorConstraint (b : Behaviour) (e_pred e_succ : Event) where
  isPred : e_pred.Predecessor e_succ
  noIntermediate : b.NoIntermediateEvent e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es
  -- succInB : e_succ ∈ b.es

abbrev Behaviour.IsNotEncapByEvent (b : Behaviour) (e : Event) : Prop := {e' ∈ b.es | e'.Encapsulates e} = ∅

def Behaviour.IsBottomEvent (b : Behaviour) (e : Event) : Prop := b.IsNotEncapByEvent e

structure CacheEvent.BottomAreOrdered (e₁ e₂ : CacheEvent) (b : Behaviour) : Prop where
  sameCacheEntry : e₁.sameCacheEntry e₂
  e₁Bottom : b.IsBottomEvent (Event.cacheEvent e₁)
  e₂Bottom : b.IsBottomEvent (Event.cacheEvent e₂)
  ordered : e₁.Ordered e₂

structure Behaviour.IsImmediateBottomPred (b : Behaviour) (e_pred e_succ : Event) where
  isImmPred : b.ImmediatePredecessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_pred

/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour → Event → Event → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour → Event → Set Event
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

structure Event.AtEntryOrdered where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent), DirectoryEvent.AreOrdered e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent), ∀ b : Behaviour, CacheEvent.BottomAreOrdered e₁ e₂ b

lemma Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction {es_pred₁ es_pred₂ es_succ : Event} {b : Behaviour}
(he₁_b : b.IsImmediateBottomPred es_pred₁ es_succ) (he₂_b : b.IsImmediateBottomPred es_pred₂ es_succ)
(hes₁_ordered_es₂ : es_pred₁.Ordered es_pred₂)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmPred.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₁_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₁_no_intermediate_to_e_suc
    simp at he₁_no_intermediate_to_e_suc
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
    unfold Behaviour.ImmediatePredecessorConstraint at he₂_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₂_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₂_no_intermediate_to_e_suc
    simp at he₂_no_intermediate_to_e_suc
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

lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (es_succ : Event)
  (es_pred₁ es_pred₂ : Event) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomPred es_pred₁ es_succ) (he₂_b : b.IsImmediateBottomPred es_pred₂ es_succ) :
  es_pred₁ = es_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b's NoIntermediatePredecessor.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : es_pred₁, h_pred₂ : es_pred₂ with
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

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir

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
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (es_succ : Event)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_preds := b.ImmBottomPredecessors es_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique b es_succ e₁ e₂
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

lemma Behaviour.immediate_bottom_predecessor_satisfying_p_unique (b : Behaviour) (es_succ : Event)
  (es_pred₁ es_pred₂ : Event) (p : Event → Prop) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomPredSatisfyingProp es_pred₁ es_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp es_pred₂ es_succ p) :
  es_pred₁ = es_pred₂ := by
    have he₁_b' : b.IsImmediateBottomPred es_pred₁ es_succ := by
      constructor
      exact he₁_b.isImmBottomPred.isImmPred
      exact he₁_b.isImmBottomPred.isBottom
    have he₂_b' : b.IsImmediateBottomPred es_pred₂ es_succ := by
      constructor
      exact he₂_b.isImmBottomPred.isImmPred
      exact he₂_b.isImmBottomPred.isBottom

    apply Behaviour.immediate_bottom_predecessor_unique b es_succ es_pred₁ es_pred₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 1, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_predecessor_satisfying_p_empty_or_unique (b : Behaviour) (es_succ : Event) (p : Event → Prop)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_preds := b.ImmBottomPredecessorsSatisfyingP es_succ p; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_satisfying_p_unique b es_succ e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Now define the immediate bottom successor. -/

structure Behaviour.ImmediateSuccessorConstraint (b : Behaviour) (e_pred e_succ : Event) where
  isSucc : e_pred.Successor e_succ
  noIntermediate : b.NoIntermediateEvent e_pred e_succ
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

lemma Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction {es_pred es_succ₁ es_succ₂ : Event} {b : Behaviour}
(he₁_b : b.IsImmediateBottomSucc es_pred es_succ₁) (he₂_b : b.IsImmediateBottomSucc es_pred es_succ₂)
(hes₁_ordered_es₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he_no_intermediate_to_e_suc₂ := he₂_b.isImmSucc.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he_no_intermediate_to_e_suc₂
    unfold Behaviour.NoIntermediateEvent at he_no_intermediate_to_e_suc₂
    unfold Behaviour.OrderedBetween at he_no_intermediate_to_e_suc₂
    simp at he_no_intermediate_to_e_suc₂
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
    unfold Behaviour.ImmediatePredecessorConstraint at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₁_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₁_no_intermediate_to_e_suc
    simp at he₁_no_intermediate_to_e_suc
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

lemma Behaviour.immediate_bottom_successor_unique (b : Behaviour) (es_pred : Event)
  (es_succ₁ es_succ₂ : Event) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomSucc es_pred es_succ₁) (he₂_b : b.IsImmediateBottomSucc es_pred es_succ₂) :
  es_succ₁ = es_succ₂ := by
    by_contra h_e_pred_diff
    match h_succ₁ : es_succ₁, h_succ₂ : es_succ₂ with
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

      match hsucc : es_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmSucc.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmSucc.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_pred with
      | .directoryEvent de_succ => simp at h_e_succ_is_cache
      | .cacheEvent ce_succ => simp at h_e_succ_is_dir

lemma Behaviour.immediate_bottom_successor_empty_or_unique (b : Behaviour) (es_pred : Event)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_succs := b.ImmBottomSuccessors es_pred; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_unique b es_pred e₁ e₂
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

lemma Behaviour.immediate_bottom_successor_satisfying_p_unique (b : Behaviour) (es_pred : Event)
  (es_succ₁ es_succ₂ : Event) (p : Event → Prop) (haddress_ordered : Event.AtEntryOrdered)
  (he₁_b : b.IsImmediateBottomSuccSatisfyingProp es_pred es_succ₁ p) (he₂_b : b.IsImmediateBottomSuccSatisfyingProp es_pred es_succ₂ p) :
  es_succ₁ = es_succ₂ := by
    have he₁_b' : b.IsImmediateBottomSucc es_pred es_succ₁ := by
      constructor
      exact he₁_b.isImmBottomSucc.isImmSucc
      exact he₁_b.isImmBottomSucc.isBottom
    have he₂_b' : b.IsImmediateBottomSucc es_pred es_succ₂ := by
      constructor
      exact he₂_b.isImmBottomSucc.isImmSucc
      exact he₂_b.isImmBottomSucc.isBottom

    apply Behaviour.immediate_bottom_successor_unique b es_pred es_succ₁ es_succ₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 2, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_successor (b : Behaviour) (es_pred : Event) (p : Event → Prop)
  (haddress_ordered : Event.AtEntryOrdered) :
  let imm_bottom_succs := b.ImmBottomSuccessorsSatisfyingP es_pred p; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_satisfying_p_unique b es_pred e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- TODO: Define encapsulate after defining event.
structure CacheEvent.EncapAnother (e₁ e₂ : CacheEvent) : Prop where
  sameCacheEntry : e₁.sameEntry e₂
-/

-- defs that'll be useful for defining when Cache Events encapsulate external not-bottom events
/- Comment out OrderedCacheEvents / CacheEvent.AreOrderedOrEncap
-- OrderedCacheEvents / CacheEvent.AreOrderedOrEncap are best defined in Behaviours.lean
def CacheEvent.stateUpgradeMayEncapsulate (e₁ e₂ : CacheEvent) (s₁ : State) : Prop :=
  e₁.WithoutCoherentPermissions s₁ ∧ e₂.External → (e₁.Ordered e₂ ∨ e₁.Encapsulates e₂)

inductive CacheEvent.OrderedOrEncapsulates (e₁ e₂ : CacheEvent) : Prop
| orderedOrEncapsulates (s₁ s₂ : State) : e₁.stateUpgradeMayEncapsulate e₂ s₁ ∨ e₂.stateUpgradeMayEncapsulate e₁ s₂ → CacheEvent.OrderedOrEncapsulates e₁ e₂
| ordered : e₁.Ordered e₂ → CacheEvent.OrderedOrEncapsulates e₁ e₂

/-- Axiom 2
Events at the same address at a cache are ordered, or may encapsulate an external event to the same address.
-/
structure CacheEvent.AreOrderedOrEncap (e₁ e₂ : CacheEvent) (s₁ s₂ : State) : Prop where
  sameCache : e₁.cid = e₂.cid
  sameAddr : e₁.a = e₂.a
  orderOrEncap : CacheEvent.OrderedOrEncapsulates e₁ e₂

def OrderedCacheEvents' (e₁ e₂ : CacheEvent) (s₁ s₂ : State) : Prop :=
  e₁.cid = e₂.cid → e₁.a = e₂.a →
  if e₁.NoEncapSameAddressDowngrade s₁ ∧ e₂.NoEncapSameAddressDowngrade s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)
  else if e₁.WithoutCoherentPermissions s₁ ∧ e₂.External then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₁.Encapsulates e₂)
  else if e₁.External ∧ e₂.WithoutCoherentPermissions s₂ then (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁ ∨ e₂.Encapsulates e₁)
  else (e₁.OrderedBefore e₂ ∨ e₂.OrderedBefore e₁)
-/

/-- Consider finite behaviours. -/
noncomputable def Behaviour.finSetEvents (b : Behaviour) : Finset Event := Set.Finite.toFinset b.finite

-- def Behaviour.eventsAtEntry (b : Behaviour)

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

def Behaviour.eventsAtCacheEntry (b : Behaviour) (addr : Addr) (cid : CacheId) (haddress_ordered : Event.AtEntryOrdered) : List Event :=
  let e_at_centry := {e ∈ b.es | e.addr = addr ∧ e.atCid cid}
  /- Don't know how to use e_at_centry and produce an ordered list? -/
  sorry

/- Def 2.33 Behaviour.StateBefore -/
noncomputable def Behaviour.StateBefore (b : Behaviour) (e : Event) (haddress_ordered : Event.AtEntryOrdered) (s_i : EntryState)
: EntryState :=
  let e_pred? := b.PreviousEvent e haddress_ordered
  match e_pred? with
  | .none => s_i
  | .some e_pred =>
    let entry_state_pred_pred := b.StateBefore e_pred haddress_ordered s_i
    e_pred.SucceedingState entry_state_pred_pred
termination_by sizeOf (b.ImmBottomPredecessors e)
-- decreasing_by sizeOf (b.ImmBottomPredecessors e)
