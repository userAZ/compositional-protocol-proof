import CompositionalProtocolProof.EventRelations
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
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

structure Behaviour.Predecessor (b : Behaviour) (e_pred e_succ : Event) where
  sameEntry : e_pred.sameEntry e_succ
  isPred : e_pred.Predecessor e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

structure Behaviour.EntryImmediatePredecessor (b : Behaviour) (e_pred e_succ : Event) where
  sameEntry : e_pred.sameEntry e_succ
  behavePred : b.Predecessor e_pred e_succ
  noIntermediate : b.NoIntermediatePredecessor e_pred e_succ

/- Access properties nested deeper in Behaviour.ImmediatePredecessor -/
def Behaviour.EntryImmediatePredecessor.isPred {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred.Predecessor e_succ := hb_imm_pred.behavePred.isPred
def Behaviour.EntryImmediatePredecessor.predInB {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred ∈ b.es := hb_imm_pred.behavePred.predInB
def Behaviour.EntryImmediatePredecessor.sameStructure {b : Behaviour} {e_pred e_succ : Event} (hb_imm_pred : Behaviour.EntryImmediatePredecessor b e_pred e_succ)
: e_pred.sameStructure e_succ := hb_imm_pred.behavePred.sameEntry.sameStruct
structure Event.EncapAtSameStructure (e_bottom e : Event) : Prop where
  encap : e_bottom.Encapsulates e
  sameEntry : e_bottom.sameEntry e

abbrev Behaviour.IsNotEncapAtSameStruct (b : Behaviour) (e : Event) : Prop := ∀ e' ∈ b.es, ¬ e'.EncapAtSameStructure e

def Behaviour.IsBottomEvent (b : Behaviour) (e : Event) : Prop := b.IsNotEncapAtSameStruct e

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

noncomputable def Behaviour.listBottomEventsAtEntry (b : Behaviour) (addr : Addr) (st : Struct) : List Event :=
  /- If b.es is defined as a Finset Event (instead of Set Event),
  Lean complains about not being able to synthesize DecidablePred on e.atCid cid. Why? -/
  let e_at_centry := b.bottomEventsAtEntry addr st
  Set.finSetEvents e_at_centry (b.bottomEventsAtEntry_finite addr st) |>.toList

lemma Behaviour.listBottomEventsAtEntry_complete (b : Behaviour) (addr : Addr) (st : Struct) :
  ∀ {e : Event}, (e ∈ b.listBottomEventsAtEntry addr st) ↔ (e ∈ b.es ∧ e.isBottomAtEntry addr st b) := by
  simp [listBottomEventsAtEntry, Event.isBottomAtEntry, Set.finSetEvents]
  intro e; constructor <;> exact fun a ↦ a

def List.isOrdered {α} (l : List α) (r : α → α → Prop): Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

structure Behaviour.BottomPredecessor (b : Behaviour) (e_pred e_succ : Event) : Prop where
  sameEntry : e_pred.sameEntry e_succ
  behavePred : b.Predecessor e_pred e_succ
  predBottom : b.IsBottomEvent e_pred
  succBottom : b.IsBottomEvent e_succ

-- I also know that the events in b's list are at the same address, and entry

lemma Behaviour.eventsAtCacheEntry_at_st (b : Behaviour) (addr : Addr) (st : Struct) : let es := b.listBottomEventsAtEntry addr st;
∀ e ∈ es, e.atStruct st := by
  intro es e he_in_es
  unfold Event.atStruct
  split
  . case h_1 st =>
    unfold Event.isDirectoryEvent
    simp
    match e with
    | .directoryEvent de => simp
    | .cacheEvent ce =>
      simp
      simp [es] at he_in_es
      unfold listBottomEventsAtEntry at he_in_es
      unfold bottomEventsAtEntry at he_in_es
      simp at he_in_es
      sorry
  . case h_2 st cid =>
    sorry

lemma Behaviour.eventsAtCacheEntry_at_st' (b : Behaviour) (addr : Addr) (st : Struct) : let es := b.listBottomEventsAtEntry addr st;
∀ e ∈ es, e.struct = st := by
  intro es e he_in_es
  unfold Event.struct
  simp [es] at he_in_es
  unfold listBottomEventsAtEntry at he_in_es
  unfold bottomEventsAtEntry at he_in_es
  simp at he_in_es
  unfold Set.finSetEvents at he_in_es
  simp at he_in_es
  have e_at_struct := he_in_es.right.atStruct
  simp at e_at_struct
  unfold Event.atStruct at e_at_struct
  unfold Event.isCacheEventAtCid at e_at_struct
  simp at e_at_struct
  split
  . case h_1 e de =>
    match e with
    | .directoryEvent de' =>
      match st with
      | .directory => rfl
      | .cache cid => simp [e_at_struct]
    | .cacheEvent ce =>
      match st with
      | .directory => rfl
      | .cache cid => simp [e_at_struct]
  . case h_2 e cid =>
    match e with
    | .directoryEvent de' =>
      match st with
      | .directory =>
        simp at e_at_struct
        unfold Event.isDirectoryEvent at e_at_struct
        simp at e_at_struct
      | .cache cid => simp [e_at_struct]
    | .cacheEvent ce =>
      match st with
      | .directory =>
        simp at e_at_struct
        unfold Event.isDirectoryEvent at e_at_struct
        simp at e_at_struct
      | .cache cid => simp [e_at_struct]

lemma Behaviour.eventsAtCacheEntry_at_addr (b : Behaviour) (addr : Addr) (st : Struct) : let es := b.listBottomEventsAtEntry addr st;
∀ e ∈ es, e.addr = addr := by
  intro es e he_in_es
  simp [es] at he_in_es
  unfold listBottomEventsAtEntry at he_in_es
  unfold bottomEventsAtEntry at he_in_es
  simp at he_in_es
  unfold Set.finSetEvents at he_in_es
  simp at he_in_es
  exact he_in_es.right.addr

lemma Behaviour.eventsAtCacheEntry_same_entry (b : Behaviour) (addr : Addr) (st : Struct) : let es := b.listBottomEventsAtEntry addr st;
  ∀ e₁ ∈ es, ∀ e₂ ∈ es, e₁.sameEntry e₂ := by
  intro es e₁ he₁_in_es e₂ he₂_in_es
  constructor
  . case sameStruct =>
    constructor
    . case sameStruct =>
      have he₁_struct : e₁.struct = st := b.eventsAtCacheEntry_at_st' addr st e₁ he₁_in_es
      have he₂_struct : e₂.struct = st := b.eventsAtCacheEntry_at_st' addr st e₂ he₂_in_es
      have he₁_struct_e₂ : e₁.struct = e₂.struct := by simp [he₁_struct, he₂_struct]
      exact he₁_struct_e₂
  . case sameAddr =>
    have he₁_addr : e₁.addr = addr := b.eventsAtCacheEntry_at_addr addr st e₁ he₁_in_es
    have he₂_addr : e₂.addr = addr := b.eventsAtCacheEntry_at_addr addr st e₂ he₂_in_es
    have he₁_addr_e₂ : e₁.addr = e₂.addr := by simp [he₁_addr, he₂_addr]
    constructor
    . case sameStruct => exact he₁_addr_e₂

lemma Behaviour.eventsAtCacheEntry_total_order (b : Behaviour) (addr : Addr) (st : Struct)
  (hentry_ordered : Event.AtEntryOrdered) :
  b.listBottomEventsAtEntry addr st |>.isOrdered (b.BottomPredecessor)
  -- probably `Event.OrderedBefore` is not the right order though! or is it? not sure you've define the order on events that these are ordered by?
:= by
  unfold List.isOrdered
  unfold Behaviour.listBottomEventsAtEntry
  simp
  unfold Behaviour.bottomEventsAtEntry
  intro i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    unfold Set.finSetEvents
    constructor
    . case sameEntry =>
      constructor
      . case sameStruct =>
        constructor
        . case sameStruct =>
          unfold Event.struct
          split
          . case h_1 e₁ de₁ heq₁ =>
            split
            . case h_1 e₂ de₂ heq₂ => rfl
            . case h_2 e₂ ce₂ heq₂ =>
              -- i and j are at Address addr and Structure st. but the goal says they're not (directory vs. cache). show contradiction.
              unfold Set.finSetEvents at i j
              unfold Set.Finite.toFinset at i j
              simp at i j

              unfold Set.Finite.toFinset at heq₁ heq₂
              unfold Set.toFinset at heq₁ heq₂
              simp at heq₁ heq₂
              unfold Finset.map at heq₁ heq₂
              simp at heq₁ heq₂
              unfold Multiset.map at heq₁ heq₂
              simp at heq₁ heq₂
              unfold Finset.toList at heq₁ heq₂
              simp at heq₁ heq₂
              unfold Multiset.toList at heq₁ heq₂
              unfold Quot.liftOn at heq₁ heq₂
              unfold Quotient.out at heq₁ heq₂
              unfold Finset.univ at heq₁ heq₂
              unfold Fintype.elems at heq₁ heq₂
              unfold Set.Finite.fintype at heq₁ heq₂
              simp at heq₁ heq₂

              unfold Fintype.card at i j
              unfold Finset.univ at i j
              unfold Fintype.elems at i j
              sorry
          . case h_2 e₁ ce₁ heq₁ =>
            -- unfold Event.isBottomAtEntry at i j
            sorry
      . case sameAddr =>
        sorry
    . case behavePred =>
      constructor
      . case sameEntry =>
        sorry
      . case isPred =>
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
    sorry

def List.stateAfter (es : List Event) (init : EntryState) : EntryState := match es with
  | [] => init
  | e :: es' => es'.stateAfter (e.SucceedingState init)

def List.stateAtE (es : List Event) (e : Event) (init : EntryState) : EntryState :=
  List.stateAfter (es.splitAt (es.indexesOf e).head!).1 init

noncomputable def Behaviour.stateBefore' (b : Behaviour) (e : Event) (init : EntryState): EntryState :=
  b.listBottomEventsAtEntry e.addr e.struct |>.insertionSort Event.OrderedBefore |>.stateAtE e init

noncomputable def Behaviour.stateAfter (b : Behaviour) (e : Event) (init : EntryState): EntryState :=
  e.SucceedingState (b.stateBefore' e init)

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
