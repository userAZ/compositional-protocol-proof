import CompositionalProtocolProof.EventRelations
import Canonical

structure EventState where
  e : Event
  s : State ⊕ DirectoryState

def EventState.stateWellFormed : EventState → Prop
| ⟨.cacheEvent _, s⟩ => match s with | .inl _ => true | .inr _ => false
| ⟨.directoryEvent _, s⟩ => match s with | .inl _ => false | .inr _ => true

structure Behaviour where
  es : Set EventState

def EventState.Ordered : EventState → EventState → Prop
| ⟨e₁, _⟩, ⟨e₂, _⟩ => e₁.Ordered e₂

structure EventState.OrderedBetween (e e_pred e_succ : EventState) where
  pred : e_pred.Ordered e := by simp
  succ : e.Ordered e_succ := by simp

def Behaviour.OrderedBetween : Behaviour → EventState → EventState → Set EventState
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween e_pred e_succ}

def Behaviour.NoIntermediatePredecessor (b : Behaviour) (e_pred e_succ : EventState) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅

def EventState.Predecessor : EventState → EventState → Prop
| ⟨e₁, _⟩, ⟨e₂, _⟩ => e₁.Predecessor e₂
def EventState.SameAddress : EventState → EventState → Prop
| ⟨e₁, _⟩, ⟨e₂, _⟩ => e₁.SameAddress e₂
def EventState.SameStructure : EventState → EventState → Prop
| ⟨e₁, _⟩, ⟨e₂, _⟩ => e₁.SameStructure e₂

structure Behaviour.ImmediatePredecessorConstraint (b : Behaviour) (e_pred e_succ : EventState) where
  isPred : e_pred.Predecessor e_succ
  noIntermediate : b.NoIntermediatePredecessor e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es

def Behaviour.ImmediatePredecessor : Behaviour → EventState → EventState → Prop
| b, e_pred, e_succ => b.ImmediatePredecessorConstraint e_pred e_succ

def EventState.Encapsulates : EventState → EventState → Prop
| ⟨e₁, _⟩, ⟨e₂, _⟩ => e₁.Encapsulates e₂

abbrev Behaviour.IsNotEncapByEvent (b : Behaviour) (e : EventState) : Prop := {e' ∈ b.es | e'.Encapsulates e} = ∅

def Behaviour.IsBottomEvent (b : Behaviour) (e : EventState) : Prop := b.IsNotEncapByEvent e

structure Behaviour.IsImmediateBottomPred (b : Behaviour) (e_pred e_succ : EventState) where
  isImmPred : b.ImmediatePredecessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_pred

-- TODO: also write a version with a constraint φ on e_pred.
/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour → EventState → EventState → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour → EventState → Set EventState
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

structure OrderedAddressEvents where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent), OrderedDirectoryEvents e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent), ∀ (s₁ s₂ : State), OrderedCacheEvents e₁ e₂ s₁ s₂

-- NOTE: Remember to use OrderedCacheEvents and OrderedDirectoryEvents at some point.
lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (es_succ : EventState) (hsucc_in_b : e_succ ∈ b.es)
  (es_pred₁ es_pred₂ : EventState) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomPred es_pred₁ es_succ) (he₂_b : b.IsImmediateBottomPred es_pred₂ es_succ) :
  es_pred₁ = es_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : es_pred₁.e, h_pred₂ : es_pred₂.e with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      -- Use OrderedDirectoryEvents to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      have e₁_same_addr_e_succ := he₁_b.isImmPred.sameAddress
      have e₂_same_addr_e_succ := he₂_b.isImmPred.sameAddress
      have es₁_same_addr_es₂ := Event.same_address_reflexive e₁_same_addr_e_succ e₂_same_addr_e_succ
      rw [h_pred₁, h_pred₂] at es₁_same_addr_es₂
      have de₁_de₂_ordered := de₁_de₂_ordered_prop es₁_same_addr_es₂

      cases de₁_de₂_ordered
      . case inl h_de₁_o_de₂ =>
        have he₁_is_de₁ : es_pred₁.e.fromDirectoryEvent de₁ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₁]
        have he₂_is_de₂ : es_pred₂.e.fromDirectoryEvent de₂ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₂]
        have e₁_o_e₂ := DirectoryEvent.ordered_events he₁_is_de₁ he₂_is_de₂ h_de₁_o_de₂
        /- Now use the definition of he₁_b and he₂_b to state that there is no intermediately ordered
        event e₃. But we have e₁ and e₂ (pred) ordered, and both are ordered before e_succ → Contradiction -/
        -- NOTE: Surely there must be a way to clean up this proof.
        have he₁_no_intermediate_to_e_suc := he₁_b.isImmPred.noIntermediate
        unfold Behaviour.ImmediatePredecessorConstraint at he₁_no_intermediate_to_e_suc
        unfold Behaviour.NoIntermediatePredecessor at he₁_no_intermediate_to_e_suc
        unfold Behaviour.OrderedBetween at he₁_no_intermediate_to_e_suc
        simp at he₁_no_intermediate_to_e_suc
        have e₂_o_e_succ := he₂_b.isImmPred.isPred
        unfold Event.Predecessor at e₂_o_e_succ
        unfold EventState.Predecessor at e₂_o_e_succ
        simp at e₂_o_e_succ

        apply he₁_no_intermediate_to_e_suc
        apply he₂_b.isImmPred.predInB

        have e₂_between_e₁_e_succ : es_pred₂.OrderedBetween es_pred₁ es_succ := {pred := e₁_o_e₂, succ := e₂_o_e_succ}
        exact e₂_between_e₁_e_succ
      . case inr h_de₂_o_de₁ =>
        have he₁_is_de₁ : es_pred₁.e.fromDirectoryEvent de₁ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₁]
        have he₂_is_de₂ : es_pred₂.e.fromDirectoryEvent de₂ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₂]
        have e₂_o_e₁ := DirectoryEvent.ordered_events he₂_is_de₂ he₁_is_de₁ h_de₂_o_de₁

        /- Now we have the hypothesis that e₂ is ordered with e₁. Show there's a contradiction in e_pred₂'s property NoIntermediatePred. -/
        have he₂_no_intermediate_to_e_suc := he₂_b.isImmPred.noIntermediate
        unfold Behaviour.ImmediatePredecessorConstraint at he₂_no_intermediate_to_e_suc
        unfold Behaviour.NoIntermediatePredecessor at he₂_no_intermediate_to_e_suc
        unfold Behaviour.OrderedBetween at he₂_no_intermediate_to_e_suc
        simp at he₂_no_intermediate_to_e_suc
        have e₂_o_e_succ := he₂_b.isImmPred.isPred
        unfold Event.Predecessor at e₂_o_e_succ
        unfold EventState.Predecessor at e₂_o_e_succ
        simp at e₂_o_e_succ

        apply he₂_no_intermediate_to_e_suc
        apply he₁_b.isImmPred.predInB
        constructor
        unfold autoParam
        . case a.pred =>
          exact e₂_o_e₁
        . case a.succ =>
          unfold autoParam

          have e₁_o_e_succ := he₁_b.isImmPred.isPred
          unfold Event.Predecessor at e₁_o_e_succ
          exact e₁_o_e_succ
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      /- Part 1. Use OrderedCacheEvents to show that ce₁ and ce₂ (which are bottom predecessors to e_succ)
      are always ordered. Part 2. This is a contradiction with ImmediateBottomPred's NoIntermediatePred. -/
      -- Part 1. ce₁ and ce₂ are OrderedCacheEvents
      cases es_pred₁.s
      . case inl s₁ =>
        cases es_pred₂.s
        . case inl s₂ =>
          have hce₁_o_ce₂ := haddress_ordered.cache_ordered ce₁ ce₂ s₁ s₂  -- need state s₁ s₂ that ce₁ and ce₂ are made on.
          -- Same cid, e_pred₁ e_pred₂
          have hce₁_cid_csucc := he₁_b.isImmPred.sameStructure
          have hce₂_cid_csucc := he₂_b.isImmPred.sameStructure
          have es₁_same_structure_es₂ := Event.same_structure_reflexive hce₁_cid_csucc hce₂_cid_csucc
          unfold EventState.SameStructure at es₁_same_structure_es₂
          unfold Event.SameStructure at es₁_same_structure_es₂
          rw [h_pred₁] at es₁_same_structure_es₂
          unfold CacheEvent.SameCache at es₁_same_structure_es₂
          unfold DirectoryEvent.SameStructure at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          unfold Event.SameStructureRelation at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          -- Same Address, e_pred₁ e_pred₂
          have hce₁_a_csucc := he₁_b.isImmPred.sameAddress
          have hce₂_a_csucc := he₂_b.isImmPred.sameAddress
          have es₁_same_addr_es₂ := Event.same_address_reflexive hce₁_a_csucc hce₂_a_csucc
          unfold EventState.SameAddress at es₁_same_addr_es₂
          unfold Event.SameAddress at es₁_same_addr_es₂
          rw [h_pred₁] at es₁_same_addr_es₂
          unfold CacheEvent.SameAddress at es₁_same_addr_es₂
          unfold DirectoryEvent.SameAddress at es₁_same_addr_es₂
          unfold Event.SameStructureRelation at es₁_same_addr_es₂
          simp at es₁_same_addr_es₂

          rw [h_pred₂] at es₁_same_structure_es₂ es₁_same_addr_es₂
          simp at es₁_same_structure_es₂ es₁_same_addr_es₂

          -- have the big if then else from OrderedCacheEvents:
          have ordered_ite := hce₁_o_ce₂ es₁_same_structure_es₂ es₁_same_addr_es₂

          /- Show for all cases of ce₁ ce₂ s₁ s₂, ce₁ and ce₂ are either:
            1. ordered (contradiction with NoIntermediatePred)
            2. one encapsulates another (contradiction with isBottom)
          -/
          sorry
        .case inr _ =>
          sorry -- Show false by EventState.stateWellFormed. Need to include it in the premise of this Lemma.
      . case inr _ =>
        sorry
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmPred.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_pred₂] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_pred₁] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_pred₁] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_pred₂] at h_e_succ_is_dir
        simp at h_e_succ_is_dir

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
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (es_succ : EventState)
 (hsucc_in_b : es_succ ∈ b.es) (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_preds := b.ImmBottomPredecessors es_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : EventState), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique b es_succ hsucc_in_b e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)
