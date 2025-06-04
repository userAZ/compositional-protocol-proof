import CompositionalProtocolProof.EventRelations
import Canonical

structure Behaviour where
  es : Set Event

def Behaviour.OrderedBetween : Behaviour → Event → Event → Set Event
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween e_pred e_succ}

def Behaviour.NoIntermediatePredecessor (b : Behaviour) (e_pred e_succ : Event) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅

structure Behaviour.ImmediatePredecessorConstraint (b : Behaviour) (e_pred e_succ : Event) where
  isPred : e_pred.Predecessor e_succ
  noIntermediate : b.NoIntermediatePredecessor e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es

def Behaviour.ImmediatePredecessor : Behaviour → Event → Event → Prop
| b, e_pred, e_succ => b.ImmediatePredecessorConstraint e_pred e_succ

abbrev Behaviour.IsNotEncapByEvent (b : Behaviour) (e : Event) : Prop := {e' ∈ b.es | e'.Encapsulates e} = ∅

def Behaviour.IsBottomEvent (b : Behaviour) (e : Event) : Prop := b.IsNotEncapByEvent e

structure Behaviour.IsImmediateBottomPred (b : Behaviour) (e_pred e_succ : Event) where
  isImmPred : b.ImmediatePredecessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_pred

-- TODO: also write a version with a constraint φ on e_pred.
/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour → Event → Event → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour → Event → Set Event
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

/-
lemma Set.e_in_s_nonempty {α : Type} (s : Set α) (e : α) (he_in_s : e ∈ s) : Nonempty s := by
  exists e

lemma Set.nonempty_is_not_empty {α : Type} (s : Set α) : Nonempty s → ¬s = ∅ := by
  intro h_nonempty
  apply Set.nonempty_iff_ne_empty'.mp
  exact h_nonempty
-/

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


  -- | .directoryEvent de, .cacheEvent ce,  => sorry
  -- | .cacheEvent ce, .directoryEvent de => sorry


structure OrderedAddressEvents where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent), OrderedDirectoryEvents e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent), ∀ (s₁ s₂ : State), OrderedCacheEvents e₁ e₂ s₁ s₂

-- NOTE: Remember to use OrderedCacheEvents and OrderedDirectoryEvents at some point.
lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (e_succ : Event) (hsucc_in_b : e_succ ∈ b.es)
  (e_pred₁ e_pred₂ : Event) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomPred e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred e_pred₂ e_succ) :
  e_pred₁ = e_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : e_pred₁, h_pred₂ : e_pred₂ with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      -- Use OrderedDirectoryEvents to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      have e₁_same_addr_e_succ := he₁_b.isImmPred.sameAddress
      have e₂_same_addr_e_succ := he₂_b.isImmPred.sameAddress
      have e₁_same_addr_e₂ := Event.same_address_reflexive e₁_same_addr_e_succ e₂_same_addr_e_succ
      have de₁_de₂_ordered := de₁_de₂_ordered_prop e₁_same_addr_e₂

      cases de₁_de₂_ordered
      . case inl h_de₁_o_de₂ =>
        have he₁_is_de₁ : e_pred₁.fromDirectoryEvent de₁ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₁]
        have he₂_is_de₂ : e_pred₂.fromDirectoryEvent de₂ := by
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
        simp at e₂_o_e_succ
        rw [← h_pred₂] at e₂_o_e_succ

        apply he₁_no_intermediate_to_e_suc
        apply he₂_b.isImmPred.predInB

        have e₂_between_e₁_e_succ : e_pred₂.OrderedBetween e_pred₁ e_succ := {pred := e₁_o_e₂, succ := e₂_o_e_succ}
        rw [h_pred₁] at e₂_between_e₁_e_succ
        rw [h_pred₂] at e₂_between_e₁_e_succ
        exact e₂_between_e₁_e_succ
      . case inr h_de₂_o_de₁ =>
        have he₁_is_de₁ : e_pred₁.fromDirectoryEvent de₁ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₁]
        have he₂_is_de₂ : e_pred₂.fromDirectoryEvent de₂ := by
          unfold Event.fromDirectoryEvent
          simp [h_pred₂]
        have e₂_o_e₁ := DirectoryEvent.ordered_events he₂_is_de₂ he₁_is_de₁ h_de₂_o_de₁
        sorry
    | .cacheEvent ce₁, .cacheEvent ce₂ => sorry
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmPred.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match e_succ with
      | .directoryEvent de_succ => contradiction
      | .cacheEvent ce_succ => contradiction
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure

      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match e_succ with
      | .directoryEvent de_succ => contradiction
      | .cacheEvent ce_succ => contradiction

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
 (hsucc_in_b : e_succ ∈ b.es) (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_preds := b.ImmBottomPredecessors e_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : Event), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique b e_succ hsucc_in_b e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)
