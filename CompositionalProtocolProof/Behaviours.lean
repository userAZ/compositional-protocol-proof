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

-- NOTE: Remember to use OrderedCacheEvents and OrderedDirectoryEvents at some point.
lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (e_succ : Event) (hsucc_in_b : e_succ ∈ b.es)
  (e_pred₁ e_pred₂ : Event) (he₁_b : b.IsImmediateBottomPred e_pred₁ e_succ) (he₂_b : b.IsImmediateBottomPred e_pred₁ e_succ) :
  e_pred₁ = e_pred₂ := by
    sorry -- this is the "multiple" case in Lemma 1.

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
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (e_succ : Event) (hsucc_in_b : e_succ ∈ b.es) :
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
      exact And.right he₁
      exact And.right he₁
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)
