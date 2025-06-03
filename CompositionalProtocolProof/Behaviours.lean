import CompositionalProtocolProof.EventRelations

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
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (e_succ : Event) :
  let imm_bottom_preds := b.ImmBottomPredecessors e_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  cases b
  case mk es =>
    -- cases es
    -- unfold ImmBottomPredecessors at imm_bottom_preds
  sorry
