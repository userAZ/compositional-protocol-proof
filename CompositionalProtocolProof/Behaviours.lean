import CompositionalProtocolProof.EventRelations

structure Behaviour where
  -- rels : Set Prop -- Prop a bad idea
  rels : Set EventRelation

/- Think if i need this for defining immediate predecessor or not.-/
/-
def Behaviour.Events : Behaviour → Set Event
| b =>
  let y := {e ∈ Event | e ∈ b.rels.Events}
  sorry
-/

-- Continue this later.
/-
def EventRelation.PredOfEvent : EventRelation → Event → Event
| er, e => match er with
  | .encapsulates _ _ _ =>  --{e₁, e₂}
  | .ordered e₁ e₂ _ => e_pred = e₁ ∧ e_succ = e₂ -- {e₁, e₂}
  | .programOrdered e₁ e₂ _ => e_pred = e₁ ∧ e_succ = e₂ -- {e₁, e₂}
  | .fieldMatch _ _ _ _ => false -- {e₁}
  | .noFieldMatch _ _ _ _ => false -- {e₁}
  | .matchingFields _ _ _ _ => false -- {e₁, e₂}
  | .noMatchingFields _ _ _ _ => false -- {e₁, e₂}

def Behaviour.PredOfEvent : Behaviour → Event → Prop
| b, e_succ => b.rels.image

def Behaviour.Predecessor : Behaviour → Event → Set Event
| b, e =>
  let ex := {e ∈ Event | b.rels.PredOfEvent e}
  sorry
-/

def Behaviour.ImmediatePredecessor : Behaviour → Event → Option Event
| b, e => sorry
  /- find e', where
    1. e' is Ordered with e.
    2. there is no e'' where e' is Ordered with e'', and e'' is Ordered with e.
  -/
  -- start with defining all events in b
  -- then define all events in b that are Ordered with e (can be related transitively (indirectly) through encapsulates, or ordered)
  -- not sure how to proceed
