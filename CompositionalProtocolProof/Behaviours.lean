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

-- TODO? define pred of event including transitivity from ordered and encapsulates relations.
def Behaviour.PredOfEvent : Behaviour → Event → Event → Prop
| b, e_pred, e_succ =>
  /- Direct predecessor case. -/
  ∃ er ∈ b.rels, er.DirectPredOfEvent e_pred e_succ
  /- TODO: or, a predecessor e_pred could be a predecessor to e_succ by transitivity (through EventRelation .ordered or .encapsulates)-/

/-
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
