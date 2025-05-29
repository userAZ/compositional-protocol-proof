import CompositionalProtocolProof.EventRelations

structure Behaviour where
  -- rels : Set Prop -- Prop a bad idea
  rels : Set EventRelation

/- Think if i need this for defining immediate predecessor or not.-/
def Behaviour.Events : Behaviour → Set Event
| b =>
  let sets := b.rels.image EventRelation.Events;
  sorry

def Behaviour.ImmediatePredecessor : Behaviour → Event → Option Event
| b, e => sorry
  /- find e', where
    1. e' is Ordered with e.
    2. there is no e'' where e' is Ordered with e'', and e'' is Ordered with e.
  -/
  -- start with defining all events in b
  -- then define all events in b that are Ordered with e (can be related transitively (indirectly) through encapsulates, or ordered)
  -- not sure how to proceed
