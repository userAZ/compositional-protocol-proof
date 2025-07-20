import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

-- [NOTE] Probably want a lemma about subsingleton input
open scoped Classical in
noncomputable def Set.toOption {α} (s : Set α) : Option (α) :=
  by classical exact
  if h : Nonempty s then some h.some
  else none

noncomputable def Behaviour.eventToState (b : Behaviour n) (init : InitialSystemState n) (e? : Option (Event n)) (cid : CacheId n) : State :=
  match e? with
  | .none => init.stateAtCid n cid
  | .some e => (b.stateAfter n (init.stateAt n e) e).cache

/-- Project the (Subsingleton) set of events at CacheId `cid` that's the immediate Finishes Before event of an Event `e`.
(although the title is "events", the set is Subsingleton, as shown by Lemma
`Behaviour.immediateFinishesBeforeEvents_is_subsingleton` in Behaviours.lean) -/
def Behaviour.eventsEndingImmediatelyBeforeEvent (b : Behaviour n) (e : Event n) (cid : CacheId n) :=
  {e' ∈ b.eventsEndingImmediatelyBefore n e | e.atCid n cid}

-- [NOTE] may need to prove finite
def ProtocolInstance.cidSetAtProtocolInstance (pi : ProtocolInstance) := {c : CacheId n | c.atProtocol n pi}

def CacheId.mkCacheGlobalP (m : Fin 2) : CacheId n := CacheId.cache (.globalP m)
def CacheId.mkCacheCluster1 (m : Fin n) : CacheId n := CacheId.cache (.cluster1 m)
def CacheId.mkCacheCluster2 (m : Fin n) : CacheId n := CacheId.cache (.cluster2 m)
def CacheId.mkProxy (n : Nat) (p : ProtocolInstance) : CacheId n := CacheId.proxy p

instance CacheId.mkCacheGlobalP_inj : Function.Injective (CacheId.mkCacheGlobalP n) := by
  simp[Function.Injective]
  simp[mkCacheGlobalP]
instance CacheId.mkCacheCluster1_inj : Function.Injective (CacheId.mkCacheCluster1 n) := by
  simp[Function.Injective]
  simp[mkCacheCluster1]
instance CacheId.mkCacheCluster2_inj : Function.Injective (CacheId.mkCacheCluster2 n) := by
  simp[Function.Injective]
  simp[mkCacheCluster2]
instance CacheId.mkCacheProxy_inj : Function.Injective (CacheId.mkProxy n) := by
  simp[Function.Injective]
  simp[mkProxy]

instance CacheId.isFintype : Fintype (CacheId n) where
  elems := by
    constructor
    case val =>
      exact (
        (List.finRange 2).map (CacheId.mkCacheGlobalP n ·) ++
        (List.finRange n).map (CacheId.mkCacheCluster1 n ·) ++
        (List.finRange n).map (CacheId.mkCacheCluster2 n ·) ++
        [CacheId.mkProxy n .global, CacheId.mkProxy n .cluster1, CacheId.mkProxy n .cluster2]
        )
    case nodup =>
      simp[List.nodup_append]
      apply And.intro
      . case left =>
        rw[List.nodup_map_iff]
        simp[List.nodup_finRange]
        simp[mkCacheGlobalP_inj,]
      . case right =>
        apply And.intro
        . case left =>
          apply And.intro
          . case left =>
            rw[List.nodup_map_iff]
            simp[List.nodup_finRange]
            simp[mkCacheCluster1_inj,]
          . case right =>
            apply And.intro
            . case left =>
              apply And.intro
              . case left =>
                rw[List.nodup_map_iff]
                simp[List.nodup_finRange]
                simp[mkCacheCluster2_inj,]
              . case right =>
                apply And.intro
                . case left =>
                  apply And.intro
                  . case left =>
                    apply And.intro
                    . case left => simp[mkProxy]
                    . case right => simp[mkProxy]
                  . case right => simp[mkProxy]
                . case right =>
                  intro fin
                  apply And.intro
                  . case left => simp[mkCacheCluster2, mkProxy]
                  . case right =>
                    apply And.intro
                    all_goals simp[mkProxy,mkCacheCluster1,mkCacheCluster2]
            . case right =>
              intro fin cid exist
              cases exist
              . case inl h =>
                rw[← h.choose_spec]
                simp[mkCacheCluster1, mkCacheCluster2]
              . case inr h =>
                cases h
                . case inl h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                . case inr h =>
                  cases h
                  . case inl h =>
                    rw[h]
                    simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                  . case inr h =>
                    rw[h]
                    simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
        . case right =>
          intro fin2 cid exist
          cases exist
          . case inl h =>
            rw[← h.choose_spec]
            simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
          . case inr h =>
            cases h
            . case inl h =>
              rw[← h.choose_spec]
              simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
            . case inr h =>
              cases h
              . case inl h =>
                rw[h]
                simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
              . case inr h =>
                cases h
                . case inl h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
                . case inr h =>
                  rw[h]
                  simp[mkProxy,mkCacheCluster1,mkCacheCluster2, mkCacheGlobalP]
  complete := by
    intro cid
    induction cid with
    | proxy pi =>
      simp
      match pi with
      | .global =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        rfl
      | .cluster1 =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        rfl
      | .cluster2 =>
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        rfl
    | cache cache_inst =>
      simp
      match cache_inst with
      | .globalP fin2 =>
        apply Or.inl
        apply Exists.intro
        · rfl
      | .cluster1 fin =>
        apply Or.inr
        apply Or.inl
        apply Exists.intro
        · rfl
      | .cluster2 fin =>
        apply Or.inr
        apply Or.inr
        apply Or.inl
        apply Exists.intro
        · rfl

lemma ProtocolInstance.cidSetAtProtocolInstance_is_finite (pi : ProtocolInstance)
  : (pi.cidSetAtProtocolInstance n).Finite := by
  simp[cidSetAtProtocolInstance]
  simp[Set.Finite,]
  simp [Subtype.finite]

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_finset (pi : ProtocolInstance) : Finset (CacheId n) :=
  Set.Finite.toFinset (ProtocolInstance.cidSetAtProtocolInstance_is_finite n pi)

noncomputable def ProtocolInstance.cidSetAtProtocolInstance_to_list (pi : ProtocolInstance) : List (CacheId n) :=
  (pi.cidSetAtProtocolInstance_to_finset n).toList

/-- Assumption: The set of events from projecting the events at `cid` is singleton. -/
noncomputable def Behaviour.stateOfSubsingletonCidSet
  (b : Behaviour n) (init : InitialSystemState n) (cid : CacheId n) (s : Set (Event n)) : State :=
  b.eventToState n init {e ∈ s | e.atCid n cid}.toOption cid

/-- List of Cache States After Events immediately finishing before an Event `e`, including State After `e`. -/
noncomputable def Behaviour.cidSetAtProtocolInstance.cacheStatesFinishBeforeEvent
  (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : List State :=
  let events_ending_immediately_before_event_ends := b.eventsEndingImmediatelyBefore n e
  let cid_list := pi.cidSetAtProtocolInstance_to_list n
  cid_list.map (b.stateOfSubsingletonCidSet n init · events_ending_immediately_before_event_ends)

structure List.swmr (l : List State) : Prop where
  swExclusiveMR : ¬ (SW ∈ l ∧ MR ∈ l) -- Cannot have both SW and MR at the same time
  exclusiveSW : l.count SW ≤ 1 -- Can only have 1 exclusive writer

def SWMR (b : Behaviour n) (init : InitialSystemState n) (pi : ProtocolInstance) (e : Event n) : Prop :=
  (Behaviour.cidSetAtProtocolInstance.cacheStatesFinishBeforeEvent n b init pi e).swmr
