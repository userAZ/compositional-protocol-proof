import Mathlib
import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.BehaviourRelationDefs

variable (n : Nat)

-- [NOTE] Probably want a lemma about subsingleton input
open scoped Classical in
noncomputable def Set.toOption {α} (s : Set α) : Option (α) :=
  by classical exact
  if h : s = ∅ then
    none
  else
    have nonempty : Nonempty s := by
      simp[← Set.nonempty_iff_ne_empty'] at h
      simp[h]
    Option.some (Classical.choice nonempty).val

noncomputable def Behaviour.eventToState (b : Behaviour n) (init : InitialSystemState n) (e? : Option (Event n)) (cid : CacheId n) : State :=
  match pi, pci with
  | .global, .globalP _
  | .cluster1, .cluster1 _
  | .cluster2, .cluster2 _ => True
  | _, _ => False

def CacheId.sameProtocol (cid₁ cid₂ : CacheId n) : Prop :=
  match cid₁, cid₂ with
  | .proxy pinst₁, .proxy pinst₂ => pinst₁ = pinst₂
  | .cache pcinst₁, .cache pcinst₂ => match pcinst₁, pcinst₂ with
    | .globalP _, .globalP _
    | .cluster1 _, .cluster1 _
    | .cluster2 _, .cluster2 _ => True
    | _, _ => False
  | .cache pcinst, .proxy pinst => MatchingProtocolInstances n pinst pcinst
  | .proxy pinst, .cache pcinst => MatchingProtocolInstances n pinst pcinst

structure CacheId.differentIdSameProtocol (cid cid_other : CacheId n) : Prop where
  ne : cid ≠ cid_other
  sameProtocol : cid.sameProtocol n cid_other

def Event.propOnCid (e : Event n) (p : CacheId n → CacheId n → Prop) : CacheId n → Prop := match e with
  | .cacheEvent ce => p ce.cid
  | .directoryEvent _ => (λ _ => False)

def Event.differentCidInSameProtocol (e : Event n) (cid : CacheId n) : Prop :=
  e.propOnCid n (CacheId.differentIdSameProtocol n) cid

def Behaviour.setOfEventsImmPredEndBefore (b : Behaviour n) (e : Event n) : Set (Option (Event n)) :=
  sorry

def SWMR (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, ∀ cid : CacheId n, e.differentCidInSameProtocol n cid → sorry

/- Want to state: the state of all caches in a protocol is SWMR
(SW ≤ 1, exclusive or, MR ≥ 0, SW = 1 → MR = 0, and MR > 0 → SW = 0) -/

/-
def SWMR (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e

def SWMR' (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ e ∈ b, e.isCacheEvent → b.stateAfter n (init.stateAt n e) e
-/
