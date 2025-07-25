import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.CompositionalProof.ProofBasic

variable (n : Nat)

/-
Assume the Initial State / Current State satisfies Compound SWMR.
  (Must define a version of Compound SWMR for InitialSystemState)
For any global SW downgrade cache event `e_gdown`:
1. the corresponding Cluster Directory state is ≤ the state after `e_gdown`.
2. the corresponding Cluster is in SWMR. (techinically have this by an Axiom)
-/

def CompoundProtocol.globalCidToProtocol (cmp : CompoundProtocol n) (g_cid : Fin 2) : Protocol n := match g_cid with
  | 0 => cmp.cluster1
  | 1 => cmp.cluster2

def ProtocolCacheInstance.globalCacheEventCid (pci : ProtocolCacheInstance n) : Fin 2 := match pci with
  | .globalP fin_2 => fin_2
  | .cluster1 _ => 3 -- Attempt to be smart; Using a value that's not a Fin 2 should produce an error.
  | .cluster2 _ => 3 -- panic! "Error: Expected a Global Cache Event, not a Cluster Cache Event!"

def CacheEvent.globalCacheEventCid (ce_greq : CacheEvent n) : Fin 2 := match ce_greq.cid with
  | .cache p_cache_inst => p_cache_inst.globalCacheEventCid
  | .proxy _ => 3

def Event.globalCacheEventCid (e_greq : Event n) : Fin 2 := match e_greq with
  | .cacheEvent ce => ce.globalCacheEventCid
  | .directoryEvent _ => 3

def CompoundProtocol.clusterProtocolCorrespondingToGlobalProtocol (cmp : CompoundProtocol n) (e_greq : Event n) : Protocol n :=
  cmp.globalCidToProtocol n (e_greq.globalCacheEventCid n)
/-- Lemma 6/7: A global downgrade `e_gdown` leaves it's corresponding cluster directory
in state `s` ≤ `e_gdown.MRS` -/
lemma CompoundProtocol.globalDowngrade.satisfies_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown : Event n) (hgdown_in_b : e_gdown ∈ b)
  (hgdown : e_gdown.isGlobalDowngrade)
  : CompoundSWMR n b init e_gdown := by
  apply CompoundSWMR.gCache
  . case gcache_satisfies_cmp_swmr =>
    simp [Behaviour.globalCacheEvent.satisfiesCompoundSWMR]
    intro haux_is_gcache
    constructor
    exact haux_is_gcache
    . case stateAfterLeGlobalCache =>
      simp[Behaviour.dirEventStateLeGlobalCacheState']
      /- Strategy: Show the latest event is the one corresponding to
      lower state to I (for fwd SW) or going to S (for fwd MR).
      Any further event requires encapsulating another Global Cache Event `e_gcache_aux`,
      and if it encapsulates this event, and since all non-downgrade events at a cache are ordered,
      the last event at the corresponding directory cannot get permissions higher than `e_gdown` -/
      /- NOTE: must know the state before this `e_gdown` satisfies Compound SWMR;
      how should I transfer the def of events before `e_creq` satisfiy Compound SWMR to `e_gdown`.
      Maybe not needed. Let's try the proof first. -/
  sorry
