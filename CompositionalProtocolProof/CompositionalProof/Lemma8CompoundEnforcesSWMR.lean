import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol

import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.Lemma4ClusterRequest

variable (n : Nat)

-- ∀ Cluster Dir & Global Cache Events, CompoundSWMR holds iff ∀ Cluster Cache Event, Compound SWMR holds
/- TODO: Show that the Prop `CompoundSWMR` holds iff for all cluster cache events, `CompoundSWMR` holds
  1. Fwd (MP) case: Use Request and Shim Axioms to show we can go from Cluster Cache Events to `CompoundSWMR`
  2. Reverse (MPR) case: Let there be an arbitrary ClusterCacheEvent event `e` in Behaviour `b`.
    a. By Request and Shim axioms, `e` may:
      i. produce additional Cluster Directory Events and Global Cache Events,
        that by `CompoundSWMR` still enforce `CompoundSWMR`.
      ii. If they produce none, then the system is still in Compound SWMR.
-/

lemma CompoundProtocol.compound_swmr_iff_cluster_requests_satsify_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n) (cmp_protocol : CompoundProtocol n)
  : CompoundSWMR.wrapper n := by
  sorry

-- ∀ cmpProtocol, CompoundSWMR holds
/- TODO: State that Cluster-Cache-Events enforce Compound SWMR
1. consider set of events at a cluster cache entry
  a. In the empty case, Compound SWMR is maintained (assuming initial state is Compound SWMR)
  b. In the multiple case, map the set to the equivalent list of events at the cache entry.
2. Multiple case:
  a. induct on the list; by Lemma 4, we know all Cache Request Events leave the protocol in Compound SWMR;
  b. in the inductive step case `cons`, apply the induction hypothesis.
-/

lemma CompoundProtocol.compound_swmr_holds
  (b : Behaviour n) (init : InitialSystemState n) (cmp_protocol : CompoundProtocol n)
  : CompoundSWMR.wrapper n := by
  sorry
