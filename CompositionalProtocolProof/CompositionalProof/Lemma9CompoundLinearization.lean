import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol

import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.Lemma8CompoundEnforcesSWMR

/- TODO:
1. define an inductive stating the Compound Linearization event of a Cluster Cache Request Event
  is defined by two cases on what the Request's Linearization event is in the cluster:
  (a) a Cluster Directory Event `e_cdir`:
    Either `e_cdir` has permissions or not.
    If not:
      Then there exists a Global Linearization Event (Cache or Directory),
      stemming from Shim Axiom 15.
    If it does:
      `e_cdir` is the linearization Event.
  (b) a Cluster Cache Event:
    There exists a previous event that obtained permissions, and enforced (did not violate) Compound SWMR
    (True because of Lemma 8 -- all Cluster requests do not violate Compound SWMR).
   -/
