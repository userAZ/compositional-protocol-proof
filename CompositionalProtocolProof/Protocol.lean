import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.Requests
import CompositionalProtocolProof.SWMR

variable (n : Nat)

/-- Axioms 4-14 -/
structure RequestAxioms where
  acqInvals : Behaviour.acqInvalWrapper n
  relWritesBack : Behaviour.ncRelWriteBackWrapper n
  whenReqAccessDir : Behaviour.axRequestAccessesDirectory n
  vdLaterWBOrGetSW : Behaviour.vdCacheEntryWBOrGetSWLaterWrapper n
  dirIdsOrdered : Behaviour.deidOrdered n
  coherentWriteDowngrades : Behaviour.coherentWriteDirDowngradeOthers n
  coherentReadDowngrades : Behaviour.coherentReadDirDowngradeOthers n
  coherentEvictGrant : Behaviour.coherentEvictGetsGrant n
  nonCohReqDowngrades : Behaviour.nonCoherentRequestDowngradeOthers n
  relAcqSelfBroadcast : Behaviour.relAcqBroadcast n
  swmr : SWMR.wrapper n

structure Protocol where
  pi : ProtocolInstance -- Which `cluster` is this protocol associated with
  requests : ProtocolInterface
  reqAxioms : RequestAxioms n
  linearizationOfEvent : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b,
    Behaviour.linearizationEventOfRequest n b init e_req
  eventReqOfProtocol : ∀ b : Behaviour n, ∀ e ∈ b, e.req ∈ requests

/- Want to State if a protocol has some requests. -/
