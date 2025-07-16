import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.Requests

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

structure Protocol where
  pi : ProtocolInstance -- Which `cluster` is this protocol associated with
  requests : ProtocolInterface
  reqAxioms : RequestAxioms n

/- Want to State if a protocol has some requests. -/
