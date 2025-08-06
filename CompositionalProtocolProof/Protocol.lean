import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.Requests
import CompositionalProtocolProof.SWMR

variable (n : Nat)

/-- Additional Axiom -/
def CompoundProtocol.acquire_invalidation_OrderedBefore_weak_read_predecessor_that_gets_perms
  (b : Behaviour n) (init : InitialSystemState n) (e_inval : Event n) (e_pred e_ww : Event n) : Prop
  :=
  (hpred_get_perms :
    Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast n b init e_pred e_ww) →
  (hinval_ob_ww : e_inval.OrderedBefore n e_ww) →
  (hww_is_weak_read : e_ww.isNcWeakRead') →
  (hinval_is_vcinval : e_inval.isVcInval) →
  (hww_same_entry_wb : e_ww.sameEntry n e_inval) →
  e_inval.OrderedBefore n e_pred

def AcquireInvalOrderedBeforeReadPred.wrapper : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_inval ∈ b, ∀ e_pred ∈ b, ∀ e_ww ∈ b,
  CompoundProtocol.acquire_invalidation_OrderedBefore_weak_read_predecessor_that_gets_perms n b init e_inval e_pred e_ww

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
  acquireInvalBeforeReadPredecessor : AcquireInvalOrderedBeforeReadPred.wrapper n

structure Protocol where
  pi : ProtocolInstance -- Which `cluster` is this protocol associated with
  requests : ProtocolInterface
  reqAxioms : RequestAxioms n
  linearizationOfEvent : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b,
    Behaviour.linearizationEventOfRequest n b init e_req
  eventReqOfProtocol : ∀ b : Behaviour n, ∀ e ∈ b, e.req ∈ requests

/- Want to State if a protocol has some requests. -/
