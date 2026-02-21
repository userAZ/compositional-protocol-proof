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

/-- Additional Axiom : after a weak request, if a Vd WriteBack `e_wb` is ordered after, and we know there's an event `e_succ_wb` that
writesback to the directory for the weak request, then we know `e_succ_wb` is either the  `e_wb` or `e_succ_wb` is ordered before `e_wb` -/
def CompoundProtocol.writeback_successor_eq_vd_writeback_or_OrderedBefore_of_weak_write_OrderedBefore_vd_write_back
  (b : Behaviour n) (init : InitialSystemState n) : Prop
  :=
  {e_ww e_succ_wb e_generated_cdir_ww e_wb : Event n} →
  (hww_stateAfter_Vd : ((b.stateBefore n (init.stateAt n e_ww) e_ww).cache n = Vd) ∨ (Behaviour.stateAfter n b (init.stateAt n e_ww) e_ww).cache = Vd) →
  (hsucc_wb : -- ∃ e_succ ∈ b.es,
  Behaviour.ImmediateBottomSuccSatisfyingProp n b e_ww e_succ_wb fun x =>
    Behaviour.succOnVdWithCorrespondingDir n b init x e_generated_cdir_ww) →
  (hww_ob_wb : e_ww.OrderedBefore n e_wb) →
  (hww_is_weak_write_or_read : e_ww.isNcWeakWrite ∨ e_ww.isNcWeakRead) →
  (hwb_is_vdwb : e_wb.isVdWriteBack) →
  (hww_same_entry_wb : e_ww.sameEntry n e_wb) →
  e_succ_wb = e_wb ∨ e_succ_wb.OrderedBefore n e_wb

def AcquireInvalOrderedBeforeReadPred.wrapper : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  ∀ e_inval ∈ b, ∀ e_pred ∈ b, ∀ e_ww ∈ b,
  CompoundProtocol.acquire_invalidation_OrderedBefore_weak_read_predecessor_that_gets_perms n b init e_inval e_pred e_ww

def weakRequestOrderedBeforeVdWriteBackIsWriteBackOrOrderedBefore.wrapper : Prop := ∀ b : Behaviour n, ∀ init : InitialSystemState n,
  CompoundProtocol.writeback_successor_eq_vd_writeback_or_OrderedBefore_of_weak_write_OrderedBefore_vd_write_back n b init

/-- Axioms 4-14 -/
structure RequestAxioms where
  acqInvals : Behaviour.acqInvalWrapper n
  relWritesBack : Behaviour.ncRelWriteBackWrapper n
  whenReqAccessDir : Behaviour.axRequestAccessesDirectory n
  hasPermsOrVdDirBeforeAfter : Behaviour.has_perms_or_vd_exists_e_dir_before_or_after n
  vdLaterWBOrGetSW : Behaviour.vdCacheEntryWBOrGetSWLaterWrapper n
  dirIdsOrdered : Behaviour.deidOrdered n
  coherentWriteDowngrades : Behaviour.coherentWriteDirDowngradeOthers n
  coherentReadDowngrades : Behaviour.coherentReadDirDowngradeOthers n
  coherentEvictGrant : Behaviour.coherentEvictGetsGrant n
  nonCohReqDowngrades : Behaviour.nonCoherentRequestDowngradeOthers n
  relAcqSelfBroadcast : Behaviour.relAcqBroadcast n
  swmr : SWMR.wrapper n
  acquireInvalBeforeReadPredecessor : AcquireInvalOrderedBeforeReadPred.wrapper n
  vdWriteBackAfterWeakRequestLinearizationEventEqOrOrderedBefore : weakRequestOrderedBeforeVdWriteBackIsWriteBackOrOrderedBefore.wrapper n

structure Protocol where
  pi : ProtocolInstance -- Which `cluster` is this protocol associated with
  requests : ProtocolInterface
  reqAxioms : RequestAxioms n
  linearizationOfEvent : ∀ b : Behaviour n, ∀ init : InitialSystemState n, ∀ e_req ∈ b,
    Behaviour.linearizationEventOfRequest n b init e_req
  eventReqOfProtocol : ∀ b : Behaviour n, ∀ e ∈ b, e.req ∈ requests

def Protocol.dirAccessOfRequest (p : Protocol n) (b : Behaviour n) (init : InitialSystemState n)
  (e_req : Event n) (he_req_in_b : e_req ∈ b)
  : ∃ e_dir ∈ b, b.dirAccessOfRequest n init e_req e_dir :=
  Behaviour.exists_e_dir_access_of_e_req n b init e_req he_req_in_b p.reqAxioms.whenReqAccessDir p.reqAxioms.hasPermsOrVdDirBeforeAfter

/- Want to State if a protocol has some requests. -/
