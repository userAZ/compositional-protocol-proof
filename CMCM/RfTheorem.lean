import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers

import CMCM.RfCases.RfSameGleWImmPredRCle
import CMCM.RfCases.RfSameGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWImmPredRGleSameClusterWImmPredRCle
import CMCM.RfCases.RfWImmPredRGleSameClusterEvictOrReadBetween
import CMCM.RfCases.RfWImmPredRGleDiffClusterWCleImmPredDown
import CMCM.RfCases.RfWImmPredRGleDiffClusterEvictOrReadBetween

variable {n : ℕ}

/- ========== START CMCM.RF case lemmas ========== -/

lemma CMCM.rf.sameGle.sameCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hsame_cle : hw_c_and_g_lin.hreq's_dir_access.choose = hr_c_and_g_lin.hreq's_dir_access.choose)
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  {hr_not_ob_w : ¬ e_r.OrderedBefore n e_w}
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- Prove RF case for same GLE and same CLE
  apply Behaviour.readsFrom.cases.wEqRGle hsame_gle (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) (hw_not_down := hw_not_down) (r_not_down := hr_not_down)

  apply Behaviour.readsFrom.wEqRGle.cases.wEqRCle hsame_cle

  -- Show `e_w` and `e_r` must be in the same protocol/cluster
  -- because they have the same GLE and CLE.
  . case hwr_same_cluster =>
    apply same_cle_implies_same_protocol hw_c_and_g_lin hr_c_and_g_lin hsame_cle
  . case hwr_com =>
    constructor
    . case sameCache =>
      exact same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle
    . case wObR =>
      exact eq_gle_cle_implies_write_before_read (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle hr_not_ob_w
    . case writeRead =>
      apply Event.writeReadPair.mk hw_is_write hw_not_down hr_is_read hr_not_down
    . case noBetween =>
      constructor
      . case noWrite =>
        -- The following cases are considered in `noInterveningWrites_implies_no_writes_between`:
        -- (1) Case analysis on the dirAccessOfRequest of `e_w` and `e_r`
        -- (2) The fact that `hsame_cle` holds rules out many cases of dirAccessOfRequest
        -- (3) `NoInterveningWrites` from the main theorem rules out intervening writes
        -- (4) `hsame_cle` also rules out intervening writes at the CLE level
        have hsame_struct : e_w.struct = e_r.struct := same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle
        exact noInterveningWrites_implies_no_writes_between hw_is_write hr_is_read hsame_struct hw_not_down hr_not_down
          hw_c_and_g_lin hr_c_and_g_lin hsame_cle hknow_dir_access hno_intervening_writes hr_not_ob_w hsucc_w_of_w_after_r
      . case noEvict =>
        -- No coherent evicts can occur between e_w and e_r when they have the same CLE.
        intro e_evict hevict_in_b hbetween_w_r hevict_sw

        -- Case analysis on dirAccessOfRequest of e_w and e_r (3x3 = 9 cases)
        have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
        have hr_dir_access := hr_c_and_g_lin.hreq's_dir_access.choose_spec.right

        -- We already proved e_w.OrderedBefore n e_r in the wObR case
        have hw_ob_r : e_w.OrderedBefore n e_r :=
          eq_gle_cle_implies_write_before_read (hw_cluster := hw_cluster) (hr_cluster := hr_cluster)
            hw_is_write hr_is_read hw_not_down hr_not_down hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle hr_not_ob_w

        -- Since hsame_cle, the directory events are the same
        cases hw_dir_access with
        -- Case 1: e_w encapDir
        | encapDir _ hw_encap =>
          cases hr_dir_access with
          -- Case 1.1: e_w encapDir, e_r encapDir
          | encapDir _ hr_encap =>
            -- Contradiction: if both encapsulate their directory events, then the directory events
            -- must be ordered with respect to e_w and e_r (since e_w OB e_r).
            -- But hsame_cle says they're the same event!
            exfalso
            -- e_w encapsulates e_w_cle and e_r encapsulates e_r_cle
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir
            have hr_encap_cle : e_r.Encapsulates n (hr_c_and_g_lin.hreq's_dir_access.choose) := hr_encap.reqEncapDir

            -- Unfold Encapsulates to get the two inequalities
            simp only [Event.Encapsulates] at hw_encap_cle hr_encap_cle

            -- From hw_encap_cle: e_w.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart and
            --                    (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_w.oEnd
            have hw_encap_1 := hw_encap_cle.1
            have hw_encap_2 := hw_encap_cle.2

            -- From hr_encap_cle: e_r.oStart < (hr_c_and_g_lin.hreq's_dir_access.choose).oStart and
            --                    (hr_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_r.oEnd
            have hr_encap_1 := hr_encap_cle.1
            have hr_encap_2 := hr_encap_cle.2

            -- From hsame_cle, substitute to replace hr_cle with hw_cle where it appears
            rw [← hsame_cle] at hr_encap_1 hr_encap_2

            -- From hw_ob_r (e_w OB e_r): e_w.oEnd < e_r.oStart
            simp only [Event.OrderedBefore] at hw_ob_r

            -- Extract well-formedness constraints
            have hw_cle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed

            -- Now we have all the linear constraints:
            -- hw_encap_1: e_w.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart
            -- hw_encap_2: (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_w.oEnd
            -- hr_encap_1: e_r.oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart
            -- hr_encap_2: (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < e_r.oEnd
            -- hw_ob_r: e_w.oEnd < e_r.oStart
            -- hw_cle_wf: (hw_c_and_g_lin.hreq's_dir_access.choose).oStart < (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd

            -- Since omega doesn't see these, let me state the contradiction more explicitly
            -- From hr_encap_1 and hr_encap_2, combined with substitution:
            -- The CLE event (which is the same for both) must satisfy:
            --   e_w.oStart < cle.oStart  [from hw_encap_1]
            --   cle.oEnd < e_w.oEnd      [from hw_encap_2]
            --   e_r.oStart < cle.oStart  [from hr_encap_1]
            --   cle.oEnd < e_r.oEnd      [from hr_encap_2]
            -- And: e_w.oEnd < e_r.oStart [from hw_ob_r]

            -- From hw_ob_r and hr_encap_1: e_w.oEnd < e_r.oStart < cle.oStart
            have step1 : e_w.oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_ob_r hr_encap_1

            -- From step1 and hw_encap_2: e_w.oEnd < cle.oStart and cle.oEnd < e_w.oEnd
            -- So: cle.oEnd < e_w.oEnd < cle.oStart
            have step2 : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_encap_2 step1

            -- But this contradicts hw_cle_wf: cle.oStart < cle.oEnd
            exact Nat.lt_asymm step2 hw_cle_wf
          -- Case 1.2: e_w encapDir, e_r orderBeforeDir
          | orderBeforeDir hreq_r_has_perms hexists_pred_r hpred_r_accesses_dir hinter_leaves_r hpred_r_same_protocol =>
            exfalso
            -- Both e_w and e_r's predecessor encapsulate the same CLE
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir
            have hpred_encap_cle : hexists_pred_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hpred_encap_cle' := hpred_r_accesses_dir.reqEncapDir
              simpa [hsame_cle] using hpred_encap_cle'

            -- Since both events are at the same cache entry and both encapsulate the same CLE,
            -- they must correspond to the same request event (by the uniqueness of dirEventOfReqEvent).
            -- Therefore: hexists_pred_r.choose = e_w
            have hpred_eq_ew : hexists_pred_r.choose = e_w := by
              have hw_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n e_w :=
                hw_encap.dirOfReq
              have hpred_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hexists_pred_r.choose := by
                convert hpred_r_accesses_dir.dirOfReq using 2
              exact (dir_event_of_req_event_unique hw_dir_of_req hpred_dir_of_req).symm

            -- Now substitute: hexists_pred_r.choose := e_w
            rw [hpred_eq_ew] at hinter_leaves_r

            -- After the fix, we have a direct contradiction:
            -- hreq_r_has_perms says: e_r was made on a state with coherent required permissions
            -- hinter_leaves_r says: all events between e_w (pred) and e_r leave state >= e_r.req.MRS
            --
            -- The contradiction: if all intermediates maintain the required permissions,
            -- and the state at e_r already has those permissions (from hreq_r_has_perms),
            -- then e_r doesn't need orderBeforeDir (its predecessor) to get permissions.
            -- But we're in the orderBeforeDir case, which contradicts this.
            --
            -- More formally:
            -- - hreq_r_has_perms encodes: state_before_e_r >= e_r.req.MRS (and coherent)
            -- - hinter_leaves_r on all intermediate events: state preserved as >= e_r.req.MRS
            -- - Therefore: e_r has no need for a predecessor to grant permissions
            -- - But orderBeforeDir requires such a predecessor
            -- - Contradiction!
            have hevict_perms := hinter_leaves_r e_evict hevict_in_b hbetween_w_r.interBetween
            have hevict_perms_after := hevict_perms.hinter_leaves_state_at_least

            -- The contradiction:
            -- hevict_perms_after says: state after evict >= e_r.req.MRS
            -- hreq_r_has_perms says: state before e_r is coherent with required perms
            --
            -- But a coherent downgrade (evict) MUST drop permissions.
            -- So we cannot have both:
            --   (1) state after evict >= required
            --   (2) state before e_r with required
            -- if an evict in between reduces permissions
            --
            -- This contradicts the orderBeforeDir assumption that e_r gets perms from predecessor
            -- (which we proved is e_w), because e_w already had them (via encapsulation).

            -- From hreq_r_has_perms (after unfolding), state before e_r has the perms
            -- From hevict_perms_after, state after evict maintains perms >= required
            -- But a coherent downgrade (evict) MUST drop permissions.
            -- This creates a contradiction.

            -- Extract what we need: e_evict must be a cache event from hbetween_w_r
            have hevict_is_cache : e_evict.isCacheEvent := hbetween_w_r.isCache
            have hevict_is_coherent : e_evict.isCoherent := by
              simp [Event.isEvictSW, Event.isCacheEvent] at hevict_sw hevict_is_cache
              cases hevict_is_cache_case : e_evict with
              | cacheEvent ce =>
                simp [hevict_is_cache_case] at hevict_sw
                simp [Event.isCoherent]
                exact hevict_sw.coherentWrite.left
              | directoryEvent de =>
                simp [hevict_is_cache_case] at hevict_is_cache

            -- Apply the helper lemma to derive False
            exact coherent_evict_downgrade_contradiction
              (cmp := cmp)
              hr_cluster
              hr_is_read
              hreq_r_has_perms
              hbetween_w_r.coherentRead
              hevict_sw
              hevict_in_b
              hevict_is_coherent
              hevict_is_cache
              hevict_perms_after
          -- Case 1.3: e_w encapDir, e_r orderAfterDir
          | orderAfterDir hreq_r_on_vd hsucc_encap_dir_r hsucc_same_protocol_r =>
            exfalso
            -- e_w encapsulates the CLE
            have hw_encap_cle : e_w.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := hw_encap.reqEncapDir

            -- e_r's successor encapsulates the same CLE (after substitution with hsame_cle)
            have hsucc_encap_cle : hsucc_encap_dir_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap_cle' := hsucc_encap_dir_r.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap_cle'

            -- e_r is ordered before its successor
            have hsucc_spec := hsucc_encap_dir_r.choose_spec.right
            simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
            have hr_ob_succ : e_r.OrderedBefore n hsucc_encap_dir_r.choose := by
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ

            -- From e_w < e_r and e_r < e_succ, we have e_w < e_succ
            have hw_ob_succ : e_w.OrderedBefore n hsucc_encap_dir_r.choose :=
              Event.ordered_trans (n := n) hw_ob_r hr_ob_succ

            -- Unfold encapsulation constraints
            simp only [Event.Encapsulates] at hw_encap_cle hsucc_encap_cle
            have hw_encap_2 := hw_encap_cle.2
            have hsucc_encap_1 := hsucc_encap_cle.1

            -- e_w.oEnd < e_succ.oStart < cle.oStart
            have h1 : e_w.oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_ob_succ hsucc_encap_1

            -- cle.oEnd < e_w.oEnd < cle.oStart
            have h2 : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hw_encap_2 h1

            -- But cle is well-formed: oStart < oEnd
            have hw_cle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
            exact Nat.lt_asymm h2 hw_cle_wf
        -- Case 2: e_w orderBeforeDir
        | orderBeforeDir hreq_w_has_perms hexists_pred_w hpred_w_accesses_dir hinter_leaves_w hpred_w_same_protocol =>
          -- e_w.OrderedBefore n e_r and hexists_pred_w is a predecessor of e_w
          have hpred_before_ew : hexists_pred_w.choose.OrderedBefore n e_w := by
            have := hexists_pred_w.choose_spec.right
            simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at this
            simp[Behaviour.ImmediateBottomPredSatisfyingProp] at this
            have hpred_is_imm_pred := this.isImmPred
            have hpred_is_pred := hpred_is_imm_pred.bPred.isPred
            simp[Event.Predecessor] at hpred_is_pred
            simp[hpred_is_pred]
          have hpred_before_er : hexists_pred_w.choose.OrderedBefore n e_r := by
            calc hexists_pred_w.choose.OrderedBefore n e_w := hpred_before_ew
              e_w.OrderedBefore n e_r := hw_ob_r

          cases hr_dir_access with
          -- Case 2.1: e_w orderBeforeDir, e_r encapDir
          | encapDir _ hr_encap =>
            exfalso
            -- e_w's predecessor encapsulates CLE, and e_r also encapsulates CLE
            have hpred_encap_cle : hexists_pred_w.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hpred_encap_cle' := hpred_w_accesses_dir.reqEncapDir
              simpa [hsame_cle] using hpred_encap_cle'
            have hr_encap_cle : e_r.Encapsulates n (hr_c_and_g_lin.hreq's_dir_access.choose) := hr_encap.reqEncapDir

            simp only [Event.Encapsulates] at hpred_encap_cle hr_encap_cle
            have hpred_encap_1 := hpred_encap_cle.1
            have hpred_encap_2 := hpred_encap_cle.2
            have hr_encap_1 := hr_encap_cle.1
            have hr_encap_2 := hr_encap_cle.2

            rw [← hsame_cle] at hr_encap_1 hr_encap_2

            simp only [Event.OrderedBefore] at hpred_before_ew hpred_before_er

            -- Setup the ordering contradiction:
            -- From hpred_encap: hpred_w.oStart < cle.oStart < hpred_w.oEnd
            -- From hr_encap: e_r.oStart < cle.oStart < e_r.oEnd
            -- From hpred_before_er: hpred_w.oEnd < e_r.oStart
            have h1 : hexists_pred_w.choose.oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hpred_before_er hr_encap_1

            have h2 : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart :=
              Nat.lt_trans hpred_encap_2 h1

            have hw_cle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
            exact Nat.lt_asymm h2 hw_cle_wf
          -- Case 2.2: e_w orderBeforeDir, e_r orderBeforeDir
          | orderBeforeDir hreq_r_has_perms hexists_pred_r hpred_r_accesses_dir hinter_leaves_r hpred_r_same_protocol =>
            exfalso
            -- Both have predecessors that must be the same (by dir_event_of_req_event_unique)
            have hw_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hexists_pred_w.choose :=
              hpred_w_accesses_dir.dirOfReq
            have hr_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hexists_pred_r.choose := by
              convert hpred_r_accesses_dir.dirOfReq using 2
            have hpreds_eq : hexists_pred_w.choose = hexists_pred_r.choose :=
              dir_event_of_req_event_unique hw_dir_of_req hr_dir_of_req

            -- Rewrite hinter_leaves_r to use the same predecessor as hinter_leaves_w
            rw [hpreds_eq.symm] at hinter_leaves_r

            have hevict_btn_wpred_r :  e_evict.OrderedBetween n hexists_pred_w.choose e_r := by
              constructor
              simp[autoParam]
              . case pred =>
                calc hexists_pred_w.choose.OrderedBefore n e_w := hpred_before_ew
                  e_w.OrderedBefore n e_evict := hbetween_w_r.interBetween.pred
              . case succ =>
                simp[autoParam]
                simp[hbetween_w_r.interBetween.succ]

            -- Now use hinter_leaves_r to get evict permissions relative to e_r
            have hevict_perms := hinter_leaves_r e_evict hevict_in_b hevict_btn_wpred_r
            have hevict_perms_after := hevict_perms.hinter_leaves_state_at_least

            have hevict_is_cache : e_evict.isCacheEvent := hbetween_w_r.isCache
            have hevict_is_coherent : e_evict.isCoherent := by
              simp [Event.isEvictSW, Event.isCacheEvent] at hevict_sw hevict_is_cache
              cases hevict_is_cache_case : e_evict with
              | cacheEvent ce =>
                simp [hevict_is_cache_case] at hevict_sw
                simp [Event.isCoherent]
                exact hevict_sw.coherentWrite.left
              | directoryEvent de =>
                simp [hevict_is_cache_case] at hevict_is_cache

            exact coherent_evict_downgrade_contradiction
              (cmp := cmp)
              hr_cluster
              hr_is_read
              hreq_r_has_perms
              hbetween_w_r.coherentRead
              hevict_sw
              hevict_in_b
              hevict_is_coherent
              hevict_is_cache
              hevict_perms_after
          -- Case 2.3: e_w orderBeforeDir, e_r orderAfterDir
          | orderAfterDir hreq_r_on_vd hsucc_encap_dir_r hsucc_same_protocol_r =>
            exfalso
            -- e_w's predecessor encapsulates CLE, e_r's successor encapsulates CLE
            have hpred_w_encap_cle : hexists_pred_w.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hpred_encap := hpred_w_accesses_dir.reqEncapDir
              simpa [hsame_cle] using hpred_encap
            have hsucc_r_encap_cle : hsucc_encap_dir_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap := hsucc_encap_dir_r.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap

            -- Ordering: pred_w < e_w < e_r < succ_r
            have hpred_w_before_ew : hexists_pred_w.choose.OrderedBefore n e_w := by
              have := hexists_pred_w.choose_spec.right
              simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at this
              simp[Behaviour.ImmediateBottomPredSatisfyingProp] at this
              have hpred_is_imm_pred := this.isImmPred
              have hpred_is_pred := hpred_is_imm_pred.bPred.isPred
              simp[Event.Predecessor] at hpred_is_pred
              simp[hpred_is_pred]
            have hsucc_r_after_er : e_r.OrderedBefore n hsucc_encap_dir_r.choose := by
              have hsucc_spec := hsucc_encap_dir_r.choose_spec.right
              simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ

            simp only [Event.OrderedBefore] at hpred_w_before_ew hsucc_r_after_er

            -- Transitivity: pred_w < e_r < succ_r
            have hpred_w_before_succ_r : hexists_pred_w.choose.OrderedBefore n hsucc_encap_dir_r.choose := by
              calc hexists_pred_w.choose.OrderedBefore n e_w := hpred_w_before_ew
                e_w.OrderedBefore n e_r := hw_ob_r
                e_r.OrderedBefore n hsucc_encap_dir_r.choose := hsucc_r_after_er
            simp only [Event.OrderedBefore] at hpred_w_before_succ_r

            -- Contradiction: cle.oEnd < pred_w.oEnd < succ_r.oStart < cle.oStart
            have h_contradiction : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := by
              calc (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < hexists_pred_w.choose.oEnd := hpred_w_encap_cle.2
                _ < hsucc_encap_dir_r.choose.oStart := hpred_w_before_succ_r
                _ < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := hsucc_r_encap_cle.1

            have hcle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
            exact Nat.lt_asymm h_contradiction hcle_wf
        -- Case 3: e_w orderAfterDir
        | orderAfterDir hreq_w_on_vd hsucc_encap_dir_w hsucc_same_protocol_w =>
          cases hr_dir_access with
          -- Case 3.1: e_w orderAfterDir, e_r encapDir
          | encapDir _ hr_encap =>
            exfalso
            -- e_w's successor encapsulates CLE, e_r also encapsulates CLE
            have hsucc_w_encap_cle : hsucc_encap_dir_w.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap := hsucc_encap_dir_w.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap
            have hr_encap_cle : e_r.Encapsulates n (hr_c_and_g_lin.hreq's_dir_access.choose) := hr_encap.reqEncapDir

            simp only [Event.Encapsulates] at hsucc_w_encap_cle hr_encap_cle

            have hsucc_spec := hsucc_encap_dir_w.choose_spec.right

            -- Ordering: e_w < succ_w and e_w < e_r
            have hw_before_succ_w : e_w.OrderedBefore n hsucc_encap_dir_w.choose := by
              simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ

            simp only [Event.OrderedBefore] at hw_before_succ_w hw_ob_r

            -- Both e_r and succ_w are at same structure
            have hsame_struct_w_r : e_w.struct = e_r.struct := same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle

            -- Both must be cache events (only cache events can encapsulate directories at cluster level)
            have hr_is_cache : e_r.isCacheEvent := hr_cluster.eAtCache

            have hsucc_w_is_cache : hsucc_encap_dir_w.choose.isCacheEvent := by
              have hsucc_req_event := hsucc_spec.satisfyP.encapCorresponding.dirCorresponds.reqEvent
              cases hsucc_ev : hsucc_encap_dir_w.choose with
              | cacheEvent _ =>
                simp [Event.isCacheEvent]
              | directoryEvent _ =>
                exfalso
                have hw_cache : e_w.isCacheEvent := hw_cluster.eAtCache
                cases hw_ev : e_w with
                | cacheEvent ce_w =>
                  have hsame_struct : e_w.struct = hsucc_encap_dir_w.choose.struct :=
                    hsucc_spec.isImmBottomSucc.sameEntry.sameStruct
                  rw [hsucc_ev, hw_ev] at hsame_struct
                  have hsame_struct_false : False := by
                    simp [Event.struct] at hsame_struct
                  exact hsame_struct_false
                | directoryEvent _ =>
                  simp [Event.isCacheEvent, hw_ev] at hw_cache

            -- Get cache event witnesses
            cases hr_ce : e_r with
            | cacheEvent ce_r =>
              cases hsucc_ce : hsucc_encap_dir_w.choose with
              | cacheEvent ce_succ_w =>
                -- Both are cache events at the same entry, ordered by cache_ordered axiom
                have hce_ordered := b.orderedAtEntry.cache_ordered ce_r ce_succ_w
                have hce_encap_or_ordered := hce_ordered.ordered
                simp [CacheEvent.encapsulatedOrOrdered, CacheEvent.encapsulatedOrBefore] at hce_encap_or_ordered

                cases hce_encap_or_ordered with
                | inl hr_before_or_in_succ_w =>
                  cases hr_before_or_in_succ_w with
                  | inl hr_encap_by_succ_w =>
                    -- e_r encapsulated by succ_w -> e_r is a downgrade (contradicts hr_not_down)
                    have hencap_ce : ce_succ_w.Encapsulates n ce_r := by
                      simpa [CacheEvent.EncapsulatedBy] using hr_encap_by_succ_w
                    have hdown_ce_r : ce_r.down :=
                      (b.orderedAtEntry.cache_encap_rule ce_succ_w ce_r) hencap_ce
                    have hdown_er : e_r.down := by
                      simpa [Event.down, hr_ce] using hdown_ce_r
                    exact hr_not_down hdown_er
                  | inr hr_ob_succ_w =>
                    -- e_r ordered before succ_w: ce_r.oEnd < ce_succ_w.oStart
                    -- Contradiction: cle.oEnd < e_r.oEnd < succ_w.oStart < cle.oStart
                    have h_contradiction : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := by
                      rw [← hsame_cle] at hr_encap_cle
                      simp [hr_ce, Event.oEnd, Event.oStart] at hr_encap_cle
                      simp [hsucc_ce, Event.oStart, Event.oEnd] at hsucc_w_encap_cle
                      simp [CacheEvent.OrderedBefore] at hr_ob_succ_w
                      calc (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < ce_r.oEnd := hr_encap_cle.2
                        _ < ce_succ_w.oStart := hr_ob_succ_w
                        _ < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := hsucc_w_encap_cle.1
                    have hcle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
                    exact Nat.lt_asymm h_contradiction hcle_wf
                | inr hsucc_w_before_or_in_r =>
                  cases hsucc_w_before_or_in_r with
                  | inl hsucc_w_encap_by_r =>
                    -- succ_w encapsulated by e_r -> contradicts succ_w being bottom at same entry
                    have hencap_ce : ce_r.Encapsulates n ce_succ_w := by
                      simpa [CacheEvent.EncapsulatedBy] using hsucc_w_encap_by_r
                    have hencap_event : e_r.Encapsulates n hsucc_encap_dir_w.choose := by
                      simpa [hr_ce, hsucc_ce] using
                        (CacheEvent.encap_then_event_encap n ce_r ce_succ_w hencap_ce)

                    have hsucc_addr_cle : hsucc_encap_dir_w.choose.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := by
                      have hsucc_same_addr := hsucc_spec.satisfyP.encapCorresponding.dirCorresponds.sameAddr
                      simpa [hsame_cle] using hsucc_same_addr
                    have hr_addr_cle : e_r.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := by
                      have hr_same_addr := hr_encap.dirCorresponds.sameAddr
                      simpa [hsame_cle] using hr_same_addr
                    have hsame_addr_r_succ : e_r.addr = hsucc_encap_dir_w.choose.addr := by
                      calc e_r.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := hr_addr_cle
                        _ = hsucc_encap_dir_w.choose.addr := by
                          symm
                          exact hsucc_addr_cle
                    have hsucc_same_struct_w : hsucc_encap_dir_w.choose.struct = e_w.struct := by
                      have hsame_struct : Event.sameStructure n e_w hsucc_encap_dir_w.choose :=
                        hsucc_spec.isImmBottomSucc.sameEntry.sameStruct
                      simpa [Event.sameStructure] using hsame_struct.symm
                    have hsame_struct_r_succ : e_r.struct = hsucc_encap_dir_w.choose.struct := by
                      calc e_r.struct = e_w.struct := hsame_struct_w_r.symm
                        _ = hsucc_encap_dir_w.choose.struct := by
                          symm
                          exact hsucc_same_struct_w
                    have hsame_entry_r_succ : e_r.sameEntry n hsucc_encap_dir_w.choose := by
                      constructor
                      . case sameStruct => exact hsame_struct_r_succ
                      . case sameAddr => exact hsame_addr_r_succ

                    have hr_in_b : e_r ∈ b := hr_encap.reqInB
                    have hencap_same : Event.EncapAtSameStructure n e_r hsucc_encap_dir_w.choose :=
                      { encap := hencap_event, sameEntry := hsame_entry_r_succ }
                    exact (hsucc_spec.isBottom e_r hr_in_b) hencap_same
                  | inr hsucc_w_ob_r =>
                    -- succ_w ordered before e_r: ce_succ_w.oEnd < ce_r.oStart
                    -- Contradiction: cle.oEnd < succ_w.oEnd < e_r.oStart < cle.oStart
                    have h_contradiction : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := by
                      rw [← hsame_cle] at hr_encap_cle
                      simp [hr_ce, Event.oEnd, Event.oStart] at hr_encap_cle
                      simp [hsucc_ce, Event.oStart, Event.oEnd] at hsucc_w_encap_cle
                      simp [CacheEvent.OrderedBefore] at hsucc_w_ob_r
                      calc (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < ce_succ_w.oEnd := hsucc_w_encap_cle.2
                        _ < ce_r.oStart := hsucc_w_ob_r
                        _ < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := hr_encap_cle.1
                    have hcle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
                    exact Nat.lt_asymm h_contradiction hcle_wf
              | directoryEvent de_succ_w =>
                -- Contradiction: succ_w is a directory event but must be cache to encapsulate cluster directory
                exfalso
                rw [hsucc_ce] at hsucc_w_is_cache
                simp [Event.isCacheEvent] at hsucc_w_is_cache
            | directoryEvent de_r =>
              -- Contradiction: e_r is a directory event but must be cache to encapsulate cluster directory
              exfalso
              rw [hr_ce] at hr_is_cache
              simp [Event.isCacheEvent] at hr_is_cache
          -- Case 3.2: e_w orderAfterDir, e_r orderBeforeDir
          | orderBeforeDir hreq_r_has_perms hexists_pred_r hpred_r_accesses_dir hinter_leaves_r hpred_r_same_protocol =>
            exfalso
            -- e_w's successor encapsulates CLE, e_r's predecessor encapsulates CLE
            have hsucc_spec := hsucc_encap_dir_w.choose_spec.right
            have hsame_struct_w_r : e_w.struct = e_r.struct :=
              same_cle_implies_same_struct hw_c_and_g_lin hr_c_and_g_lin hsame_cle

            have hsucc_w_encap_cle : hsucc_encap_dir_w.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap := hsucc_encap_dir_w.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap
            have hpred_r_encap_cle : hexists_pred_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hpred_encap := hpred_r_accesses_dir.reqEncapDir
              simpa [hsame_cle] using hpred_encap

            simp only [Event.Encapsulates] at hsucc_w_encap_cle hpred_r_encap_cle

            -- Ordering relationships
            have hw_before_succ_w : e_w.OrderedBefore n hsucc_encap_dir_w.choose := by
              simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ
            have hpred_r_before_er : hexists_pred_r.choose.OrderedBefore n e_r := by
              have := hexists_pred_r.choose_spec.right
              simp[Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at this
              simp[Behaviour.ImmediateBottomPredSatisfyingProp] at this
              have hpred_is_imm_pred := this.isImmPred
              have hpred_is_pred := hpred_is_imm_pred.bPred.isPred
              simp[Event.Predecessor] at hpred_is_pred
              simp[hpred_is_pred]

            simp only [Event.OrderedBefore] at hw_before_succ_w hpred_r_before_er hw_ob_r

            -- Contradiction: both pred_r and succ_w are bottom cache events at the same entry
            -- that encapsulate the same CLE, so they must be ordered or encapsulate each other;
            -- either case contradicts bottomness or CLE well-formedness.

            -- Unpack predecessor proof to access bottomness + sameEntry
            have hpred_spec := hexists_pred_r.choose_spec.right
            simp [Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast] at hpred_spec

            have hpred_same_entry_er : hexists_pred_r.choose.sameEntry n e_r :=
              hpred_spec.isImmPred.bPred.sameEntry

            have hsucc_same_entry_w : e_w.sameEntry n hsucc_encap_dir_w.choose :=
              hsucc_encap_dir_w.choose_spec.right.isImmBottomSucc.sameEntry

            -- Show pred_r and succ_w are at the same entry
            have hpred_addr_cle : hexists_pred_r.choose.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := by
              have hpred_same_addr := hpred_r_accesses_dir.dirCorresponds.sameAddr
              simpa [hsame_cle] using hpred_same_addr
            have hsucc_addr_cle : hsucc_encap_dir_w.choose.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := by
              have hsucc_same_addr := hsucc_encap_dir_w.choose_spec.right.satisfyP.encapCorresponding.dirCorresponds.sameAddr
              simpa [hsame_cle] using hsucc_same_addr
            have hw_addr_cle : e_w.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := by
              have hw_addr := hsucc_same_entry_w.sameAddr
              exact hw_addr.trans hsucc_addr_cle
            have hpred_struct_w : hexists_pred_r.choose.struct = e_w.struct := by
              have hpred_struct_er := hpred_same_entry_er.sameStruct
              calc hexists_pred_r.choose.struct = e_r.struct := hpred_struct_er
                _ = e_w.struct := hsame_struct_w_r.symm
            have hpred_addr_w : hexists_pred_r.choose.addr = e_w.addr := by
              calc hexists_pred_r.choose.addr = (hw_c_and_g_lin.hreq's_dir_access.choose).addr := hpred_addr_cle
                _ = e_w.addr := by
                  symm
                  exact hw_addr_cle
            have hpred_same_entry_w : hexists_pred_r.choose.sameEntry n e_w := by
              constructor
              . case sameStruct => exact hpred_struct_w
              . case sameAddr => exact hpred_addr_w

            have hpred_same_entry_succ : hexists_pred_r.choose.sameEntry n hsucc_encap_dir_w.choose := by
              have hsame_entry_w_pred : e_w.sameEntry n hexists_pred_r.choose :=
                Event.same_entry_symm n hexists_pred_r.choose e_w hpred_same_entry_w
              exact Event.event_same_entry_trans (n := n) (e₁ := hexists_pred_r.choose)
                (e₂ := hsucc_encap_dir_w.choose) (e₃ := e_w) hsame_entry_w_pred hsucc_same_entry_w

            -- Show both pred_r and succ_w are cache events
            have hpred_is_cache : hexists_pred_r.choose.isCacheEvent :=
              orderBeforeDir_pred_is_cache_event n b init e_r hexists_pred_r hr_cluster.eAtCache

            have hsucc_is_cache : hsucc_encap_dir_w.choose.isCacheEvent := by
              -- Use the helper lemma: e_w is cache, e_w and succ_w are same entry, so succ_w is cache
              have hsucc_spec_full := hsucc_encap_dir_w.choose_spec.right
              simp only [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec_full
              exact orderAfterDir_succ_is_cache_event n b e_w hsucc_encap_dir_w.choose
                (fun x => Behaviour.succOnVdWithCorrespondingDir n b init x (hw_c_and_g_lin.hreq's_dir_access.choose))
                hsucc_spec_full hw_cluster.eAtCache

            -- Use cache ordering to get the contradiction
            cases hpred_ev : hexists_pred_r.choose with
            | cacheEvent ce_pred =>
              cases hsucc_ev : hsucc_encap_dir_w.choose with
              | cacheEvent ce_succ =>
                have hce_ordered := b.orderedAtEntry.cache_ordered ce_pred ce_succ
                have hce_encap_or_ordered := hce_ordered.ordered
                simp [CacheEvent.encapsulatedOrOrdered, CacheEvent.encapsulatedOrBefore] at hce_encap_or_ordered
                cases hce_encap_or_ordered with
                | inl hpred_before_or_in_succ =>
                  cases hpred_before_or_in_succ with
                  | inl hpred_encap_by_succ =>
                    -- succ encapsulates pred -> pred not bottom
                    have hencap_pred : ce_succ.Encapsulates n ce_pred := by
                      simpa [CacheEvent.EncapsulatedBy] using hpred_encap_by_succ
                    have hencap_event : hsucc_encap_dir_w.choose.Encapsulates n hexists_pred_r.choose := by
                      simpa [hsucc_ev, hpred_ev] using
                        (CacheEvent.encap_then_event_encap n ce_succ ce_pred hencap_pred)
                    have hpred_in_b : hexists_pred_r.choose ∈ b := hpred_r_accesses_dir.reqInB
                    have hencap_same : Event.EncapAtSameStructure n hsucc_encap_dir_w.choose hexists_pred_r.choose :=
                      { encap := hencap_event, sameEntry := Event.same_entry_symm n _ _ hpred_same_entry_succ }
                    exact (hpred_spec.isBottomPred hsucc_encap_dir_w.choose hsucc_encap_dir_w.choose_spec.left) hencap_same
                  | inr hpred_ob_succ =>
                    -- pred ordered before succ -> cle.oEnd < pred.oEnd < succ.oStart < cle.oStart
                    have h_contra : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := by
                      simp [hpred_ev, Event.oEnd, Event.oStart] at hpred_r_encap_cle
                      simp [hsucc_ev, Event.oStart, Event.oEnd] at hsucc_w_encap_cle
                      simp [CacheEvent.OrderedBefore] at hpred_ob_succ
                      calc (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < ce_pred.oEnd := hpred_r_encap_cle.2
                        _ < ce_succ.oStart := hpred_ob_succ
                        _ < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := hsucc_w_encap_cle.1
                    have hcle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
                    exact Nat.lt_asymm h_contra hcle_wf
                | inr hsucc_before_or_in_pred =>
                  cases hsucc_before_or_in_pred with
                  | inl hsucc_encap_by_pred =>
                    -- pred encapsulates succ -> succ not bottom
                    have hencap_succ : ce_pred.Encapsulates n ce_succ := by
                      simpa [CacheEvent.EncapsulatedBy] using hsucc_encap_by_pred
                    have hencap_event : hexists_pred_r.choose.Encapsulates n hsucc_encap_dir_w.choose := by
                      simpa [hsucc_ev, hpred_ev] using
                        (CacheEvent.encap_then_event_encap n ce_pred ce_succ hencap_succ)
                    have hsucc_in_b : hsucc_encap_dir_w.choose ∈ b := hsucc_encap_dir_w.choose_spec.left
                    have hencap_same : Event.EncapAtSameStructure n hexists_pred_r.choose hsucc_encap_dir_w.choose :=
                      { encap := hencap_event, sameEntry := hpred_same_entry_succ }
                    exact (hsucc_spec.isBottom hexists_pred_r.choose hpred_r_accesses_dir.reqInB) hencap_same
                  | inr hsucc_ob_pred =>
                    -- succ ordered before pred -> cle.oEnd < succ.oEnd < pred.oStart < cle.oStart
                    have h_contra : (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := by
                      simp [hpred_ev, Event.oEnd, Event.oStart] at hpred_r_encap_cle
                      simp [hsucc_ev, Event.oStart, Event.oEnd] at hsucc_w_encap_cle
                      simp [CacheEvent.OrderedBefore] at hsucc_ob_pred
                      calc (hw_c_and_g_lin.hreq's_dir_access.choose).oEnd < ce_succ.oEnd := hsucc_w_encap_cle.2
                        _ < ce_pred.oStart := hsucc_ob_pred
                        _ < (hw_c_and_g_lin.hreq's_dir_access.choose).oStart := hpred_r_encap_cle.1
                    have hcle_wf := (hw_c_and_g_lin.hreq's_dir_access.choose).oWellFormed
                    exact Nat.lt_asymm h_contra hcle_wf
              | directoryEvent _ =>
                exfalso
                simp [Event.isCacheEvent, hsucc_ev] at hsucc_is_cache
            | directoryEvent _ =>
              exfalso
              simp [Event.isCacheEvent, hpred_ev] at hpred_is_cache
          -- Case 3.3: e_w orderAfterDir, e_r orderAfterDir
          | orderAfterDir hreq_r_on_vd hsucc_encap_dir_r hsucc_same_protocol_r =>
            exfalso
            -- Both successors encapsulate the CLE
            have hsucc_w_encap_cle : hsucc_encap_dir_w.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap := hsucc_encap_dir_w.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap
            have hsucc_r_encap_cle : hsucc_encap_dir_r.choose.Encapsulates n (hw_c_and_g_lin.hreq's_dir_access.choose) := by
              have hsucc_encap := hsucc_encap_dir_r.choose_spec.right.satisfyP.encapCorresponding.reqEncapDir
              simpa [hsame_cle] using hsucc_encap

            -- Both successors are directory events encapsulating the same CLE
            -- They must be equal (by dir_event_of_req_event_unique)
            have hw_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hsucc_encap_dir_w.choose := by
              have := hsucc_encap_dir_w.choose_spec.right.satisfyP.encapCorresponding.dirOfReq
              exact this
            have hr_dir_of_req : (hw_c_and_g_lin.hreq's_dir_access.choose).dirEventOfReqEvent n hsucc_encap_dir_r.choose := by
              convert hsucc_encap_dir_r.choose_spec.right.satisfyP.encapCorresponding.dirOfReq using 2
            have hsucc_eq : hsucc_encap_dir_w.choose = hsucc_encap_dir_r.choose :=
              dir_event_of_req_event_unique hw_dir_of_req hr_dir_of_req
            -- Now both e_w and e_r have the same successor encapsulating CLE
            -- But e_w < e_r < succ, so succ cannot be immediate successor to both

            -- From hw_ob_r: e_w.oEnd < e_r.oStart
            simp only [Event.OrderedBefore] at hw_ob_r

            -- Both have immediate successor relationships
            have hw_before_succ : e_w.OrderedBefore n hsucc_encap_dir_w.choose := by
              have hsucc_spec := hsucc_encap_dir_w.choose_spec.right
              simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ
            have her_before_succ : e_r.OrderedBefore n hsucc_encap_dir_r.choose := by
              have hsucc_spec := hsucc_encap_dir_r.choose_spec.right
              simp [Behaviour.ImmediateBottomSuccSatisfyingProp] at hsucc_spec
              have hsucc_is_succ := hsucc_spec.isImmBottomSucc.isSucc
              simpa [Event.Successor, Event.Predecessor] using hsucc_is_succ

            simp only [Event.OrderedBefore] at hw_before_succ her_before_succ

            -- Contradiction: succ_w = succ_r but e_r is between e_w and succ
            -- violating immediate successor property
            sorry

/-
lemma CMCM.rf.sameGle.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hsame_gle : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.sameCluster.wImmPredRCle
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cluster : Event.sameProtocol n e_w e_r)
  (hevict_or_read_between_w_r_cle : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry

lemma CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_down : ReadDowngradeAtWrite.evictOrReadBetween.wAndRDown hw_c_and_g_lin hr_c_and_g_lin)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  sorry
-/

/- ========== END CMCM.RF case lemmas ========== -/


theorem CMCM.rf_holds
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  {hw_cluster : e_w.isClusterCache} {hr_cluster : e_r.isClusterCache}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  {hw_not_down : ¬ e_w.down} {hr_not_down : ¬ e_r.down}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  /- Synchronization conditions -/
  (hgle_cle_rf_constraints : CompoundProtocol.gleOrdering.Cases hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hr_not_ob_w : ¬ e_r.OrderedBefore n e_w)
  (hsucc_w_of_w_after_r : ∀ e_w_succ ∈ b, e_w_succ.isWrite ∧ e_w_succ.sameProtocol n e_w ∧ e_w_succ.sameStructure n e_w ∧
    e_w.OrderedBefore n e_w_succ → e_r.oEnd < e_w_succ.oEnd)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin
  := by
  -- probably want to start with cases of `e_w` and `e_r`'s GLEs.
  -- Only expand cases of `e_w` and `e_r`'s requests (coherent, non-coherent, release, acquire...) further into the subcases.

  let e_w_gle := hw_c_and_g_lin.hreq's_global_lin.choose
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  let e_w_cle := hw_c_and_g_lin.hreq's_dir_access.choose
  let e_r_cle := hr_c_and_g_lin.hreq's_dir_access.choose


  let test := hw_c_and_g_lin.hreq's_global_lin.choose_spec.right.isDirEvent

  cases hgle_cle_rf_constraints
  . case sameGle hsame_gle hcle_cases =>
    cases hcle_cases
    . case wEqRCle hsame_cle =>
      apply CMCM.rf.sameGle.sameCle hw_c_and_g_lin hr_c_and_g_lin hsame_gle hsame_cle (hw_cluster := hw_cluster) (hr_cluster := hr_cluster) (hw_not_down := hw_not_down) (hr_not_down := hr_not_down) (hr_not_ob_w := hr_not_ob_w) hknow_dir_access hno_intervening_writes hsucc_w_of_w_after_r
    . case otherCases hsame_as_gle_ob_cases =>
      cases hsame_as_gle_ob_cases
      . case wImmPredRCle hw_imm_pred_r_cle =>
        apply CMCM.rf.sameGle.wImmPredRCle hw_c_and_g_lin hr_c_and_g_lin
        . case hsame_gle => exact hsame_gle
        . case hw_imm_pred_r_cle => exact hw_imm_pred_r_cle
      . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
        apply CMCM.rf.sameGle.evictOrReadBetweenWAndRCleSameCluster hw_c_and_g_lin hr_c_and_g_lin
        . case hsame_gle => exact hsame_gle
        . case hevict_or_read_between_w_r_cle => exact hevict_or_read_between_w_r_cle
  . case wImmPredRGle hw_imm_pred_r_gle hcle_cases =>
      cases hcle_cases
      . case sameCluster hsame_cluster hsame_cluster_cases =>
        -- NOTE: potential to reuse some of the same cluster case lemmas
        -- from the same GLE & CLE case
        cases hsame_cluster_cases
        . case wImmPredRCle hw_imm_pred_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.wImmPredRCle hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hw_imm_pred_r_cle => exact hw_imm_pred_r_cle
        . case evictOrReadBetweenWAndRCleSameCluster hevict_or_read_between_w_r_cle =>
          apply CMCM.rf.wImmPredRGle.sameCluster.evictOrReadBetweenWAndRCleSameCluster hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hsame_cluster => exact hsame_cluster
          . case hevict_or_read_between_w_r_cle => exact hevict_or_read_between_w_r_cle
      . case diffCluster hdiff_cluster hdiff_cluster_cases =>
        cases hdiff_cluster_cases
        . case wCleImmPredDown hw_cle_imm_pred_r_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_r_down => exact hw_cle_imm_pred_r_down
        . case evictOrReadBetweenWAndRDown hw_cle_imm_pred_down =>
          apply CMCM.rf.wImmPredRGle.diffCluster.evictOrReadBetweenWAndRDown hw_c_and_g_lin hr_c_and_g_lin
          . case hw_imm_pred_r_gle => exact hw_imm_pred_r_gle
          . case hdiff_cluster => exact hdiff_cluster
          . case hw_cle_imm_pred_down => exact hw_cle_imm_pred_down
