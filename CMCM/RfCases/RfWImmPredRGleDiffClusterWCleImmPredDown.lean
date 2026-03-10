import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.RfCases.RfSameGleWImmPredRCleHelpers

/-- Proof that reads-from is correct when e_w's GLE is the immediate predecessor of e_r's GLE,
    the events are in different clusters, and e_w's CLE is the immediate predecessor of the
    directory-level read downgrade at e_w's protocol.

    Uses the `diffCluster` constructor of `sameOrDifferentCluster.cases` with
    `wHasPermsAfter.notImmPred.noEvictBetween` for the coherent case. -/
lemma CMCM.rf.wImmPredRGle.diffCluster.wCleImmPredDown
  {cmp : CompoundProtocol n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_gle : CompoundProtocol.gleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cluster : ¬ Event.sameProtocol n e_w e_r)
  (hw_cle_imm_pred_r_down : ReadDowngradeAtWrite.wCleImmPredDown hw_c_and_g_lin hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  (hw_in_b : e_w ∈ b) (hw_cluster_cache : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : Behaviour.readsFrom.cases hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access
  := by
  -- GLE_w is ordered before GLE_r (from immediate predecessor)
  apply Behaviour.readsFrom.cases.wObRGle
    (hw_imm_pred_r_gle.isImmPred.bPred.isPred)
  -- Different cluster → different cache
  have hdiff_cache : e_w.struct ≠ e_r.struct :=
    fun h => hdiff_cluster (sameStructure_implies_sameProtocol h)
  refine .diffCluster (r_is_read := hr_is_read) hdiff_cluster hdiff_cache ?_ ?_
  · -- encapGDown
    constructor
    intro hstate_sw
    have ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, h_wrapper⟩ :=
      diffCache_coherent_globalDowngrade hr_c_and_g_lin
    have h_dpow := h_wrapper.downgradePrevOwner
    have h_at_prev := h_dpow.atPrevOwner
    have h_fwd := h_dpow.fwdFromRequester
    have h_is_cache := h_dpow.downAtCache
    -- hstate_sw says directoryStateMadeOn = .SW with owner e_w.gCacheOfCEvent
    -- atPrevOwner uses the same (b.stateBefore ...).directory = directoryStateMadeOn
    unfold Behaviour.directoryStateMadeOn at hstate_sw
    rw [hstate_sw] at h_at_prev
    -- h_at_prev : e_r_gdown.downgradeAtPrevOwner n (.SW ⟨SW, _⟩ e_w.gCacheOfCEvent)
    -- Case-split: e_r_gdown must be a cache event (from downAtCache)
    cases e_r_gdown with
    | directoryEvent de =>
      exact absurd h_is_cache (by simp [Event.isCacheEvent])
    | cacheEvent ce =>
      refine ⟨.cacheEvent ce, he_r_gdown_in_b, ?_, ?_⟩
      · -- ce.cid = e_w.gCacheOfCEvent (from downgradeAtPrevOwner on .SW state)
        simp only [Event.downgradeAtPrevOwner] at h_at_prev
        simp only [Event.cid]
        exact h_at_prev
      · -- ce.down (from downgradeCorrespondingToRequest → downgradeOfReq.isDown)
        exact downgradeCorrespondingToRequest_isDown h_fwd
  · -- diffCache.case
    -- Why by_cases on e_w.isCoherent? Why not by_cases of if e_w leaves SW state?
    by_cases hw_coherent : e_w.isCoherent
    · -- Coherent case: write has permissions after
      have hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW :=
        coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster_cache.eAtCache
      refine .wHasPermsAfter hw_leaves_SW (.notImmPred (.noEvictBetween ⟨hw_cle_imm_pred_r_down.rDown, ?_, ?_, hw_cle_imm_pred_r_down.rDown.existsRDownAtW.choose_spec.right.right.right⟩))
      · -- noWriteBtn: Event.Between.noWrite b init e_w e_r_down e_w_cle e_r_cdir_down
        -- Proof strategy: For any intervening cluster-cache write e_inter (not a downgrade):
        --   - Same cache as e_w: e_inter's CLE can't be between e_w_cle and e_r_cdir_down
        --     because e_w_cle is the immediate predecessor of e_r_cdir_down (nothing between them).
        --   - Different cache, same cluster: the dir write downgrade from e_inter can't be
        --     between e_w_cle and e_r_cdir_down by the same immPred argument.
        --   - Different cluster: no diff-cluster dir write downgrade between the CLEs,
        --     using NoInterveningWrites.constraints.diffClusterNotBetweenCles
        --     (the interval [e_w_cle, e_r_cdir_down] ⊂ [e_w_cle, e_r_cle]).
        -- All cases are proved by showing the boundary events are too tight for any write's
        -- CLE to fit between them.
        intro e_inter he_inter hcluster hwrite hnotdown
        have hcontra := hno_intervening_writes e_inter he_inter hcluster hwrite hnotdown
        -- Use immPred to show nothing can be between e_w_cle and e_r_cdir_down
        sorry
      · -- noEvictBtn: Event.Between.noEvict b e_w e_r_down
        -- Proof strategy: ∀ e_inter ∈ b, e_inter.Between e_w e_r_down → ¬ e_inter.isEvictSW
        -- Since e_w_cle is immPred of e_r_cdir_down, any cache event at the same cache
        -- between e_w and e_r_down would need a CLE between e_w_cle and e_r_cdir_down,
        -- but nothing is between them (from ImmediateBottomPredecessor).
        intro e_inter he_inter hbetween
        -- hbetween.interBetween gives e_inter ordered between e_w and e_r_down
        -- hbetween.sameCache gives e_inter at same cache as e_w and e_r_down
        -- hbetween.coherentRead gives e_r_down.isCoherent
        -- Use hw_cle_imm_pred_r_down.wCleImmPredRDown to show no intermediate events
        sorry
    · -- Non-coherent case: split on whether write has perms or not
      have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
      -- Need rCleAfterWCle: e_w_cle.OrderedBefore n e_r_cle
      -- From hw_cle_imm_pred_r_down: e_w_cle is immPred of e_r_cdir_down, which is before e_r_cle
      have hr_cle_after : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin := by
        sorry -- Derive from e_w_cle < e_r_cdir_down < e_r_cle ordering chain
      -- dirAccessOfRequest determines whether write has missing perms
      have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
      cases hw_dir_access with
      | encapDir hreq_missing_perms _ =>
        -- NC write with missing perms → wNoPermsAfter
        exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
      | orderBeforeDir _ _ _ _ _ _ _ _ =>
        -- NC write with perms (predecessor obtained dir access) → wCleAfter
        exact .wCleAfter hr_cle_after
      | orderAfterDir _ _ _ _ =>
        -- NC weak request on Vd (e.g. writeback) → wCleAfter
        exact .wCleAfter hr_cle_after
