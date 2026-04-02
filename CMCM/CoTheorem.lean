import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.Herd.Defs

variable {n : ℕ}

/-! # CO Theorem: Coherence Order from Protocol Axioms

Derive `co.ordering` for two writes to the same address from protocol axioms.
The communication mechanism (downgrade chain) is the SAME as RF — the second
write's request triggers a downgrade at the first write's cache. The evidence
structures (SameCluster.cleOb.cleOrdering.Cases, DifferentCluster.cleOB.cleOrdering.Cases)
are shared with RF and parameterized by linearization events (no isRead constraint).

The CO theorem mirrors the RF theorem with isWrite replacing isRead for the
second event. ~95% of RF infrastructure is reused.
-/

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
variable {e₁ e₂ : Event n}

-- CO theorem: derive co.ordering from protocol axioms.
-- Given two writes to the same address with linearization events,
-- determine the ordering case (sameCache / sameClusDiffCache / diffClus).
theorem co_ordering_holds
    (hw₁ : e₁.isWrite) (hw₂ : e₂.isWrite)
    (hsame_addr : e₁.addr = e₂.addr)
    (w₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (w₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h_in_b₁ : e₁ ∈ b) (h_in_b₂ : e₂ ∈ b)
    (h_cache₁ : e₁.isClusterCache) (h_cache₂ : e₂.isClusterCache)
    (h_notdown₁ : ¬ e₁.down) (h_notdown₂ : ¬ e₂.down)
    (h_dir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    -- The key input: GLE ordering determines the high-level case.
    (h_gle_ordering : CompoundProtocol.gleOrdering.Cases w₁_lin w₂_lin)
    : co.ordering w₁_lin w₂_lin := by
  -- Case-split on GLE ordering: same GLE or w₁'s GLE OB w₂'s GLE.
  cases h_gle_ordering with
  | sameGle same_gle cle_cases =>
    -- Same GLE → same or different cluster at CLE level.
    cases cle_cases with
    | wEqRCle w_r_cle_eq =>
      -- Same CLE. Two writes at same address with same CLE → sameCache.
      -- Need e₁ OB e₂ from SWMR/cache serialization.
      sorry
    | otherCases other =>
      -- Same GLE, CLEs differ → sameClusDiffCache.
      exact .sameClusDiffCache sorry other
  | wObRGle w_ob_r_gle cle_cases =>
    -- w₁'s GLE OB w₂'s GLE.
    cases cle_cases with
    | sameCluster same_prot cle_ord =>
      -- Same cluster, GLE₁ OB GLE₂ → sameClusDiffCache.
      exact .sameClusDiffCache same_prot cle_ord
    | diffCluster diff_prot cle_ord =>
      -- Different cluster → diffClus.
      exact .diffClus diff_prot cle_ord

end Herd
