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

-- Two non-downgrade cache events at same cache: ¬ e₂ OB e₁ → e₁ OB e₂.
-- Generalization of eq_gle_cle_implies_write_before_read (which carries unused isRead).
theorem cache_events_ordered_from_not_reverse
    {b : Behaviour n} {e₁ e₂ : Event n}
    (h₁_cluster : e₁.isClusterCache) (h₂_cluster : e₂.isClusterCache)
    (h₁_notdown : ¬ e₁.down) (h₂_notdown : ¬ e₂.down)
    (h_not_reverse : ¬ e₂.OrderedBefore n e₁)
    : e₁.OrderedBefore n e₂ := by
  match he₁ : e₁, h₁_cluster.eAtCache with
  | .cacheEvent ce₁, _ =>
    match he₂ : e₂, h₂_cluster.eAtCache with
    | .cacheEvent ce₂, _ =>
      have h₁_nd : ¬ ce₁.down := by simpa [Event.down, he₁] using h₁_notdown
      have h₂_nd : ¬ ce₂.down := by simpa [Event.down, he₂] using h₂_notdown
      simp only [Event.OrderedBefore, Event.oEnd, Event.oStart, he₁, he₂] at h_not_reverse
      cases (b.orderedAtEntry.cache_ordered ce₁ ce₂).ordered with
      | inl h => cases h with
        | inl henc => exact absurd (b.orderedAtEntry.cache_encap_rule ce₂ ce₁ henc) h₁_nd
        | inr hob => simpa [Event.OrderedBefore, Event.oEnd, Event.oStart, he₁, he₂] using hob
      | inr h => cases h with
        | inl henc => exact absurd (b.orderedAtEntry.cache_encap_rule ce₁ ce₂ henc) h₂_nd
        | inr hob => exact absurd hob h_not_reverse
    | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
  | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh

-- CO theorem: derive co.ordering from protocol axioms.
-- Given two writes to the same address with linearization events,
-- determine the ordering case (sameCache / sameClusDiffCache / diffClus).
theorem co_ordering_holds
    (hw₁ : e₁.isWrite) (hw₂ : e₂.isWrite)
    (hsame_addr : e₁.addr = e₂.addr)
    (w₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (w₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (h_in_b₁ : e₁ ∈ b) (h_in_b₂ : e₂ ∈ b)
    (h_cache₁ : e₁.isClusterCache) (h_cache₂ : e₂.isClusterCache)
    (h_notdown₁ : ¬ e₁.down) (h_notdown₂ : ¬ e₂.down)
    (h_dir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    -- Direction: e₂ is not before e₁ (e₂ overwrites e₁, so e₁ comes first).
    (h_not_reverse : ¬ e₂.OrderedBefore n e₁)
    -- The key input: GLE ordering determines the high-level case.
    (h_gle_ordering : CompoundProtocol.gleOrdering.Cases w₁_cmpLin w₂_cmpLin)
    : co.ordering w₁_cmpLin w₂_cmpLin := by
  -- Case-split on GLE ordering: same GLE or w₁'s GLE OB w₂'s GLE.
  cases h_gle_ordering with
  | sameGle same_gle cle_cases =>
    -- Same GLE → same or different cluster at CLE level.
    cases cle_cases with
    | wEqRCle w_r_cle_eq =>
      -- Same CLE → same cache (same directory entry → same struct).
      -- e₁ OB e₂ from cache_ordered + h_not_reverse.
      have h_same_struct := same_cle_implies_same_struct w₁_cmpLin w₂_cmpLin w_r_cle_eq
      -- cache_ordered gives e₁ OB e₂ ∨ e₂ OB e₁. h_not_reverse eliminates reverse.
      have h_e₁_ob_e₂ : e₁.OrderedBefore n e₂ :=
        cache_events_ordered_from_not_reverse (b := b) h_cache₁ h_cache₂ h_notdown₁ h_notdown₂ h_not_reverse
      exact .sameCache w_r_cle_eq same_gle h_e₁_ob_e₂
    | otherCases other =>
      -- Same GLE → same protocol (same_gle_implies_same_protocol).
      exact .sameClusDiffCache (same_gle_implies_same_protocol w₁_cmpLin w₂_cmpLin same_gle) (Or.inl same_gle) other
  | wObRGle w_ob_r_gle cle_cases =>
    -- w₁'s GLE OB w₂'s GLE.
    cases cle_cases with
    | sameCluster same_prot cle_ord =>
      -- Same cluster, GLE₁ OB GLE₂ → sameClusDiffCache.
      exact .sameClusDiffCache same_prot (Or.inr w_ob_r_gle) cle_ord
    | diffCluster diff_prot cle_ord =>
      -- Different cluster → diffClus.
      exact .diffClus diff_prot w_ob_r_gle cle_ord

end Herd
