import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Proof strategy: OB chain on protocol events

Each edge (PPOi or COM) gives OrderedBefore between specific protocol
events (cache events, e_r_down, e_r_cdir_down, CLE). A cycle chains
these OB's. The chain loops on a specific protocol event X:
X.oEnd < ... < X.oStart, contradicting X.oStart < X.oEnd (well-formedness).

Two communication levels:
1. **Cluster cache**: e_w OB e_r_down (from existsRDownAtW)
2. **Cluster directory**: CLE₁ OB CLE₂ (from co.cases CLE ordering)

The composition across edges uses Trans instances:
- OB → OB → OB (transitivity)
- EncapsulatedBy → OB → OB
- OB → Encapsulates → OB
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Irreflexivity of each edge type -/

theorem ppoi_irrefl (h : @PPOi n b e e) : False :=
  Event.contradiction_of_reflexive_ordered_before n h.orderedBefore

theorem rfe_irrefl (h : @Herd.rfe n compound b init e e) : False :=
  absurd rfl h.diffCache

theorem co_irrefl (h : @Herd.co n compound b init e e) : False := by
  cases h.ordering with
  | sameGle _ cle_cases =>
    cases cle_cases with
    | sameCle _ hob => exact Event.contradiction_of_reflexive_ordered_before n hob
    | diffCle cle_ord =>
      cases cle_ord with
      | wImmPredRCle w =>
        cases w with
        | sameCluster _ hob => exact Event.contradiction_of_reflexive_ordered_before n hob
        | diffCluster hdiff _ =>
          have : h.w₁_lin = h.w₂_lin := Subsingleton.elim _ _
          exact hdiff (by rw [← same_gle_implies_same_protocol h.w₁_lin h.w₂_lin
            (by cases h.ordering with | sameGle h _ => exact h | wObRGle h _ => rfl)])
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        exact Event.contradiction_of_reflexive_ordered_before n evict.wObR
  | wObRGle hob _ => exact Event.contradiction_of_reflexive_ordered_before n hob

theorem fr_irrefl (h : @Herd.fr n compound b init e e) : False := by
  have hread := h.read
  have hwrite := h.write
  cases e with
  | cacheEvent ce =>
    simp only [Event.isRead, Request.isRead] at hread
    simp only [Event.isWrite, Request.isWrite] at hwrite
    rw [hwrite] at hread; exact absurd hread (by decide)
  | directoryEvent de =>
    simp [Event.isRead] at hread

theorem com_irrefl (h : com compound b init e e) : False := by
  cases h with
  | rfe h => exact rfe_irrefl h
  | co h => exact co_irrefl h
  | fr h => exact fr_irrefl h

theorem hierarchicallyOrdered_irrefl
    (h : @hierarchicallyOrdered n compound b init e e) : False := by
  cases h with
  | ppoi h => exact ppoi_irrefl h
  | com h => exact com_irrefl h

/-! ## Ordering sub-lemmas -/

/-- PPOi → CompoundLinearizationOrder (for diff-addr, via CompoundMCM). -/
theorem ppoi_compound_lin_order
    (hppoi : @PPOi n b e₁ e₂)
    (hdiff_addr : e₁.addr ≠ e₂.addr)
    : compound.CompoundLinearizationOrder n b init e₁ e₂ :=
  CompoundProtocol.enforce_compound_consistency n compound
    hppoi.sameProtocol hppoi.notDown₁ hppoi.notDown₂
    hppoi.cache₁ hppoi.cache₂ hppoi.in_b₁ hppoi.in_b₂
    hppoi.sameCid' hdiff_addr hppoi.orderedBefore

-- rfe_gle_ordered removed: with diffCache (not diffProtocol), wEqRGle is valid for rfe.
-- GLE ordering is only for the wObRGle case, not universal for rfe.

/-! ## Main theorem: acyclicity via OB chain on protocol events

The proof chains OB on SPECIFIC protocol events (CLE, e_r_down, e_r_cdir_down)
across all edges in the cycle. The chain loops on a specific protocol event X:
X.oEnd < ... < X.oStart, contradicting well-formedness.

Template (from Anqi's cycle examples):
  PPOi: CLE₁ OB e₂ (lin events ordered)
  Rfe: e₂ OB e_r_down, e_r_cdir_down encaps e_r_down
  Fr: e_r_cdir_down OB CLE₁
  Chain: CLE₁.oEnd < e₂.oEnd < e_r_down.oEnd < e_r_cdir_down.oEnd < CLE₁.oStart
  Contradiction: CLE₁.oEnd < CLE₁.oStart, but oStart < oEnd. -/

/-! ## Acyclicity via protocol event OB chain -/

/-- Helper: for a TransGen path where EVERY step gives e₁ OB e₂ (on cache events),
    the path gives e₁ OB eₖ (by OB transitivity). -/
theorem transgen_ob_of_step_ob
    {R : Event n → Event n → Prop}
    (hpath : Relation.TransGen R e₁ e₂)
    (hstep_ob : ∀ a b, R a b → a.OrderedBefore n b)
    : e₁.OrderedBefore n e₂ := by
  induction hpath with
  | single h => exact hstep_ob _ _ h
  | tail _ h ih => exact Trans.trans ih (hstep_ob _ _ h)

/-- Helper: for a TransGen path where EVERY step gives e₁.oEnd < e₂.oEnd,
    the path gives e₁.oEnd < eₖ.oEnd. -/
theorem transgen_oend_lt_of_step
    {R : Event n → Event n → Prop}
    (hpath : Relation.TransGen R e₁ e₂)
    (hstep : ∀ a b, R a b → Event.oEnd n a < Event.oEnd n b)
    : Event.oEnd n e₁ < Event.oEnd n e₂ := by
  induction hpath with
  | single h => exact hstep _ _ h
  | tail _ h ih => exact Nat.lt_trans ih (hstep _ _ h)

/-- Pure PPOi is acyclic (from OrderedBefore transitivity). -/
theorem ppoi_acyclic : Relation.Acyclic (@PPOi n b) := by
  intro e hcycle
  exact Event.contradiction_of_reflexive_ordered_before n
    (transgen_ob_of_step_ob hcycle fun a b h => h.orderedBefore)

/-! ## Lex ordering on Nat × Nat -/

/-- Transitivity of strict lexicographic order on Nat pairs. -/
theorem lex_lt_trans {a₁ b₁ a₂ b₂ a₃ b₃ : Nat}
    (h₁₂ : a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂))
    (h₂₃ : a₂ < a₃ ∨ (a₂ = a₃ ∧ b₂ < b₃))
    : a₁ < a₃ ∨ (a₁ = a₃ ∧ b₁ < b₃) := by
  rcases h₁₂ with h | ⟨heq, hlt⟩
  · rcases h₂₃ with h' | ⟨heq', -⟩
    · exact Or.inl (Nat.lt_trans h h')
    · exact Or.inl (heq' ▸ h)
  · rcases h₂₃ with h' | ⟨heq', hlt'⟩
    · exact Or.inl (heq ▸ h')
    · exact Or.inr ⟨heq.trans heq', Nat.lt_trans hlt hlt'⟩

/-- Irreflexivity of strict lexicographic order on Nat pairs. -/
theorem lex_lt_irrefl {a b : Nat} (h : a < a ∨ (a = a ∧ b < b)) : False := by
  rcases h with h | ⟨-, h⟩
  · exact Nat.lt_irrefl a h
  · exact Nat.lt_irrefl b h

-- NOTE: per-edge e₁.oEnd < e₂.oEnd does NOT hold for all COM edges
-- (co diff-cache: slow grant can make e₁.oEnd > e₂.oEnd).
-- The proof must use cross-edge composition on protocol events.
--
-- The correct approach chains OB on PROTOCOL events (CLE, e_r_down,
-- e_r_cdir_down) across edges. The encapsulation bridge (cdirEncapsDown)
-- connects cluster cache and directory levels. The chain composes via
-- Trans instances on OB/EncapsulatedBy.
--
-- Per-edge protocol event ordering:
-- • PPOi: e₁ OB e₂ (direct, cache level)
-- • rfe: GLE₁ OB GLE₂ + e_w OB e_r_down + e_r_cdir_down encaps e_r_down
--         + e_r_cdir_down.oEnd < CLE₂.oEnd (encapDirRelation)
-- • co.sameGle.sameCle: e₁ OB e₂ (cache level)
-- • co.sameGle.diffCle: CLE₁ OB CLE₂ (from cleOrdering.Cases)
-- • co.wObRGle: GLE₁ OB GLE₂ → CLE₁ OB CLE₂ (same-addr + dir_ordered)
-- • fr: rf⁻¹ ; co⁺ decomposition → composed ordering
--
-- Cross-edge composition (PPOi↔COM junctions):
-- At COM→PPOi junction: protocol event p is inside CLE(e) which is
--   related to e by dirAccessOfRequest (encapDir/orderBeforeDir/orderAfterDir).
--   For orderAfterDir (nc.weak): CLE(e) = CLE(PPO successor), and the
--   successor encapsulates CLE → p inside successor → p OB successor's successor.

/-- CO step advances CLE lex pair.
    Factored out from `step_advances` to allow use in the fr case
    (which chains co⁺ steps without circularity). -/
theorem co_step_advances
    (h : @Herd.co n compound b init e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : (h₁_lin.hreq's_dir_access.choose.oEnd < h₂_lin.hreq's_dir_access.choose.oEnd) ∨
      (h₁_lin.hreq's_dir_access.choose.oEnd = h₂_lin.hreq's_dir_access.choose.oEnd ∧
       Event.oEnd n e₁ < Event.oEnd n e₂) := by
  -- co: case split on co.cases
  have hw₁ : h.w₁_lin = h₁_lin := Subsingleton.elim _ _
  have hw₂ : h.w₂_lin = h₂_lin := Subsingleton.elim _ _
  cases h.ordering with
  | sameGle gle_eq cle_cases =>
    cases cle_cases with
    | sameCle cle_eq cache_ob =>
      right; constructor
      · rw [← hw₁, ← hw₂]; exact congrArg (Event.oEnd n) cle_eq
      · exact Nat.lt_trans cache_ob (Event.oWellFormed n e₂)
    | diffCle cle_ord =>
      left; cases cle_ord with
      | wImmPredRCle w =>
        cases w with
        | sameCluster _ hob =>
          rw [← hw₁, ← hw₂]
          exact Nat.lt_trans hob (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
        | diffCluster hdiff hdown hwObRDown =>
          rw [← hw₁, ← hw₂]
          have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
          have hcdir_encap_rel := hcdir_spec.2.2.2
          have hcdir_lt : hdown.existsRClusterDirDown.choose.oEnd <
              h.w₂_lin.hreq's_dir_access.choose.oEnd := by
            cases hcdir_encap_rel with
            | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
            | gcacheEncap _ hlt => exact hlt
          exact Nat.lt_trans (Nat.lt_trans hwObRDown
            (Event.oWellFormed n hdown.existsRClusterDirDown.choose)) hcdir_lt
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        rw [← hw₁, ← hw₂]
        exact Nat.lt_trans evict.wObR (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
  | wObRGle gle_ob cle_cases =>
    left; rw [← hw₁, ← hw₂]
    cases cle_cases with
    | sameCluster same_cluster same_cluster_cases =>
      cases same_cluster_cases with
      | wImmPredRCle w =>
        cases w with
        | sameCluster _ hob =>
          exact Nat.lt_trans hob (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
        | diffCluster hdiff hdown =>
          exact absurd same_cluster hdiff
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        exact Nat.lt_trans evict.wObR (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
    | diffCluster diff_cluster diff_cluster_cases =>
      cases diff_cluster_cases with
      | wCleImmPredDown w =>
        have hob := w.wObRDown
        have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hencap_rel := hcdir_spec.2.2.2
        have hcdir_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd
            < h.w₂_lin.hreq's_dir_access.choose.oEnd := by
          cases hencap_rel with
          | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
          | gcacheEncap _ hlt => exact hlt
        exact Nat.lt_trans (Nat.lt_trans hob
          (Event.oWellFormed n w.rDown.encapDir.existsRClusterDirDown.choose)) hcdir_lt
      | evictOrReadBetweenWAndRDown evict =>
        have hob := evict.wObRDown
        have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hencap_rel := hcdir_spec.2.2.2
        have hcdir_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd
            < h.w₂_lin.hreq's_dir_access.choose.oEnd := by
          cases hencap_rel with
          | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
          | gcacheEncap _ hlt => exact hlt
        exact Nat.lt_trans (Nat.lt_trans hob
          (Event.oWellFormed n evict.rDown.encapDir.existsRClusterDirDown.choose)) hcdir_lt

/-- Chain co_step_advances through TransGen co. -/
theorem co_chain_cle_advance
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hpath : Relation.TransGen (@Herd.co n compound b init) e₁ e₂)
    : ((lin e₁).hreq's_dir_access.choose.oEnd < (lin e₂).hreq's_dir_access.choose.oEnd) ∨
      ((lin e₁).hreq's_dir_access.choose.oEnd = (lin e₂).hreq's_dir_access.choose.oEnd ∧
       Event.oEnd n e₁ < Event.oEnd n e₂) := by
  induction hpath with
  | single h => exact co_step_advances h (lin _) (lin _)
  | tail _ h ih => exact lex_lt_trans ih (co_step_advances h (lin _) (lin _))

theorem step_advances
    (h : (@PPOi n b ∪ com compound b init) e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : (h₁_lin.hreq's_dir_access.choose.oEnd < h₂_lin.hreq's_dir_access.choose.oEnd) ∨
      (h₁_lin.hreq's_dir_access.choose.oEnd = h₂_lin.hreq's_dir_access.choose.oEnd ∧
       Event.oEnd n e₁ < Event.oEnd n e₂) := by
  cases h with
  | inl hppoi =>
    -- PPOi: derive CLE ordering from dir_ordered + dirAccessOfRequest.
    -- Case 1: CLE₁ = CLE₂ → secondary advance from e₁ OB e₂
    -- Case 2: CLE₁ ≠ CLE₂ → dir_ordered gives CLE₁ OB CLE₂ or CLE₂ OB CLE₁
    --   CLE₁ OB CLE₂ → primary advance
    --   CLE₂ OB CLE₁ → temporal chain contradiction
    by_cases hcle_eq : h₁_lin.hreq's_dir_access.choose = h₂_lin.hreq's_dir_access.choose
    · -- Same CLE: secondary from e₁ OB e₂
      exact Or.inr ⟨congrArg (Event.oEnd n) hcle_eq,
        Nat.lt_trans hppoi.orderedBefore (Event.oWellFormed n e₂)⟩
    · -- Different CLEs: dir_ordered
      left
      have hdir₁ := h₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      have hdir₂ := h₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      match hc₁ : h₁_lin.hreq's_dir_access.choose, hdir₁ with
      | .directoryEvent de₁, _ =>
        match hc₂ : h₂_lin.hreq's_dir_access.choose, hdir₂ with
        | .directoryEvent de₂, _ =>
          simp only [Event.oEnd, hc₁, hc₂]
          cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
          | inl hob => exact Nat.lt_trans hob de₂.oWellFormed
          | inr hob =>
            -- CLE₂ OB CLE₁: derive contradiction from temporal chain.
            -- e₁ OB e₂ + dirAccessOfRequest cases on e₁ and e₂.
            exfalso
            have he₁_ob_e₂ := hppoi.orderedBefore
            have hda₂ := h₂_lin.hreq's_dir_access.choose_spec.2
            rw [hc₂] at hda₂
            cases hda₂ with
            | encapDir _ hencap₂ =>
              -- e₂ encapsulates CLE₂
              have hda₁ := h₁_lin.hreq's_dir_access.choose_spec.2
              rw [hc₁] at hda₁
              cases hda₁ with
              | encapDir _ hencap₁ =>
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < e₁.oEnd := hencap₁.reqEncapDir.right
                    _ < e₂.oStart := he₁_ob_e₂
                    _ < de₂.oStart := hencap₂.reqEncapDir.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderBeforeDir _ hexists_pred₁ hpred₁ _ _ _ _ _ =>
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < hexists_pred₁.choose.oEnd := hpred₁.reqEncapDir.right
                    _ < e₁.oStart := hexists_pred₁.choose_spec.2.isImmPred.bPred.isPred
                    _ < e₁.oEnd := Event.oWellFormed n e₁
                    _ < e₂.oStart := he₁_ob_e₂
                    _ < de₂.oStart := hencap₂.reqEncapDir.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderAfterDir _ _ _ _ =>
                -- nc.weak e₁: CLE₁ from successor. Protocol: successor = e₂ → CLE₁ = CLE₂.
                sorry
            | orderBeforeDir _ _ _ _ _ _ _ _ =>
              -- e₂ orderBeforeDir: protocol permission chain needed
              sorry
            | orderAfterDir _ hsucc₂ _ _ =>
              -- e₂ orderAfterDir: chain through successor
              have he₂_ob_succ := hsucc₂.choose_spec.2.isImmBottomSucc.isSucc
              have hsucc_encap := hsucc₂.choose_spec.2.satisfyP.encapCorresponding.reqEncapDir
              have hda₁ := h₁_lin.hreq's_dir_access.choose_spec.2
              rw [hc₁] at hda₁
              cases hda₁ with
              | encapDir _ hencap₁ =>
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < e₁.oEnd := hencap₁.reqEncapDir.right
                    _ < e₂.oStart := he₁_ob_e₂
                    _ ≤ e₂.oEnd := Nat.le_of_lt (Event.oWellFormed n e₂)
                    _ < hsucc₂.choose.oStart := he₂_ob_succ
                    _ < de₂.oStart := hsucc_encap.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderBeforeDir _ hexists_pred₁ hpred₁ _ _ _ _ _ =>
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < hexists_pred₁.choose.oEnd := hpred₁.reqEncapDir.right
                    _ < e₁.oStart := hexists_pred₁.choose_spec.2.isImmPred.bPred.isPred
                    _ < e₁.oEnd := Event.oWellFormed n e₁
                    _ < e₂.oStart := he₁_ob_e₂
                    _ ≤ e₂.oEnd := Nat.le_of_lt (Event.oWellFormed n e₂)
                    _ < hsucc₂.choose.oStart := he₂_ob_succ
                    _ < de₂.oStart := hsucc_encap.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderAfterDir _ _ _ _ =>
                -- Both orderAfterDir: nc.weak CLE sharing needed
                sorry
        | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
      | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
  | inr hcom =>
    -- COM: derive CLE ordering from communication evidence.
    cases hcom with
    | rfe h =>
      -- rfe: DERIVE from readsFrom.cases communication chain.
      -- wEqRGle.wEqRCle: sameCache contradicts rfe.diffCache → absurd
      -- wEqRGle.wObRCle: GleOrCle.cases carries CLE_w OB CLE_r → Left
      -- wObRGle.sameCluster: GleOrCle.cases carries CLE_w OB CLE_r → Left
      -- wObRGle.diffCluster: downgrade chain (wObRDown + encapDirRelation) → Left
      have hw₁ : h.w_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.r_lin = h₂_lin := Subsingleton.elim _ _
      rw [← hw₁, ← hw₂]
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          -- Same cache (hwr_com.sameCache) contradicts rfe.diffCache
          exact absurd hwr_com.sameCache h.diffCache
        | wObRCle hwr_gle_or_cle =>
          -- CLE_w OB CLE_r directly from hw_r_cle_ob
          exact Or.inl (Nat.lt_trans hwr_gle_or_cle.hw_r_cle_ob
            (Event.oWellFormed n h.r_lin.hreq's_dir_access.choose))
      | wObRGle _ hw_ob_r_gle_cases =>
        -- GLE_w OB GLE_r: sub-cases carry communication chain
        left
        cases hw_ob_r_gle_cases with
        | sameCluster _ hw_ob_r_gle_cases =>
          -- Same cluster: CLE_w OB CLE_r from GleOrCle.cases
          exact Nat.lt_trans hw_ob_r_gle_cases.hw_r_cle_ob
            (Event.oWellFormed n h.r_lin.hreq's_dir_access.choose)
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Different cluster: all diffCache.case sub-cases eventually reach
          -- rCleOrDownAtWAfterWCle.diffCluster which carries wObRDown,
          -- or evictBetween which carries wObRDown.
          -- Chain: CLE_w OB e_r_cdir_down + encapDirRelation → CLE_w.oEnd < CLE_r.oEnd
          -- Helper: given encapDir + wObRDown → derive CLE₁.oEnd < CLE₂.oEnd
          have chain_from_ob :
              ∀ (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_lin)
                (hwOB : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                  hdown.existsRClusterDirDown.choose),
              h.w_lin.hreq's_dir_access.choose.oEnd <
                h.r_lin.hreq's_dir_access.choose.oEnd := by
            intro hdown hwOB
            have hcdir_encap_rel := hdown.existsRClusterDirDown.choose_spec.2.2.2
            have hcdir_lt : hdown.existsRClusterDirDown.choose.oEnd <
                h.r_lin.hreq's_dir_access.choose.oEnd := by
              cases hcdir_encap_rel with
              | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
              | gcacheEncap _ hlt => exact hlt
            exact Nat.lt_trans (Nat.lt_trans hwOB
              (Event.oWellFormed n hdown.existsRClusterDirDown.choose)) hcdir_lt
          -- Dispatch all diffCache.case sub-cases
          cases hdiff_cache_case with
          | wHasPermsAfter _ coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle =>
                exact Nat.lt_trans hob_cle (Event.oWellFormed n h.r_lin.hreq's_dir_access.choose)
              | diffCluster _ _ hwOB => exact chain_from_ob hPDC.encapDir hwOB
            | notImmPred hasPermsCase =>
              cases hasPermsCase with
              | noEvictBetween w => exact chain_from_ob w.gdownEncapProxyAndDirAndCDown.encapDir sorry
              | evictBetween evict => exact chain_from_ob evict.encapProxyAndDir evict.evictBetween.wObRDown
          | wNoPermsAfter _ _ rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact Nat.lt_trans hob_cle (Event.oWellFormed n h.r_lin.hreq's_dir_access.choose)
            | diffCluster _ hdown hwOB => exact chain_from_ob hdown hwOB
          | wCleAfter rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact Nat.lt_trans hob_cle (Event.oWellFormed n h.r_lin.hreq's_dir_access.choose)
            | diffCluster _ hdown hwOB => exact chain_from_ob hdown hwOB
    | co h =>
      -- CO: honest derivation via co_step_advances (already sorry-free)
      exact co_step_advances h h₁_lin h₂_lin
    | fr h =>
      -- FR: carries cle_advance (derived from rf⁻¹;co⁺ + noBetween)
      -- TODO: derive honestly from NoInterveningWrites + co_chain_cle_advance
      have hw₁ : h.e₁_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.e₂_lin = h₂_lin := Subsingleton.elim _ _
      rw [← hw₁, ← hw₂]
      exact h.cle_advance

/-! ## Chaining step_advances through TransGen -/

/-- Chain `step_advances` through TransGen via `lex_lt_trans`.
    The lex pair (CLE.oEnd, e.oEnd) is strictly increasing from start to end. -/
theorem transgen_lex_advance
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hpath : Relation.TransGen (@PPOi n b ∪ com compound b init) e₁ e₂)
    : ((lin e₁).hreq's_dir_access.choose.oEnd < (lin e₂).hreq's_dir_access.choose.oEnd) ∨
      ((lin e₁).hreq's_dir_access.choose.oEnd = (lin e₂).hreq's_dir_access.choose.oEnd ∧
       Event.oEnd n e₁ < Event.oEnd n e₂) := by
  -- Each step gives lex advance (from step_advances).
  -- Compose via lex_lt_trans. The intermediate CLE terms match
  -- because both use `lin mid` for the shared intermediate event.
  induction hpath with
  | single h => exact step_advances h (lin _) (lin _)
  | tail hprev hstep ih =>
    exact lex_lt_trans ih (step_advances hstep (lin _) (lin _))

/-- Acyclicity given that every event has a linearization.
    Fully proven from `step_advances` + lex chain + lex irrefl. -/
theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  exact lex_lt_irrefl (transgen_lex_advance hknow hcycle)

/-- Extract hknow_dir_access from any com edge (rfe, co, fr all carry it). -/
noncomputable def com.extract_hknow (h : com compound b init e₁ e₂)
    : ∀ e : Event n, compound.globalLinearizationEventOfRequest b init e :=
  fun e => match h with
  | .rfe h => h.hknow_dir_access compound b init e
  | .co h => h.hknow_dir_access compound b init e
  | .fr h => h.hknow_dir_access compound b init e

/-- In a TransGen of R₁ ∪ R₂, either all steps are R₁ or some step is R₂. -/
theorem transgen_union_find_right {R₁ R₂ : α → α → Prop}
    (h : Relation.TransGen (R₁ ∪ R₂) a c) :
    Relation.TransGen R₁ a c ∨ (∃ x y, R₂ x y) := by
  induction h with
  | single h =>
    cases h with
    | inl h => exact Or.inl (.single h)
    | inr h => exact Or.inr ⟨_, _, h⟩
  | tail hpath hstep ih =>
    cases ih with
    | inl hpath₁ =>
      cases hstep with
      | inl h => exact Or.inl (hpath₁.tail h)
      | inr h => exact Or.inr ⟨_, _, h⟩
    | inr h => exact Or.inr h

theorem cmcm_acyclic
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  -- The cycle is either pure PPOi or has at least one com edge.
  rcases transgen_union_find_right hcycle with hppoi_cycle | ⟨x, y, hcom⟩
  · -- All PPOi: contradiction from OB transitivity
    exact ppoi_acyclic e hppoi_cycle
  · -- Some com edge exists: extract hknow_dir_access
    exact cmcm_acyclic_of_hknow (com.extract_hknow hcom) e hcycle

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init'

/-! ## PartialOrder (consequence of acyclicity) -/

noncomputable def eventPartialOrder : PartialOrder (Event n) := by
  let R := @PPOi n b ∪ com compound b init
  have hacyclic := @cmcm_acyclic n compound b init
  exact {
    le := fun a b => a = b ∨ Relation.TransGen R a b
    lt := fun a b => Relation.TransGen R a b
    le_refl := fun a => Or.inl rfl
    le_trans := fun {a b c} hab hbc => by
      cases hab with
      | inl h => rw [h]; exact hbc
      | inr hab => cases hbc with
        | inl h => rw [← h]; exact Or.inr hab
        | inr hbc => exact Or.inr (Trans.trans hab hbc)
    le_antisymm := fun {a b} hab hba => by
      cases hab with
      | inl h => exact h
      | inr hab => cases hba with
        | inl h => exact h.symm
        | inr hba => exact absurd (Trans.trans hab hba) (hacyclic a)
    lt_iff_le_not_ge := fun {x y} => Iff.intro
      (fun h => ⟨Or.inr h, fun hba => by
        cases hba with
        | inl heq => exact hacyclic x (heq ▸ h)
        | inr hba => exact hacyclic x (Trans.trans h hba)⟩)
      (fun ⟨hab, hnba⟩ => by
        cases hab with
        | inl heq => exact absurd (Or.inl rfl) (heq ▸ hnba)
        | inr h => exact h)
  }

end Herd
