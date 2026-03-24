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
  absurd rfl h.diffProtocol

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

/-- rfe → GLE ordering (from readsFrom.cases, wObRGle branch). -/
theorem rfe_gle_ordered
    (h : @Herd.rfe n compound b init e₁ e₂)
    : h.w_lin.hreq's_global_lin.choose.OrderedBefore n
      h.r_lin.hreq's_global_lin.choose := by
  cases h.readsFrom with
  | wEqRGle _ hwr_same_cluster _ => exact absurd hwr_same_cluster h.diffProtocol
  | wObRGle hw_r_gle_ob _ => exact hw_r_gle_ob

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

/-- Every edge in PPOi ∪ com gives a CLE-lexicographic ordering:
    either the CLE strictly advances, or CLEs are equal and e₁ OB e₂.
    Requires linearization witnesses (from `hknow_dir_access` or com edges).

    This is the key per-step lemma for the acyclicity proof.
    A cycle forces all CLEs equal (non-decreasing in a cycle → constant),
    then all steps give OB on cache events → chain gives e OB e → contradiction. -/
theorem step_cle_lex
    (h : (@PPOi n b ∪ com compound b init) e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : (h₁_lin.hreq's_dir_access.choose.oEnd < h₂_lin.hreq's_dir_access.choose.oEnd) ∨
      (h₁_lin.hreq's_dir_access.choose = h₂_lin.hreq's_dir_access.choose ∧
       e₁.OrderedBefore n e₂) := by
  cases h with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ on same cache, same address.
    -- CLE₁ and CLE₂ are at same cluster directory, same address.
    -- dir_ordered gives CLE₁ OB CLE₂ or CLE₁ = CLE₂ or CLE₂ OB CLE₁.
    -- Case CLE₁ = CLE₂: Right with OB from PPOi.orderedBefore.
    -- Case CLE₁ OB CLE₂: Left (strict CLE advance).
    -- Case CLE₂ OB CLE₁: contradiction (requires 9-case dirAccessOfRequest analysis).
    sorry
  | inr hcom =>
    -- COM: same-address communication edge.
    -- rfe: GLE₁ OB GLE₂ → CLE₁ OB CLE₂ (same-addr dir_ordered excludes CLE₂ OB CLE₁).
    -- co.sameGle.sameCle: same CLE + e₁ OB e₂ → Right.
    -- co.sameGle.diffCle: CLE₁ OB CLE₂ from cleOrdering.Cases → Left.
    -- co.wObRGle: GLE₁ OB GLE₂ → CLE₁ OB CLE₂ → Left.
    -- fr: composed from rf⁻¹ ; co⁺ → CLE ordering from intermediate writes.
    sorry

/-- From `step_cle_lex` applied to a cycle: all CLEs must be equal,
    then all steps give OB on cache events. -/
theorem cmcm_acyclic
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  -- Proof strategy:
  -- 1. If the cycle is pure PPOi: ppoi_acyclic gives contradiction.
  -- 2. If the cycle has a com edge: extract linearization witnesses.
  --    Apply step_cle_lex to each step:
  --    a. CLE.oEnd is non-decreasing along the cycle (from step_cle_lex).
  --    b. Non-decreasing in a cycle → constant → all CLEs equal.
  --    c. All CLEs equal → every step gives e₁ OB e₂ (from step_cle_lex Right).
  --    d. Chain of OB → e OB e → contradiction (Event.contradiction_of_reflexive_ordered_before).
  sorry

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
