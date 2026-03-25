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
  cases h.comm with
  | sameCache _ hob => exact Event.contradiction_of_reflexive_ordered_before n hob
  | sameClusDiffCache _ cle_ord =>
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob => exact Event.contradiction_of_reflexive_ordered_before n hob
      | diffCluster hdiff _ _ => exact absurd rfl hdiff
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact Event.contradiction_of_reflexive_ordered_before n evict.wObR
  | diffClus hdiff _ => exact absurd rfl hdiff

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

/-! ## StepOrdering: ordering between linearization points

Each cache event e has a linearization point `lin(e)` = CLE.
Each edge derives `StepOrdering lin(e₁) lin(e₂)` using auxiliary
protocol events (e_r_down, e_r_cdir_down, cache events) from the
PPOi/COM communication evidence.

StepOrdering has 4 constructors matching the OB/Encap chain shape.
Transitivity composes chains. Irreflexivity from OB irreflexivity.
A cycle gives StepOrdering lin(e) lin(e) → contradiction. -/

/-- Ordering between linearization points, connected via auxiliary
    protocol events through OB and Encapsulates/EncapsulatedBy. -/
inductive StepOrdering : Event n → Event n → Prop where
  /-- Direct OB between linearization points -/
  | ob (h : l₁.OrderedBefore n l₂) : StepOrdering l₁ l₂
  /-- OB to intermediate, intermediate inside target lin point -/
  | obEncap (p : Event n) (h_ob : l₁.OrderedBefore n p) (h_enc : p.EncapsulatedBy n l₂)
      : StepOrdering l₁ l₂
  /-- Same linearization point: cache events advance but CLE stays.
      l₁ = l₂ = CLE, with cache events e₁ OB e₂ that encapsulate CLE.
      The previous/next steps connect to/from this shared CLE. -/
  | sameLin (e₁' e₂' : Event n) (h_eq : l₁ = l₂)
      (h_enc₁ : l₁.EncapsulatedBy n e₁') (h_ob : e₁'.OrderedBefore n e₂')
      (h_enc₂ : l₂.EncapsulatedBy n e₂') : StepOrdering l₁ l₂


/-- StepOrdering is transitive. 3 constructors × 3 = 9 cases. -/
theorem StepOrdering.trans {l₁ l₂ l₃ : Event n}
    (h₁₂ : StepOrdering l₁ l₂) (h₂₃ : StepOrdering l₂ l₃) : StepOrdering l₁ l₃ := by
  cases h₁₂ with
  | ob h₁ =>
    cases h₂₃ with
    | ob h₂ => exact .ob (Trans.trans h₁ h₂)
    | obEncap p hp hpe => exact .obEncap p (Trans.trans h₁ hp) hpe
    | sameLin _ _ heq _ _ _ => subst heq; exact .ob h₁
  | obEncap q hq hqe =>
    cases h₂₃ with
    | ob h₂ => exact .ob (Trans.trans hq (Event.encap_by_order_trans n hqe h₂))
    | obEncap p hp hpe => exact .obEncap p (Trans.trans hq (Event.encap_by_order_trans n hqe hp)) hpe
    | sameLin _ _ heq _ _ _ => subst heq; exact .obEncap q hq hqe
  | sameLin e₁' e₂' heq he₁ hob he₂ =>
    subst heq; exact h₂₃

/-- StepOrdering is irreflexive. -/
theorem StepOrdering.irrefl {l : Event n} (h : StepOrdering l l) : False := by
  cases h with
  | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
  | obEncap p hp hpe =>
    exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans hp (Event.oWellFormed n p)) hpe.right)
  | sameLin e₁' e₂' heq he₁ hob he₂ =>
    have : l.oEnd < l.oEnd :=
      calc l.oEnd
        _ < e₁'.oEnd := he₁.right
        _ < e₂'.oStart := hob
        _ < l.oStart := he₂.left
        _ < l.oEnd := Event.oWellFormed n l
    exact Nat.lt_irrefl _ this

/-- Chain StepOrdering through TransGen. -/
theorem StepOrdering.of_transGen
    (h : Relation.TransGen (@StepOrdering n) l₁ l₂) : StepOrdering l₁ l₂ := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact StepOrdering.trans ih h

/-- StepOrdering is acyclic. -/
theorem StepOrdering.acyclic : Relation.Acyclic (@StepOrdering n) := by
  intro l hcycle
  exact StepOrdering.irrefl (StepOrdering.of_transGen hcycle)

/-- Map each PPOi ∪ com step to a StepOrdering between linearization points.
    PPOi: direct OB (e₁ OB e₂).
    rfe/co/fr: extract protocol events from communication evidence. -/
theorem step_to_ordering
    (h : (@PPOi n b ∪ com compound b init) e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂. Connect CLEs through cache events.
    -- CLE₁ relates to e₁ via dirAccessOfRequest.
    -- CLE₂ relates to e₂ via dirAccessOfRequest.
    -- Cases depend on dirAccessOfRequest for each event.
    -- For encapDir: CLE EncapBy e → encapObEncap(e₁, e₂) with e₁, e₂ inside CLEs
    -- For orderBeforeDir: CLE OB e → chain CLE₁ OB e₁ OB e₂ → CLE₁ OB CLE₂
    -- For orderAfterDir: e OB CLE → cache events serve as intermediaries
    sorry
  | inr hcom =>
    cases hcom with
    | rfe h =>
      -- rfe: extract protocol events from readsFrom.cases
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          -- Same CLE, same cache: e_w OB e_r. Both inside same CLE.
          sorry -- encapObEncap with e₁, e₂ inside shared CLE
        | wObRCle hwr_gle_or_cle =>
          -- CLE_w OB CLE_r directly (same cluster, cluster dir serialization)
          exact .ob (by
            rw [← show h.w_lin = lin e₁ from Subsingleton.elim _ _,
                ← show h.r_lin = lin e₂ from Subsingleton.elim _ _]
            exact hwr_gle_or_cle.hw_r_cle_ob)
      | wObRGle _ hw_ob_r_gle_cases =>
        cases hw_ob_r_gle_cases with
        | sameCluster _ hw_ob_cases =>
          -- Same cluster, CLE_w OB CLE_r from GleOrCle.cases
          exact .ob (by
            rw [← show h.w_lin = lin e₁ from Subsingleton.elim _ _,
                ← show h.r_lin = lin e₂ from Subsingleton.elim _ _]
            exact hw_ob_cases.hw_r_cle_ob)
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Different cluster: extract wObRDown from diffCache.case sub-cases
          have hw₁ : h.w_lin = lin e₁ := Subsingleton.elim _ _
          have hw₂ : h.r_lin = lin e₂ := Subsingleton.elim _ _
          -- Helper: given encapDir + wObRDown → StepOrdering.obEncap
          have from_encap_wob
              (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_lin)
              (hwOB : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                hdown.existsRClusterDirDown.choose) :
              @StepOrdering n (lin e₁).hreq's_dir_access.choose
                (lin e₂).hreq's_dir_access.choose := by
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.2.2
            exact .obEncap hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwOB)
              (by rw [← hw₂]; cases hencap_rel with
                  | cleEncap henc => exact henc
                  | gcacheEncap henc _ => sorry)
          -- Dispatch all diffCache.case sub-cases
          cases hdiff_cache_case with
          | wHasPermsAfter _ coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle =>
                exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
              | diffCluster _ _ hwOB => exact from_encap_wob hPDC.encapDir hwOB
            | notImmPred hasPermsCase =>
              cases hasPermsCase with
              | noEvictBetween w =>
                sorry -- needs dir_ordered chain for wObRDown
              | evictBetween evict =>
                exact from_encap_wob evict.encapProxyAndDir evict.evictBetween.wObRDown
          | wNoPermsAfter _ _ rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
          | wCleAfter rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
    | co h =>
      -- co: extract from co.ordering
      cases h.comm with
      | sameCache _ cache_ob =>
        -- Same cache: e₁ OB e₂. Both inside same CLE.
        sorry -- encapObEncap with e₁, e₂ inside shared CLE
      | sameClusDiffCache _ cle_ord =>
        -- Same cluster, diff cache: CLE ordering from cleOrdering.Cases
        have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
        have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
        cases cle_ord with
        | wImmPredRCle w =>
          cases w with
          | sameCluster _ hob =>
            -- CLE₁ OB CLE₂ directly
            exact .ob (by rw [← hw₁, ← hw₂]; exact hob)
          | diffCluster _ hdown hwObRDown =>
            -- CLE₁ OB e_r_cdir_down, e_r_cdir_down EncapBy CLE₂
            -- = obEncap
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.2.2
            exact .obEncap hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwObRDown)
              (by rw [← hw₂]; cases hencap_rel with
                  | cleEncap henc => exact henc
                  | gcacheEncap henc _ => sorry) -- gcacheEncap gives GCR encaps, not CLE encaps
        | evictOrReadBetweenWAndRCleSameCluster evict =>
          -- CLE₁ OB CLE₂ from wObR
          exact .ob (by rw [← hw₁, ← hw₂]; exact evict.wObR)
      | diffClus _ diff_cluster_cases =>
        -- Different cluster: downgrade chain via wObRDown + encapDirRelation
        have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
        have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
        cases diff_cluster_cases with
        | wCleImmPredDown w =>
          -- wObRDown: CLE₁ OB e_r_cdir_down
          -- encapDirRelation: e_r_cdir_down EncapBy CLE₂
          have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hencap_rel := hcdir_spec.2.2.2
          exact .obEncap w.rDown.encapDir.existsRClusterDirDown.choose
            (by rw [← hw₁]; exact w.wObRDown)
            (by rw [← hw₂]; cases hencap_rel with
                | cleEncap henc => exact henc
                | gcacheEncap henc _ => sorry)
        | evictOrReadBetweenWAndRDown evict =>
          have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hencap_rel := hcdir_spec.2.2.2
          exact .obEncap evict.rDown.encapDir.existsRClusterDirDown.choose
            (by rw [← hw₁]; exact evict.wObRDown)
            (by rw [← hw₂]; cases hencap_rel with
                | cleEncap henc => exact henc
                | gcacheEncap henc _ => sorry)
    | fr h =>
      -- fr: rf⁻¹;co⁺ composition
      sorry

-- Old lex pair approach (co_step_advances, co_chain_cle_advance, step_advances,
-- transgen_lex_advance) removed. Using StepOrdering instead.
-- Placeholder to mark where old code was:
/-- Acyclicity given that every event has a linearization.
    Chains `step_to_ordering` through TransGen via `StepOrdering.trans`,
    then `StepOrdering.irrefl` gives the contradiction. -/
theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  suffices ∀ a c, Relation.TransGen (PPOi ∪ com compound b init) a c →
      StepOrdering (hknow a).hreq's_dir_access.choose (hknow c).hreq's_dir_access.choose by
    exact StepOrdering.irrefl (this e e hcycle)
  intro a c hpath
  induction hpath with
  | single h => exact step_to_ordering h hknow
  | tail _ h ih => exact StepOrdering.trans ih (step_to_ordering h hknow)

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
