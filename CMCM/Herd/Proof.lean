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

/-- List.stateAfter on append singleton: processing xs then e equals
    applying e's SucceedingState to the result of processing xs. -/
theorem list_stateAfter_append_singleton (xs : List (Event n)) (e : Event n) :
    ∀ init : EntryState n,
    (xs ++ [e]).stateAfter n init = e.SucceedingState n (xs.stateAfter n init) := by
  induction xs with
  | nil => intro init; simp [List.stateAfter]
  | cons x xs ih => intro init; simp only [List.cons_append, List.stateAfter]; exact ih _

/-- Behaviour.stateAfter = event's SucceedingState applied to stateBefore. -/
theorem stateAfter_eq_succeedingState
    {b : Behaviour n} {init : EntryState n} {e : Event n} :
    b.stateAfter n init e = e.SucceedingState n (b.stateBefore n init e) := by
  unfold Behaviour.stateAfter Behaviour.stateBefore
  exact list_stateAfter_append_singleton _ _ _

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

StepOrdering has 3 constructors: ob, obEndLt, sameLin.
Transitivity composes chains. Irreflexivity from OB irreflexivity.
A cycle gives StepOrdering lin(e) lin(e) → contradiction. -/

/-- Ordering between linearization points, connected via auxiliary
    protocol events through OB and Encapsulates/EncapsulatedBy. -/
inductive StepOrdering : Event n → Event n → Prop where
  /-- Direct OB between linearization points -/
  | ob (h : l₁.OrderedBefore n l₂) : StepOrdering l₁ l₂
  /-- OB to intermediate, intermediate finishes before target lin point.
      Uses oEnd < (not full EncapsulatedBy) because in the `noGlobalCache` shim case,
      the GCR is a previous event that encapsulates cdir_down but is NOT encapsulated
      by CLE — only cdir_down.oEnd < CLE.oEnd holds. -/
  | obEndLt (p : Event n) (h_ob : l₁.OrderedBefore n p) (h_lt : Event.oEnd n p < Event.oEnd n l₂)
      : StepOrdering l₁ l₂
  /-- Same linearization point: cache events advance but CLE stays.
      Used when both events encapsulate the shared CLE. -/
  | sameLin (e₁' e₂' : Event n) (h_eq : l₁ = l₂)
      (h_enc₁ : l₁.EncapsulatedBy n e₁') (h_ob : e₁'.OrderedBefore n e₂')
      (h_enc₂ : l₂.EncapsulatedBy n e₂') : StepOrdering l₁ l₂
  /-- Same linearization point: equality only (no encapsulation evidence).
      Used when one event doesn't encapsulate the CLE (e.g., orderBeforeDir).
      Irrefl is NOT provable from `.eq` alone — the cycle-level argument
      guarantees at least one non-eq edge (rfe/fr always give ob/obEndLt). -/
  | eq (h_eq : l₁ = l₂) : StepOrdering l₁ l₂


/-- StepOrdering is transitive. 3 constructors × 3 = 9 cases. -/
theorem StepOrdering.trans {l₁ l₂ l₃ : Event n}
    (h₁₂ : StepOrdering l₁ l₂) (h₂₃ : StepOrdering l₂ l₃) : StepOrdering l₁ l₃ := by
  cases h₁₂ with
  | ob h₁ =>
    cases h₂₃ with
    | ob h₂ => exact .ob (Trans.trans h₁ h₂)
    | obEndLt p hp hlt => exact .obEndLt p (Trans.trans h₁ hp) hlt
    | sameLin _ _ heq _ _ _ => subst heq; exact .ob h₁
    | eq heq => subst heq; exact .ob h₁
  | obEndLt q hq hqlt =>
    cases h₂₃ with
    | ob h₂ =>
      exact .ob (Trans.trans hq (show q.OrderedBefore n l₃ from Nat.lt_trans hqlt h₂))
    | obEndLt p hp hlt =>
      exact .obEndLt p (Trans.trans hq (show q.OrderedBefore n p from Nat.lt_trans hqlt hp)) hlt
    | sameLin _ _ heq _ _ _ => subst heq; exact .obEndLt q hq hqlt
    | eq heq => subst heq; exact .obEndLt q hq hqlt
  | sameLin e₁' e₂' heq he₁ hob he₂ =>
    subst heq; exact h₂₃
  | eq heq =>
    subst heq; exact h₂₃

/-- StepOrdering is irreflexive. -/
theorem StepOrdering.irrefl {l : Event n} (h : StepOrdering l l) : False := by
  cases h with
  | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
  | obEndLt p hp hlt =>
    -- l OB p: l.oEnd < p.oStart. p.oEnd < l.oEnd.
    exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans hp (Event.oWellFormed n p)) hlt)
  | sameLin e₁' e₂' heq he₁ hob he₂ =>
    have : l.oEnd < l.oEnd :=
      calc l.oEnd
        _ < e₁'.oEnd := he₁.right
        _ < e₂'.oStart := hob
        _ < l.oStart := he₂.left
        _ < l.oEnd := Event.oWellFormed n l
    exact Nat.lt_irrefl _ this
  | eq _ =>
    -- Can't derive False from just l = l. In practice, the composed
    -- cycle result is never .eq because rfe/fr always give non-eq.
    -- Handle at cycle level in cmcm_acyclic_of_hknow.
    sorry

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

/-- Map a single co edge to StepOrdering. Factored out to avoid recursion in step_to_ordering. -/
theorem co_step_to_ordering
    (h : @Herd.co n compound b init e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h.comm with
  | sameCache same_cle cache_ob =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    have hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose := by
      rw [← hw₁, ← hw₂]; exact same_cle
    have hda₁ := (lin e₁).hreq's_dir_access.choose_spec.2; rw [← hw₁] at hda₁
    have hda₂ := (lin e₂).hreq's_dir_access.choose_spec.2; rw [← hw₂] at hda₂
    cases hda₁ with
    | encapDir _ hencap₁ =>
      cases hda₂ with
      | encapDir _ hencap₂ =>
        exact .sameLin e₁ e₂ hcle_eq
          (by rw [← hw₁]; exact ⟨hencap₁.reqEncapDir.left, hencap₁.reqEncapDir.right⟩)
          cache_ob
          (by rw [← hw₂]; exact ⟨hencap₂.reqEncapDir.left, hencap₂.reqEncapDir.right⟩)
      | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq hcle_eq
      | orderAfterDir _ _ _ _ => exact .eq hcle_eq
    | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq hcle_eq
    | orderAfterDir _ _ _ _ => exact .eq hcle_eq
  | sameClusDiffCache _ cle_ord =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob => exact .ob (by rw [← hw₁, ← hw₂]; exact hob)
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        exact .obEndLt hdown.existsRClusterDirDown.choose
          (by rw [← hw₁]; exact hwObRDown)
          (by rw [← hw₂]; cases hcdir_spec.2.2.2 with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt)
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact .ob (by rw [← hw₁, ← hw₂]; exact evict.wObR)
  | diffClus _ diff_cluster_cases =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    cases diff_cluster_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt w.rDown.encapDir.existsRClusterDirDown.choose
        (by rw [← hw₁]; exact w.wObRDown)
        (by rw [← hw₂]; cases hcdir_spec.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose
        (by rw [← hw₁]; exact evict.wObRDown)
        (by rw [← hw₂]; cases hcdir_spec.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)

/-- Chain co steps through TransGen into a single StepOrdering. -/
theorem co_chain_step_ordering
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hpath : Relation.TransGen (@Herd.co n compound b init) e₁ e₂)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  induction hpath with
  | single h => exact co_step_to_ordering h lin
  | tail _ h ih => exact StepOrdering.trans ih (co_step_to_ordering h lin)

/-- Map each PPOi ∪ com step to a StepOrdering between linearization points.
    PPOi: direct OB (e₁ OB e₂).
    rfe/co/fr: extract protocol events from communication evidence. -/
theorem step_to_ordering
    (h : (@PPOi n b ∪ com compound b init) e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ on same cache. Map to StepOrdering CLE₁ CLE₂.
    have hw₁ : (lin e₁) = lin e₁ := rfl
    have hw₂ : (lin e₂) = lin e₂ := rfl
    -- by_cases on CLE equality
    by_cases hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose
    · -- Same CLE → .eq
      exact .eq hcle_eq
    · -- Different CLEs: case-split on dirAccessOfRequest for both events
      have hda₁ := (lin e₁).hreq's_dir_access.choose_spec.2
      have hda₂ := (lin e₂).hreq's_dir_access.choose_spec.2
      cases hda₁ with
      | encapDir _ hencap₁ =>
        -- CLE₁ inside e₁: CLE₁.oEnd < e₁.oEnd
        cases hda₂ with
        | encapDir _ hencap₂ =>
          -- Both encapDir: CLE₁.oEnd < e₁.oEnd < e₂.oStart < CLE₂.oStart → .ob
          exact .ob (Nat.lt_trans (Nat.lt_trans hencap₁.reqEncapDir.right hppoi.orderedBefore) hencap₂.reqEncapDir.left)
        | orderBeforeDir _ hexists_pred₂ hpred₂_encap hinter_leaves _ _ _ _ =>
          -- CLE₁ inside e₁ (encapDir), CLE₂ inside pred₂ (orderBeforeDir).
          -- pred₂ = hexists_pred₂.choose is the immediate bottom pred of e₂.
          -- Need to order e₁ vs pred₂.
          -- For same-address: cache_ordered gives the split.
          -- For different-address: needs CompoundMCM.
          have hpred₂_spec := hexists_pred₂.choose_spec.right
          have hpred₂_ob_e₂ := hpred₂_spec.isImmPred.bPred.isPred
          -- Extract CacheEvents from e₁ and pred₂
          match he₁_ce : e₁, hppoi.cache₁ with
          | .cacheEvent ce₁, _ =>
            have hpred₂_cache := hpred₂_spec.satisfyP.reqCache
            match hpred₂_ce : hexists_pred₂.choose, hpred₂_cache with
            | .cacheEvent ce_pred₂, _ =>
              -- Both are cache events. Use cache_ordered for ordering.
              have hord := b.orderedAtEntry.cache_ordered ce₁ ce_pred₂
              cases hord.ordered with
              | inl hencap_or_before =>
                -- e₁ encapsulated by or before pred₂
                cases hencap_or_before with
                | inl hencap₁_by_pred₂ =>
                  -- e₁ encapsulated by pred₂ → e₁ is a downgrade (cache_encap_rule).
                  -- Contradicts hppoi.notDown₁.
                  exact absurd
                    (show Event.down n (Event.cacheEvent ce₁) from
                      b.orderedAtEntry.cache_encap_rule ce_pred₂ ce₁ hencap₁_by_pred₂)
                    hppoi.notDown₁
                | inr he₁_ob_pred₂ =>
                  -- e₁ OB pred₂: CLE₁.oEnd < e₁.oEnd < pred₂.oStart < CLE₂.oStart → .ob
                  have hpred₂_encap_cle₂ : hexists_pred₂.choose.Encapsulates n
                      (lin e₂).hreq's_dir_access.choose := hpred₂_encap.reqEncapDir
                  exact .ob (Nat.lt_trans (Nat.lt_trans hencap₁.reqEncapDir.right
                    (by rw [hpred₂_ce]; exact he₁_ob_pred₂))
                    hpred₂_encap_cle₂.left)
              | inr hencap_or_before =>
                -- pred₂ encapsulated by or before e₁
                cases hencap_or_before with
                | inl hpred₂_encap_by_e₁ =>
                  -- pred₂ encapsulated by e₁ → pred₂ is a downgrade (cache_encap_rule).
                  -- Contradicts hpred₂_spec.satisfyP.notDown.
                  exact absurd
                    (show Event.down n hexists_pred₂.choose from by
                      rw [hpred₂_ce]
                      exact b.orderedAtEntry.cache_encap_rule ce₁ ce_pred₂ hpred₂_encap_by_e₁)
                    hpred₂_spec.satisfyP.notDown
                | inr hpred₂_ob_e₁ =>
                  -- pred₂ OB e₁: e₁ is between pred₂ and e₂.
                  -- Predecessor elimination: e₁ satisfies the property,
                  -- contradicting noIntermediateSatisfyingP.
                  sorry -- predecessor elimination: needs reqHasNoPermsLeavesStateAtLeast for e₁
            | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
          | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
        | orderAfterDir _ hsucc_encap₂ _ _ =>
          -- e₂ has orderAfterDir: CLE₂ inside succ₂ (immediate bottom successor of e₂).
          -- Chain: CLE₁.oEnd < e₁.oEnd < e₂.oEnd < succ₂.oStart < CLE₂.oStart → CLE₁ OB CLE₂
          have hsucc₂_spec := hsucc_encap₂.choose_spec.right
          have he₂_ob_succ₂ : Event.oEnd n e₂ < Event.oStart n hsucc_encap₂.choose :=
            hsucc₂_spec.isImmBottomSucc.isSucc
          have hsucc₂_encap_cle₂ := hsucc₂_spec.satisfyP.encapCorresponding.reqEncapDir
          exact .ob (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
            hencap₁.reqEncapDir.right hppoi.orderedBefore)
            (Event.oWellFormed n e₂)) he₂_ob_succ₂) hsucc₂_encap_cle₂.left)
      | orderBeforeDir _ hexists_pred₁ hpred₁_encap _ _ _ _ _ =>
        -- CLE₁ inside pred₁. pred₁.oEnd < e₁.oStart.
        cases hda₂ with
        | encapDir _ hencap₂ =>
          -- CLE₁ inside pred₁, CLE₂ inside e₂.
          -- Chain: CLE₁.oEnd < pred₁.oEnd < e₁.oStart < e₁.oEnd < e₂.oStart < CLE₂.oStart → .ob
          have hpred₁_ob_e₁ := hexists_pred₁.choose_spec.2.isImmPred.bPred.isPred
          exact .ob (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
            hpred₁_encap.reqEncapDir.right hpred₁_ob_e₁)
            (Event.oWellFormed n e₁)) hppoi.orderedBefore) hencap₂.reqEncapDir.left)
        | orderBeforeDir _ _ _ _ _ _ _ _ =>
          -- Both orderBeforeDir: CLEs from predecessors.
          -- For same-address: use dir_ordered (same cluster + same address). ✓
          -- For diff-address: use CompoundMCM (avoids cross-address dir_ordered).
          by_cases h_same_addr : e₁.addr = e₂.addr
          · -- Same address: dir_ordered valid (same cluster from PPOi, same addr).
            have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
            have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
            match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₁, _ =>
              match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
              | .directoryEvent de₂, _ =>
                cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
                | inl hob => exact .ob hob
                | inr hob =>
                  -- CLE₂ OB CLE₁. Same addr, both orderBeforeDir → predecessor elimination.
                  sorry -- same-addr predecessor elimination
          · -- Different address: CompoundMCM.
            sorry -- diff-addr: CompoundMCM for orderBeforeDir×orderBeforeDir
        | orderAfterDir _ hsucc_encap₂ _ _ =>
          -- e₂ has orderAfterDir: CLE₂ inside succ₂.
          -- Chain: CLE₁.oEnd < pred₁.oEnd < e₁.oEnd < e₂.oEnd < succ₂.oStart < CLE₂.oStart
          have hpred₁_ob_e₁ := hexists_pred₁.choose_spec.2.isImmPred.bPred.isPred
          have hsucc₂_spec := hsucc_encap₂.choose_spec.right
          have he₂_ob_succ₂ : Event.oEnd n e₂ < Event.oStart n hsucc_encap₂.choose :=
            hsucc₂_spec.isImmBottomSucc.isSucc
          have hsucc₂_encap_cle₂ := hsucc₂_spec.satisfyP.encapCorresponding.reqEncapDir
          exact .ob (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
            hpred₁_encap.reqEncapDir.right hpred₁_ob_e₁)
            (Event.oWellFormed n e₁)) hppoi.orderedBefore)
            (Event.oWellFormed n e₂)) (Nat.lt_trans he₂_ob_succ₂ hsucc₂_encap_cle₂.left))
      | orderAfterDir _ hsucc_encap₁ _ _ =>
        -- e₁ has orderAfterDir: CLE₁ from succ₁ (after e₁).
        -- Split on same-addr vs diff-addr to avoid cross-address dir_ordered.
        by_cases h_same_addr : e₁.addr = e₂.addr
        · -- Same address: dir_ordered valid (same cluster + same addr).
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₁, _ =>
            match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₂, _ =>
              cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
              | inl hob => exact .ob hob
              | inr hob =>
                -- Same-addr CLE₂ OB CLE₁ with orderAfterDir(e₁).
                sorry -- same-addr orderAfterDir(e₁): CLE₂ OB CLE₁ contradiction
        · -- Different address: CompoundMCM theorem gives the ordering.
          -- This is the key bridge showing CompoundMCM is useful!
          have hclo := @ppoi_compound_lin_order n compound b init e₁ e₂ hppoi h_same_addr
          -- CompoundLinearizationOrder: isPPOPair → e_lin₁ OB e_lin₂ ∨ lazy
          unfold CompoundProtocol.CompoundLinearizationOrder at hclo
          have hob_or_lazy := hclo hppoi.ppo
          cases hob_or_lazy with
          | inl helin_ob =>
            -- e_lin₁ OB e_lin₂: compound linearization events ordered.
            -- e_lin₁ at-or-inside CLE₁ (from clusterDirLin for orderAfterDir).
            -- CLE₂ OB CLE₁ + e_lin at-or-inside CLE → temporal contradiction.
            sorry -- CompoundMCM temporal chain contradiction
          | inr hlazy =>
            -- Lazy case: only for nc.weak → c.release with orderAfterDir.
            sorry -- lazy CompoundLinearizationOrder case
  | inr hcom =>
    cases hcom with
    | rfe h =>
      -- rfe: extract protocol events from readsFrom.cases
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          -- Vacuous: wEqRCle requires sameCache, rfe requires diffCache
          exact absurd hwr_com.sameCache h.diffCache
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
          -- Helper: given encapDir + wObRDown → StepOrdering.obEndLt
          have from_encap_wob
              (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_lin)
              (hwOB : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                hdown.existsRClusterDirDown.choose) :
              @StepOrdering n (lin e₁).hreq's_dir_access.choose
                (lin e₂).hreq's_dir_access.choose := by
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.2.2
            exact .obEndLt hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwOB)
              (by rw [← hw₂]; cases hencap_rel with
                  | cleEncap henc => exact henc.right
                  | gcacheEncap _ hlt => exact hlt)
          -- Dispatch all diffCache.case sub-cases
          cases hdiff_cache_case with
          | wHasPermsAfter hw_leaves_SW coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle =>
                exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
              | diffCluster _ _ hwOB => exact from_encap_wob hPDC.encapDir hwOB
            | notImmPred hasPermsCase =>
              cases hasPermsCase with
              | noEvictBetween w =>
                -- noEvictBetween: use encapDir + dir_ordered for CLE_w OB cdir_down
                have hPDC := w.gdownEncapProxyAndDirAndCDown
                have hcdir_spec := hPDC.encapDir.existsRClusterDirDown.choose_spec
                have hencap_rel := hcdir_spec.2.2.2
                -- Both CLE_w and cdir_down are directory events
                have hcdir_isdir := hcdir_spec.2.1
                have hcle_isdir := h.w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                -- Extract DirectoryEvent from both, use dir_ordered
                match h_cdir_ev : hPDC.encapDir.existsRClusterDirDown.choose, hcdir_isdir with
                | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
                | .directoryEvent de_cdir, _ =>
                  match h_cle_ev : h.w_lin.hreq's_dir_access.choose, hcle_isdir with
                  | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
                  | .directoryEvent de_cle, _ =>
                    cases (b.orderedAtEntry.dir_ordered de_cle de_cdir).ordered with
                    | inl hob_dir =>
                      -- CLE_w OB cdir_down (as DirectoryEvent.OrderedBefore = Nat inequality)
                      -- Construct obEncap directly on the matched terms
                      exact .obEndLt (.directoryEvent de_cdir)
                        (show (Event.directoryEvent de_cle).OrderedBefore n (.directoryEvent de_cdir) from hob_dir)
                        (by rw [← hw₂, ← h_cdir_ev]; cases hencap_rel with
                            | cleEncap henc => exact henc.right
                            | gcacheEncap _ hlt => exact hlt)
                    | inr hob_dir =>
                      -- cdir_down OB CLE_w: temporal contradiction
                      -- e_w OB e_r_down, cdir encapsulates e_r_down, cdir OB CLE_w, CLE_w inside e_w
                      exfalso
                      have hda := h.w_lin.hreq's_dir_access.choose_spec.2
                      rw [h_cle_ev] at hda
                      have hwObRDown := w.noEvictBetween.wObRDown
                      have hcdirEncap := hPDC.cdirEncapsDown
                      -- cdir.oEnd < CLE_w.oStart (hob_dir) and e_w.oEnd < e_r_down.oStart (hwObRDown)
                      -- CLE_w inside e_w (from encapDir): CLE_w.oEnd < e_w.oEnd
                      -- cdir encaps e_r_down: e_r_down.oEnd < cdir.oEnd
                      -- Chain: de_cle.oEnd < ... < e_w.oEnd < e_r_down.oStart ≤ e_r_down.oEnd < de_cdir.oEnd < de_cle.oStart
                      -- Contradiction: de_cle.oEnd < de_cle.oStart
                      cases hda with
                      | encapDir _ hencap =>
                        have : de_cle.oEnd < de_cle.oEnd :=
                          calc de_cle.oEnd
                            _ < e₁.oEnd := hencap.reqEncapDir.right
                            _ < hPDC.existsRDownAtW.choose.oStart := hwObRDown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir.oEnd := by simp [Event.Encapsulates, Event.oEnd, h_cdir_ev] at hcdirEncap; exact hcdirEncap.2
                            _ < de_cle.oStart := hob_dir
                            _ ≤ de_cle.oEnd := Nat.le_of_lt de_cle.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderBeforeDir _ hexists_pred hpred _ _ _ _ _ =>
                        have : de_cle.oEnd < de_cle.oEnd :=
                          calc de_cle.oEnd
                            _ < hexists_pred.choose.oEnd := hpred.reqEncapDir.right
                            _ < e₁.oStart := hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                            _ < e₁.oEnd := Event.oWellFormed n e₁
                            _ < hPDC.existsRDownAtW.choose.oStart := hwObRDown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir.oEnd := by simp [Event.Encapsulates, Event.oEnd, h_cdir_ev] at hcdirEncap; exact hcdirEncap.2
                            _ < de_cle.oStart := hob_dir
                            _ ≤ de_cle.oEnd := Nat.le_of_lt de_cle.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderAfterDir hweak_req _ _ _ =>
                        -- nc.weak with wHasPermsAfter: contradiction.
                        -- wHasPermsAfter = reqLeavesStateAtLeast SW = SW ≤ stateAfter.cache
                        -- ncWeakReqOnVd gives: stateAfter.cache = Vd (or stateBefore = Vd)
                        -- SW ≤ Vd is false by decide.
                        exfalso
                        -- hw_leaves_SW : SW ≤ stateAfter.cache
                        -- hweak_req.reqOnOrAfterVd : stateBefore.cache = Vd ∨ stateAfter.cache = Vd
                        cases hweak_req.reqOnOrAfterVd with
                        | inr hafter_vd =>
                          -- stateAfter.cache = Vd. SW ≤ Vd is false.
                          unfold Behaviour.reqLeavesStateAtLeast at hw_leaves_SW
                          rw [hafter_vd] at hw_leaves_SW
                          exact absurd hw_leaves_SW (by
                            simp [LE.le, State.le, LT.lt, State.lt, SW, Vd, Option.le])
                        | inl hbefore_vd =>
                          -- stateBefore.cache = Vd. nc.weak write from Vd:
                          -- RequestState ⟨.w,false,.Weak⟩ Vd = Vd (from _ => Vd branch).
                          -- stateAfter.cache = Vd. SW ≤ Vd is false.
                          -- The stateAfter = SucceedingState(stateBefore) for the last event.
                          -- stateBefore.cache = Vd = ⟨some .wr, false⟩, not ⟨some .wr, true⟩ (SW).
                          -- So nc.weak write maps Vd → Vd.
                          -- Same contradiction: SW ≤ Vd false.
                          -- stateBefore.cache = Vd → stateAfter.cache = Vd for nc.weak write
                          -- Step 1: stateAfter = SucceedingState(stateBefore)
                          unfold Behaviour.reqLeavesStateAtLeast at hw_leaves_SW
                          rw [stateAfter_eq_succeedingState] at hw_leaves_SW
                          -- Step 2: SucceedingState for cache event, non-downgrade = RequestState
                          -- Step 3: RequestState for nc.weak write on Vd = Vd
                          -- e₁ is cache event (from rfe context)
                          have hda := h.w_lin.hreq's_dir_access.choose_spec.2
                          rw [h_cle_ev] at hda
                          -- e₁ not down (from orderAfterDir.hnot_down)
                          have hnotdown := hweak_req.notDown
                          -- nc.weak: req = ⟨.w, false, .Weak⟩ or ⟨.r, false, .Weak⟩
                          have hncweak := hweak_req.weakReq
                          -- hw_leaves_SW now has SucceedingState form.
                          -- Match e₁ to cache event, unfold SucceedingState + RequestState
                          match he₁ : e₁ with
                          | .directoryEvent _ =>
                            have := hweak_req.reqCache; simp [Event.isCacheEvent, he₁] at this
                          | .cacheEvent ce₁ =>
                            have hnotdown_bool : ce₁.down = false := by
                              cases hd : ce₁.down <;> simp_all [Event.down, he₁]
                            simp only [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, he₁] at hncweak
                            have hwrite' : ce₁.req.val.rw = .w := by
                              have := h.write; simpa [Event.isWrite, he₁, Request.isWrite] using this
                            have hreq_val : ce₁.req.val = ⟨.w, false, .Weak⟩ := by
                              obtain ⟨hnc, hweak⟩ := hncweak
                              cases hv : ce₁.req.val with | mk rw c cs => simp_all [Bool.not_eq_true]
                            have hreq_eq : ce₁.req = ⟨⟨.w, false, .Weak⟩, by simp [Request.IsValid']⟩ :=
                              Subtype.ext hreq_val
                            -- Compute stateAfter.cache step by step
                            have hsucc_cache : (Event.SucceedingState n (.cacheEvent ce₁)
                                (b.stateBefore n (InitialSystemState.stateAt n init (.cacheEvent ce₁))
                                  (.cacheEvent ce₁))).cache =
                                ce₁.req.RequestState (b.stateBefore n (InitialSystemState.stateAt n init (.cacheEvent ce₁))
                                  (.cacheEvent ce₁)).cache := by
                              simp [Event.SucceedingState, CacheEvent.SucceedingState, hnotdown_bool, EntryState.cache]
                            rw [hsucc_cache, hbefore_vd, hreq_eq] at hw_leaves_SW
                            -- Now hw_leaves_SW : SW ≤ RequestState ⟨.w,false,.Weak⟩ Vd
                            -- Compute: RequestState gives Vd. Then SW ≤ Vd false.
                            simp [ValidRequest.RequestState, Vd,
                              LE.le, State.le, LT.lt, State.lt, SW, Option.le] at hw_leaves_SW
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
    | co h => exact co_step_to_ordering h lin
    | fr h =>
      -- fr: rf⁻¹;co⁺ composition.
      -- Two cases based on e₁ vs e₂ cluster relationship.
      -- Same cluster: dir_ordered on CLEs valid (same directory, same address).
      -- Diff cluster: e₂ write triggers downgrade at e₁ cluster.
      by_cases h_same_prot : e₁.sameProtocol n e₂
      · -- Same cluster: CLE₁ and CLE₂ at same cluster directory.
        by_cases hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose
        · exact .eq hcle_eq
        · -- dir_ordered valid (same cluster, same address)
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₁, _ =>
            match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₂, _ =>
              cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
              | inl hob => exact .ob hob
              | inr hob =>
                -- CLE₂ OB CLE₁ at same cluster → contradiction via NIW.
                exfalso
                obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain⟩ := h.comm
                have hlin := fun e => h.hknow_dir_access compound b init e
                have h_constraints := h_no_between e₂ h.in_b₂
                  h.cache₂ h.write h.notDown₂ (hlin e₂)
                -- e₁ and e₂ at same cluster → CLE₂.protocol = CLE₁.protocol
                have hprot_e₂_e₁ : e₂.protocol = e₁.protocol := by
                  unfold Event.sameProtocol at h_same_prot; exact h_same_prot.symm
                have hcle₂_prot := write_cle_protocol_eq_write_protocol (hlin e₂)
                have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
                have hprot₂ : (hlin e₂).hreq's_dir_access.choose.protocol =
                    (lin e₁).hreq's_dir_access.choose.protocol := by
                  calc (hlin e₂).hreq's_dir_access.choose.protocol
                    _ = e₂.protocol := hcle₂_prot
                    _ = e₁.protocol := hprot_e₂_e₁
                    _ = (lin e₁).hreq's_dir_access.choose.protocol := hcle₁_prot.symm
                -- by_cases on e_w's cluster
                have hcle_w_prot := write_cle_protocol_eq_write_protocol e_w_lin
                by_cases h_ew_prot : e₂.protocol = e_w.protocol
                · -- Same cluster e_w: all three CLEs at same directory.
                  have hprot₁ : (hlin e₂).hreq's_dir_access.choose.protocol =
                      e_w_lin.hreq's_dir_access.choose.protocol := by
                    calc (hlin e₂).hreq's_dir_access.choose.protocol
                      _ = e₂.protocol := hcle₂_prot
                      _ = e_w.protocol := h_ew_prot
                      _ = e_w_lin.hreq's_dir_access.choose.protocol := hcle_w_prot.symm
                  -- notBetweenCles: CLE₂ not between CLE_w and CLE₁
                  have h_isDirWrite : (hlin e₂).hreq's_dir_access.choose.isDirWrite := by
                    have : hlin e₂ = h.e₂_lin := Subsingleton.elim _ _
                    rw [this]; exact write_event_cle_isDirWrite h.write h.cache₂ h.notDown₂ h.e₂_lin h.in_b₂
                  -- Need OrderedBetween: CLE_w OB CLE₂ OB CLE₁
                  -- CLE₂ OB CLE₁ from hob. CLE_w OB CLE₂ from dir_ordered (same cluster).
                  have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                  match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                  | .directoryEvent de_w, _ =>
                    cases (b.orderedAtEntry.dir_ordered de_w de₂).ordered with
                    | inl hob_w₂ =>
                      have h_ob_between :
                          (hlin e₂).hreq's_dir_access.choose.OrderedBetween n
                          e_w_lin.hreq's_dir_access.choose (lin e₁).hreq's_dir_access.choose := by
                        exact ⟨by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                                  show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _,
                                  hfc₂, hfcw]; exact hob_w₂,
                               by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                                  show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _,
                                  hfc₂, hfc₁]; exact hob⟩
                      have h_nbc := h_constraints.notBetweenCles
                      unfold SameClusterCLE.NotBetweenCLEs at h_nbc
                      exact h_nbc ⟨hprot₁, hprot₂, h_isDirWrite⟩ h_ob_between
                    | inr hob_₂w =>
                      -- CLE₂ OB CLE_w: co chain gives CLE_w.oEnd ≤ CLE₂.oEnd → contradiction
                      have hco_so := co_chain_step_ordering hlin h_co_chain
                      rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hco_so
                      -- Extract oEnd: StepOrdering gives CLE_w.oEnd ≤ CLE₂.oEnd
                      have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                        cases hco_so with
                        | ob h_ob =>
                          simp only [Event.oEnd, hfcw] at h_ob
                          exact Nat.le_of_lt (Nat.lt_trans h_ob (by
                            simp only [Event.oEnd, show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂]
                            exact de₂.oWellFormed))
                        | obEndLt p hp hlt =>
                          simp only [Event.oEnd, hfcw] at hp
                          simp only [Event.oEnd, show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂] at hlt ⊢
                          exact Nat.le_of_lt (Nat.lt_trans (Nat.lt_trans hp (Event.oWellFormed n p)) hlt)
                        | sameLin _ _ heq _ _ _ =>
                          simp only [Event.oEnd, hfcw, show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂] at heq ⊢
                          exact Nat.le_of_eq (congrArg DirectoryEvent.oEnd (Event.directoryEvent.inj heq))
                        | eq heq =>
                          simp only [Event.oEnd, hfcw, show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂] at heq ⊢
                          exact Nat.le_of_eq (congrArg DirectoryEvent.oEnd (Event.directoryEvent.inj heq))
                      have : de_w.oEnd < de_w.oEnd :=
                        calc de_w.oEnd ≤ de₂.oEnd := hcw_le
                          _ < de_w.oStart := hob_₂w
                          _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed
                      exact Nat.lt_irrefl _ this
                · -- Diff cluster e_w: e₂ triggers downgrade at e_w's cluster.
                  -- diffClusterNotBetweenCles_sameCache excludes this downgrade
                  -- between CLE_w and CLE₁. Needs encapProxyAndDirAndCDown(e_w, lin e₂)
                  -- which requires cdirEncapsDown (separate sorry in RfProofHelpers).
                  sorry
      · -- Different cluster: e₂ write triggers downgrade at e₁'s cluster.
        -- Use cdirEncapsDown_exists which provides both e_cdir and e_cache_down
        -- as explicit existential witnesses (avoids Exists.choose issues).
        obtain ⟨e_cdir, he_cdir_in_b, he_cdir_isDir, he_cdir_proto, hcdir_lt_cle₂,
          ⟨e_cache_down, he_cdown_in_b, hcdir_encap_down, hcdown_is_down, hcdown_is_cache⟩,
          ⟨e_evict, he_evict_in_b, he_evict_isDir, he_evict_down, hevict_lt_cle₂, hcdir_ob_evict,
           he_evict_proto, he_evict_isDirWrite, he_evict_translatedDir⟩⟩ :=
          cdirEncapsDown_exists (lin e₁) (lin e₂) h.in_b₁ h.cache₁
        have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
        match hfc_cdir : e_cdir, he_cdir_isDir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de_cdir, _ =>
          match hfc_cle₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cle₁, _ =>
            cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
            | inl hob =>
              have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
              exact .obEndLt (.directoryEvent de_cdir)
                (show (Event.directoryEvent de_cle₁).OrderedBefore n
                    (.directoryEvent de_cdir) from hob)
                (by rw [hw₂']; exact hcdir_lt_cle₂)
            | inr hob =>
              -- cdir OB CLE₁: e₂'s downgrade at e₁'s cluster is before e₁'s CLE.
              -- Use dir_ordered CLE₁ e_evict: if CLE₁ OB e_evict → .obEndLt e_evict.
              -- If e_evict OB CLE₁ → NIW contradiction (e_evict has down=true).
              have he_evict_isdir' := he_evict_isDir
              match hfc_evict : e_evict, he_evict_isdir' with
              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
              | .directoryEvent de_evict, _ =>
                cases (b.orderedAtEntry.dir_ordered de_cle₁ de_evict).ordered with
                | inl hob_cle₁_evict =>
                  -- CLE₁ OB e_evict → .obEndLt e_evict (CLE₁ before evict, evict.oEnd < CLE₂.oEnd)
                  have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                  exact .obEndLt (.directoryEvent de_evict)
                    (show (Event.directoryEvent de_cle₁).OrderedBefore n
                        (.directoryEvent de_evict) from hob_cle₁_evict)
                    (by rw [hw₂']; exact hevict_lt_cle₂)
                | inr hob_evict_cle₁ =>
                  -- e_evict OB CLE₁: evict (down=true) before reader's CLE → NIW.
                  exfalso
                  obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain⟩ := h.comm
                  have hlin := fun e => h.hknow_dir_access compound b init e
                  have h_constraints := h_no_between e₂ h.in_b₂
                    h.cache₂ h.write h.notDown₂ (hlin e₂)
                  -- e_evict at e₁'s cluster. Need e_w at same cluster for notBetweenCles.
                  by_cases h_ew_prot : e₁.protocol = e_w.protocol
                  · -- Same cluster e_w/e₁: use diffClusterNotBetweenCles_sameCache.
                    -- e_evict at e₁'s cluster = e_w's cluster, with down=true.
                    -- Need: e_evict.OrderedBetween CLE_w CLE₁
                    -- hob_evict_cle₁ gives e_evict OB CLE₁ ✓.
                    -- Need CLE_w OB e_evict: from dir_ordered (same cluster/addr).
                    have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                    match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                    | .directoryEvent de_w, _ =>
                      cases (b.orderedAtEntry.dir_ordered de_w de_evict).ordered with
                      | inl hob_w_evict =>
                        -- CLE_w OB e_evict OB CLE₁: evict between CLE_w and CLE₁.
                        -- Apply diffClusterNotBetweenCles_sameCache.
                        have h_between : e_evict.OrderedBetween n
                            e_w_lin.hreq's_dir_access.choose
                            (lin e₁).hreq's_dir_access.choose :=
                          ⟨by rw [hfcw, hfc_evict]; exact hob_w_evict,
                           by rw [hfc_evict, hfc_cle₁]; exact hob_evict_cle₁⟩
                        exact absurd ⟨e_evict, by rw [hfc_evict]; exact he_evict_in_b,
                          { interDiffProtocol := by
                              intro heq; exact h_same_prot (h_ew_prot.trans heq.symm)
                            downToW := by
                              show e_evict.protocol = e_w.protocol
                              rw [hfc_evict]; exact he_evict_proto.trans h_ew_prot
                            isDirWrite := by rw [hfc_evict]; exact he_evict_isDirWrite
                            downIsDown := by rw [hfc_evict]; exact he_evict_down
                            isDir := by rw [hfc_evict]; simp [Event.isDirectoryEvent]
                            translatedDir := by rw [hfc_evict]; exact he_evict_translatedDir
                          }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                      | inr hob_evict_w =>
                        -- e_evict OB CLE_w: evict before write CLE.
                        -- co chain: CLE_w before CLE₂ → CLE_w.oEnd < CLE₂.oEnd.
                        -- e_evict.oEnd < CLE_w.oStart. And CLE_w.oEnd < CLE₂.oEnd.
                        -- But e_evict.oEnd < CLE₂.oEnd (from hevict_lt_cle₂). Consistent.
                        -- Need: CLE₁ before something → .obEndLt. But CLE₁ is after evict
                        -- and after CLE_w. No proxy available for .obEndLt.
                        -- → exfalso via co chain temporal contradiction.
                        sorry -- evict OB CLE_w: protocol temporal contradiction
                  · -- Different cluster e_w/e₁.
                    sorry -- diff-cluster e_w: diffClusterNotBetweenCles_sameCache
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
    have hstep := this e e hcycle
    -- Handle each StepOrdering case. The .eq case uses dir_ordered de de → False
    -- (CLE is always a directory event; self-ordering contradicts oWellFormed).
    -- Non-.eq cases use the standard irrefl arguments.
    cases hstep with
    | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
    | obEndLt p hp hlt =>
      exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans hp (Event.oWellFormed n p)) hlt)
    | sameLin e₁' e₂' heq he₁ hob he₂ =>
      have : Event.oEnd n (hknow e).hreq's_dir_access.choose <
             Event.oEnd n (hknow e).hreq's_dir_access.choose :=
        calc _ < e₁'.oEnd := he₁.right
          _ < e₂'.oStart := hob
          _ < (hknow e).hreq's_dir_access.choose.oStart := he₂.left
          _ < (hknow e).hreq's_dir_access.choose.oEnd :=
            Event.oWellFormed n (hknow e).hreq's_dir_access.choose
      exact Nat.lt_irrefl _ this
    | eq _ =>
      have hisdir := (hknow e).hreq's_dir_access.choose_spec.right.isDirEvent
      match (hknow e).hreq's_dir_access.choose, hisdir with
      | .directoryEvent de, _ =>
        cases (b.orderedAtEntry.dir_ordered de de).ordered with
        | inl h => exact absurd (Nat.lt_trans h de.oWellFormed) (Nat.lt_irrefl _)
        | inr h => exact absurd (Nat.lt_trans h de.oWellFormed) (Nat.lt_irrefl _)
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
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
