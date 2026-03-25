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
  /-- OB to intermediate, intermediate finishes before target lin point.
      Weaker than EncapsulatedBy — only requires oEnd < l₂.oEnd, not oStart constraint.
      Sufficient for irrefl (l.oEnd < p.oStart ≤ p.oEnd < l.oEnd) and trans. -/
  | obEndLt (p : Event n) (h_ob : l₁.OrderedBefore n p) (h_lt : Event.oEnd n p < Event.oEnd n l₂)
      : StepOrdering l₁ l₂
  /-- Same linearization point: cache events advance but CLE stays. -/
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
    | obEndLt p hp hlt => exact .obEndLt p (Trans.trans h₁ hp) hlt
    | sameLin _ _ heq _ _ _ => subst heq; exact .ob h₁
  | obEndLt q hq hqlt =>
    -- q.oEnd < l₂.oEnd. Cases on h₂₃:
    cases h₂₃ with
    | ob h₂ =>
      -- q.oEnd < l₂.oEnd (hqlt), l₂.oEnd < l₃.oStart (h₂) → q OB l₃
      have hq_ob_l₃ : q.OrderedBefore n l₃ := Nat.lt_trans hqlt h₂
      exact .ob (Trans.trans hq hq_ob_l₃)
    | obEndLt p hp hlt =>
      -- q.oEnd < l₂.oEnd (hqlt), l₂.oEnd < p.oStart (hp) → q OB p
      have hq_ob_p : q.OrderedBefore n p := Nat.lt_trans hqlt hp
      exact .obEndLt p (Trans.trans hq hq_ob_p) hlt
    | sameLin _ _ heq _ _ _ => subst heq; exact .obEndLt q hq hqlt
  | sameLin e₁' e₂' heq he₁ hob he₂ =>
    subst heq; exact h₂₃

/-- StepOrdering is irreflexive. -/
theorem StepOrdering.irrefl {l : Event n} (h : StepOrdering l l) : False := by
  cases h with
  | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
  | obEndLt p hp hlt =>
    -- l OB p: l.oEnd < p.oStart. p.oEnd < l.oEnd.
    -- Chain: l.oEnd < p.oStart ≤ p.oEnd < l.oEnd → contradiction
    exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans hp (Event.oWellFormed n p)) hlt)
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
          -- Helper: given encapDir + wObRDown → StepOrdering.obEncap
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
                      -- Construct obEndLt directly on the matched terms
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
                      | orderAfterDir _ _ _ _ =>
                        -- nc.weak with wHasPermsAfter: contradiction
                        -- wHasPermsAfter means coherent perms, but orderAfterDir is nc.weak
                        sorry
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
      | sameCache same_cle cache_ob =>
        -- Same CLE (same_cle), e₁ OB e₂ (cache_ob). Produce .sameLin.
        have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
        have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
        have hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose := by
          rw [← hw₁, ← hw₂]; exact same_cle
        -- Need: CLE inside e₁ (EncapsulatedBy) and CLE inside e₂
        -- From dirAccessOfRequest encapDir: e encapsulates CLE → CLE EncapsulatedBy e
        -- For orderBeforeDir/orderAfterDir: CLE is not inside the event directly
        -- Use .sameLin with e₁, e₂ as the encapsulating events
        sorry
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
            exact .obEndLt hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwObRDown)
              (by rw [← hw₂]; cases hencap_rel with
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
          have hencap_rel := hcdir_spec.2.2.2
          exact .obEndLt w.rDown.encapDir.existsRClusterDirDown.choose
            (by rw [← hw₁]; exact w.wObRDown)
            (by rw [← hw₂]; cases hencap_rel with
                | cleEncap henc => exact henc.right
                | gcacheEncap _ hlt => exact hlt)
        | evictOrReadBetweenWAndRDown evict =>
          have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hencap_rel := hcdir_spec.2.2.2
          exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose
            (by rw [← hw₁]; exact evict.wObRDown)
            (by rw [← hw₂]; cases hencap_rel with
                | cleEncap henc => exact henc.right
                | gcacheEncap _ hlt => exact hlt)
    | fr h =>
      -- fr: rf⁻¹;co⁺ composition.
      -- Strategy: dir_ordered on CLE₁ and CLE₂ gives CLE₁ OB CLE₂ or CLE₂ OB CLE₁.
      -- CLE₁ OB CLE₂ → .ob. CLE₂ OB CLE₁ → exfalso via NoInterveningWrites.
      have hw₁ : h.e₁_lin = lin e₁ := Subsingleton.elim _ _
      have hw₂ : h.e₂_lin = lin e₂ := Subsingleton.elim _ _
      have hdir₁ := h.e₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      have hdir₂ := h.e₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      match hfc₁ : h.e₁_lin.hreq's_dir_access.choose, hdir₁ with
      | .directoryEvent de₁, _ =>
        match hfc₂ : h.e₂_lin.hreq's_dir_access.choose, hdir₂ with
        | .directoryEvent de₂, _ =>
          cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
          | inl hob =>
            -- CLE₁ OB CLE₂: de₁.oEnd < de₂.oStart → .ob
            exact .ob hob
          | inr hob =>
            -- CLE₂ OB CLE₁: derive contradiction via NoInterveningWrites.
            exfalso
            obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain⟩ := h.comm
            -- Apply NoInterveningWrites to e₂
            have hlin := fun e => h.hknow_dir_access compound b init e
            have h_constraints := h_no_between e₂ h.in_b₂
              h.cache₂ h.write h.notDown₂ (hlin e₂)
            -- notBetweenGles: GLE₂ not between GLE_w and GLE₁ (unconditional)
            have h_nbg := h_constraints.notBetweenGles
            -- Get GLE directory events
            have hgle₂_eq : hlin e₂ = h.e₂_lin := Subsingleton.elim _ _
            have hglew_eq : e_w_lin = hlin e_w := Subsingleton.elim _ _
            have hgdir₂ := (hlin e₂).hreq's_global_lin.choose_spec.2.isDirEvent
            have hgdir_w := e_w_lin.hreq's_global_lin.choose_spec.2.isDirEvent
            have hgdir₁ := h.e₁_lin.hreq's_global_lin.choose_spec.2.isDirEvent
            match hgc₂ : (hlin e₂).hreq's_global_lin.choose, hgdir₂ with
            | .directoryEvent ge₂, _ =>
              match hgcw : e_w_lin.hreq's_global_lin.choose, hgdir_w with
              | .directoryEvent ge_w, _ =>
                match hgc₁ : h.e₁_lin.hreq's_global_lin.choose, hgdir₁ with
                | .directoryEvent ge₁, _ =>
                  -- dir_ordered on GLEs to check if GLE₂ is between GLE_w and GLE₁
                  cases (b.orderedAtEntry.dir_ordered ge_w ge₂).ordered with
                  | inl hgle_w₂ =>
                    cases (b.orderedAtEntry.dir_ordered ge₂ ge₁).ordered with
                    | inl hgle_₂₁ =>
                      -- GLE₂ between GLE_w and GLE₁ → notBetweenGles gives False
                      exact h_nbg ⟨by
                        simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                          hgle₂_eq, hgc₂, hglew_eq, hgcw]; exact hgle_w₂, by
                        simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                          hgle₂_eq, hgc₂, hgc₁]; exact hgle_₂₁⟩
                    | inr hgle_₁₂ =>
                      -- GLE₁ OB GLE₂: use notBetweenCles (sameProtocol case)
                      -- or derive temporal contradiction from RF evidence
                      sorry
                  | inr hgle_₂w =>
                    -- GLE₂ OB GLE_w: use RF GLE evidence to derive contradiction
                    sorry
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh

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
