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

/-- Every edge in PPOi ∪ com strictly advances the lexicographic pair
    (CLE(e).oEnd, e.oEnd), tracking BOTH directory event AND cache event
    end times simultaneously.

    Primary: CLE.oEnd (directory event end time) — advances for COM edges
    and most PPOi edges (directory events are totally ordered by dir_ordered).
    Secondary: e.oEnd (cache event end time) — advances when CLEs are equal
    (from PPOi OB or co.sameGle.sameCle OB).

    Each cluster's cache and directory events are totally ordered
    (cache_ordered, dir_ordered). The lex pair (CLE.oEnd, e.oEnd) is
    strictly increasing along any path → cycle gives contradiction. -/
theorem step_advances
    (h : (@PPOi n b ∪ com compound b init) e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : (h₁_lin.hreq's_dir_access.choose.oEnd < h₂_lin.hreq's_dir_access.choose.oEnd) ∨
      (h₁_lin.hreq's_dir_access.choose.oEnd = h₂_lin.hreq's_dir_access.choose.oEnd ∧
       Event.oEnd n e₁ < Event.oEnd n e₂) := by
  cases h with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ on same cache, same address.
    -- Case split: CLE₁ = CLE₂ (secondary advances) or CLE₁ ≠ CLE₂ (use dir_ordered).
    by_cases hcle_eq : h₁_lin.hreq's_dir_access.choose = h₂_lin.hreq's_dir_access.choose
    · -- CLE₁ = CLE₂: secondary advances (same CLE.oEnd + e₁ OB e₂)
      exact Or.inr ⟨congrArg (Event.oEnd n) hcle_eq,
        Nat.lt_trans hppoi.orderedBefore (Event.oWellFormed n e₂)⟩
    · -- CLE₁ ≠ CLE₂: dir_ordered gives total ordering on directory events
      left
      have hdir₁ := h₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      have hdir₂ := h₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      match hc₁ : h₁_lin.hreq's_dir_access.choose, hdir₁ with
      | .directoryEvent de₁, _ =>
        match hc₂ : h₂_lin.hreq's_dir_access.choose, hdir₂ with
        | .directoryEvent de₂, _ =>
          simp only [Event.oEnd, hc₁, hc₂]
          cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
          | inl hob =>
            -- CLE₁ OB CLE₂ → CLE₁.oEnd < CLE₂.oStart < CLE₂.oEnd
            exact Nat.lt_trans hob de₂.oWellFormed
          | inr hob =>
            -- CLE₂ OB CLE₁ (de₂.oEnd < de₁.oStart) → derive False
            -- Key chain: for non-orderAfterDir e₁, de₁.oEnd ≤ e₁.oEnd < e₂.oStart.
            -- For encapDir/orderAfterDir e₂, e₂.oStart < de₂.oStart or e₂.oEnd < de₂.oStart.
            -- This gives de₂.oEnd < de₁.oStart ≤ de₁.oEnd < ... < de₂.oEnd → contradiction.
            exfalso
            have he₁_ob_e₂ := hppoi.orderedBefore -- e₁.oEnd < e₂.oStart
            have hda₂ := h₂_lin.hreq's_dir_access.choose_spec.2
            -- de₂.oEnd < de₁.oStart from hob (DirectoryEvent.OrderedBefore)
            -- de₁.oStart < de₁.oEnd from well-formedness
            have hde₂_lt_de₁ : de₂.oEnd < de₁.oEnd :=
              Nat.lt_trans hob de₁.oWellFormed
            -- Case split on e₂'s dirAccessOfRequest to bound de₂ vs e₂
            rw [hc₂] at hda₂
            cases hda₂ with
            | encapDir _ hencap₂ =>
              -- e₂ encapsulates CLE₂: e₂.oStart < de₂.oStart, de₂.oEnd < e₂.oEnd
              -- Chain: de₂.oEnd < de₁.oStart ≤ de₁.oEnd ≤ e₁.oEnd < e₂.oStart < de₂.oStart < de₂.oEnd
              have hda₁ := h₁_lin.hreq's_dir_access.choose_spec.2
              rw [hc₁] at hda₁
              cases hda₁ with
              | encapDir _ hencap₁ =>
                -- de₁ inside e₁: de₁.oEnd < e₁.oEnd
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < e₁.oEnd := hencap₁.reqEncapDir.right
                    _ < e₂.oStart := he₁_ob_e₂
                    _ < de₂.oStart := hencap₂.reqEncapDir.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderBeforeDir _ hexists_pred₁ hpred₁ _ _ _ _ _ =>
                -- de₁ inside predecessor, predecessor OB e₁
                -- Chain: de₂ < de₁ < pred < e₁ < e₂ < de₂ → contradiction
                have : de₂.oEnd < de₂.oEnd :=
                  calc de₂.oEnd < de₁.oStart := hob
                    _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                    _ < hexists_pred₁.choose.oEnd := hpred₁.reqEncapDir.right
                    _ < e₁.oStart := hexists_pred₁.choose_spec.2.isImmPred.bPred.isPred
                    _ < e₁.oEnd := (Event.oWellFormed n e₁)
                    _ < e₂.oStart := he₁_ob_e₂
                    _ < de₂.oStart := hencap₂.reqEncapDir.left
                    _ < de₂.oEnd := de₂.oWellFormed
                exact Nat.lt_irrefl _ this
              | orderAfterDir _ hsucc₁ _ _ =>
                -- e₁ orderAfterDir: nc.weak, CLE₁ from successor.
                -- For PPOi, the successor should be e₂ (release), giving CLE₁ = CLE₂.
                -- But CLE₁ ≠ CLE₂ (hcle_eq) → contradiction.
                -- Requires: orderAfterDir successor = PPO successor e₂ (protocol uniqueness).
                sorry
            | orderBeforeDir _ hexists_pred₂ hpred₂ hinter₂ _ _ _ _ =>
              -- e₂ orderBeforeDir: CLE₂ (de₂) from predecessor.
              -- predecessor encapsulates de₂ and is OB e₂.
              -- Use dir_ordered on de₁ and de₂ — already in `inr hob` branch.
              -- Need: derive False from hob (de₂ OB de₁) + protocol structure.
              --
              -- The predecessor is at the same cache as e₁ (from PPOi).
              -- All intermediate events between predecessor and e₂ preserve perms.
              -- e₁ is between predecessor and e₂ (or before predecessor).
              -- If e₁ is after predecessor (predecessor OB e₁):
              --   e₁ is an intermediate → stateBeforeAndAfterAtLeast constrains e₁.
              -- This is deep protocol reasoning about permission preservation.
              sorry
            | orderAfterDir _ hsucc₂ _ _ =>
              -- e₂ orderAfterDir: e₂ OB successor, successor encapsulates de₂
              have he₂_ob_succ := hsucc₂.choose_spec.2.isImmBottomSucc.isSucc
              have hsucc_encap := hsucc₂.choose_spec.2.satisfyP.encapCorresponding.reqEncapDir
              -- Chain goes through successor: e₂.oEnd < succ.oStart < de₂.oStart < de₂.oEnd
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
              | orderAfterDir _ hsucc₁ _ _ =>
                -- Both e₁ and e₂ orderAfterDir: both nc.weak.
                -- CLE₁ from e₁'s successor, CLE₂ from e₂'s successor.
                -- For PPOi nc.weak → release: successor = release = e₂.
                -- CLE₁ = CLE₂ (both from e₂'s dir event) → contradicts hcle_eq.
                -- Requires: orderAfterDir successor = PPO successor (protocol uniqueness).
                sorry
        | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
      | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
  | inr hcom =>
    -- COM: same-address communication edge. CLE ordering from structure.
    cases hcom with
    | rfe h =>
      -- rfe: GLE₁ OB GLE₂ → CLE₁.oEnd < CLE₂.oEnd (primary advances)
      left
      have hw₁ : h.w_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.r_lin = h₂_lin := Subsingleton.elim _ _
      rw [← hw₁, ← hw₂]
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster _ =>
        -- Same GLE implies same cluster → contradicts diffProtocol
        exact absurd hwr_same_cluster h.diffProtocol
      | wObRGle _ hw_ob_r_gle_cases =>
        -- GLE₁ OB GLE₂ with sub-cases
        cases hw_ob_r_gle_cases with
        | sameCluster hSameCluster _ =>
          -- Same cluster contradicts rfe's diffProtocol
          exact absurd hSameCluster h.diffProtocol
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Different cluster: CLE₁ ≠ CLE₂. Use dir_ordered.
          have hdir₁ := h.w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
          have hdir₂ := h.r_lin.hreq's_dir_access.choose_spec.2.isDirEvent
          match hc₁ : h.w_lin.hreq's_dir_access.choose, hdir₁ with
          | .directoryEvent de₁, _ =>
            match hc₂ : h.r_lin.hreq's_dir_access.choose, hdir₂ with
            | .directoryEvent de₂, _ =>
              simp only [Event.oEnd, hc₁, hc₂]
              cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
              | inl hob => exact Nat.lt_trans hob de₂.oWellFormed
              | inr hob =>
                -- CLE₂ OB CLE₁. Case split on diffCache.case sub-cases.
                exfalso
                have hr_eq : h.r_lin = h₂_lin := Subsingleton.elim _ _
                have hw_eq : h.w_lin = h₁_lin := Subsingleton.elim _ _
                have hcle₂_rfe : h.r_lin.hreq's_dir_access.choose = .directoryEvent de₂ := by
                  rw [hr_eq]; exact hc₂
                have hcle₁_rfe : h.w_lin.hreq's_dir_access.choose = .directoryEvent de₁ := by
                  rw [hw_eq]; exact hc₁
                -- Helper: given de₁.oEnd < t and t < de₂.oEnd → contradiction with hob
                have chain_contradiction :
                    ∀ (t : Nat), de₁.oEnd < t → t < de₂.oEnd → False := by
                  intro t h1 h2
                  have : de₁.oEnd < de₁.oEnd :=
                    calc de₁.oEnd < t := h1
                      _ < de₂.oEnd := h2
                      _ < de₁.oStart := hob
                      _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                  exact Nat.lt_irrefl _ this
                -- Helper: given encapDir + wObRDown → chain → contradiction
                have from_encapDir_ob :
                    ∀ (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_lin)
                      (hwOB : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                        hdown.existsRClusterDirDown.choose),
                    False := by
                  intro hdown hwOB
                  have hcdir_encap_rel := hdown.existsRClusterDirDown.choose_spec.2.2.2
                  have hcdir_lt : hdown.existsRClusterDirDown.choose.oEnd < de₂.oEnd := by
                    cases hcdir_encap_rel with
                    | cleEncap henc => rw [hcle₂_rfe] at henc; simp [Event.Encapsulates] at henc; exact henc.2
                    | gcacheEncap _ hlt => rw [hcle₂_rfe] at hlt; simp [Event.oEnd] at hlt; exact hlt
                  -- Convert hwOB (Event.OrderedBefore) to de₁.oEnd < cdir.oEnd
                  have hwOB_nat : de₁.oEnd < hdown.existsRClusterDirDown.choose.oEnd := by
                    have h1 := hwOB
                    simp only [Event.OrderedBefore, Event.oEnd, show h.w_lin = h₁_lin from Subsingleton.elim _ _, hc₁] at h1
                    exact Nat.lt_trans h1 (Event.oWellFormed n hdown.existsRClusterDirDown.choose)
                  exact chain_contradiction _ hwOB_nat hcdir_lt
                -- Dispatch all diffCache.case sub-cases.
                -- All paths reach rCleOrDownAtWAfterWCle.diffCluster which now carries wObRDown.
                cases hdiff_cache_case with
                | wHasPermsAfter _ coherentCase =>
                  cases coherentCase with
                  | immPred rCle hPDC =>
                    cases rCle with
                    | sameCluster hSame _ => exact absurd hSame h.diffProtocol
                    | diffCluster _ _ hwOB => exact from_encapDir_ob hPDC.encapDir hwOB
                  | notImmPred hasPermsCase =>
                    cases hasPermsCase with
                    | noEvictBetween w =>
                      -- noEvictBetween has full cache-level chain: e₁ OB e_r_down, cdirEncapsDown.
                      -- Use dir_ordered on de₁ and e_r_cdir_down to get wObRDown.
                      have hPDC := w.gdownEncapProxyAndDirAndCDown
                      have hcdir_spec' := hPDC.encapDir.existsRClusterDirDown.choose_spec
                      have hcdir_is_dir' := hcdir_spec'.2.1
                      match hcd' : hPDC.encapDir.existsRClusterDirDown.choose, hcdir_is_dir' with
                      | .directoryEvent de_cdir', _ =>
                        have hcle₁_rfe' : h.w_lin.hreq's_dir_access.choose = .directoryEvent de₁ := by
                          rw [show h.w_lin = h₁_lin from Subsingleton.elim _ _]; exact hc₁
                        cases (b.orderedAtEntry.dir_ordered de₁ de_cdir').ordered with
                        | inl hob_cdir =>
                          -- de₁ OB de_cdir': this IS the wObRDown we need
                          have hwOB' : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                              hPDC.encapDir.existsRClusterDirDown.choose := by
                            simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                              hcle₁_rfe', hcd']
                            exact hob_cdir
                          exact from_encapDir_ob hPDC.encapDir hwOB'
                        | inr hob_cdir =>
                          -- de_cdir' OB de₁: contradiction from cache-level chain.
                          -- e₁ OB e_r_down + cdirEncapsDown + e_r_cdir_down OB de₁ →
                          -- de₁.oEnd < e₁.oEnd < e_r_down.oStart ≤ e_r_down.oEnd
                          --   < e_r_cdir_down.oEnd < de₁.oStart ≤ de₁.oEnd → contradiction
                          exfalso
                          have he₁_ob_rdown := hPDC.existsRDownAtW.choose_spec.2.2.2
                          have hcdirEncaps := hPDC.cdirEncapsDown
                          -- e_r_cdir_down.oEnd < de₁.oStart (from hob_cdir, adjusting types)
                          have hcdir_before_de₁ : de_cdir'.oEnd < de₁.oStart := hob_cdir
                          -- e_r_down.oEnd < e_r_cdir_down.oEnd (from cdirEncapsDown)
                          have hrdown_lt_cdir : hPDC.existsRDownAtW.choose.oEnd <
                              hPDC.encapDir.existsRClusterDirDown.choose.oEnd := by
                            simp [Event.Encapsulates] at hcdirEncaps
                            exact hcdirEncaps.2
                          -- Chain through e₁'s dirAccessOfRequest
                          have hda₁_rfe := h₁_lin.hreq's_dir_access.choose_spec.2
                          rw [hc₁] at hda₁_rfe
                          cases hda₁_rfe with
                          | encapDir _ hencap_e₁ =>
                            have : de₁.oEnd < de₁.oEnd :=
                              calc de₁.oEnd < e₁.oEnd := hencap_e₁.reqEncapDir.right
                                _ < hPDC.existsRDownAtW.choose.oStart := he₁_ob_rdown
                                _ ≤ hPDC.existsRDownAtW.choose.oEnd :=
                                    Nat.le_of_lt (Event.oWellFormed n _)
                                _ < de_cdir'.oEnd := by
                                    simp [Event.oEnd, hcd'] at hrdown_lt_cdir; exact hrdown_lt_cdir
                                _ < de₁.oStart := hcdir_before_de₁
                                _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                            exact Nat.lt_irrefl _ this
                          | orderBeforeDir _ hexists_pred hpred _ _ _ _ _ =>
                            have : de₁.oEnd < de₁.oEnd :=
                              calc de₁.oEnd < hexists_pred.choose.oEnd := hpred.reqEncapDir.right
                                _ < e₁.oStart := hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                                _ < e₁.oEnd := Event.oWellFormed n e₁
                                _ < hPDC.existsRDownAtW.choose.oStart := he₁_ob_rdown
                                _ ≤ hPDC.existsRDownAtW.choose.oEnd :=
                                    Nat.le_of_lt (Event.oWellFormed n _)
                                _ < de_cdir'.oEnd := by
                                    simp [Event.oEnd, hcd'] at hrdown_lt_cdir; exact hrdown_lt_cdir
                                _ < de₁.oStart := hcdir_before_de₁
                                _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                            exact Nat.lt_irrefl _ this
                          | orderAfterDir _ _ _ _ =>
                            -- e₁ orderAfterDir (nc.weak) with rfe wHasPermsAfter:
                            -- wHasPermsAfter requires coherent write perms (SW).
                            -- nc.weak is non-coherent → contradiction with wHasPermsAfter.
                            sorry
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                    | evictBetween evict =>
                      exact from_encapDir_ob evict.encapProxyAndDir evict.evictBetween.wObRDown
                | wNoPermsAfter _ _ rCle =>
                  cases rCle with
                  | sameCluster hSame _ => exact absurd hSame h.diffProtocol
                  | diffCluster _ hdown hwOB => exact from_encapDir_ob hdown hwOB
                | wCleAfter rCle =>
                  cases rCle with
                  | sameCluster hSame _ => exact absurd hSame h.diffProtocol
                  | diffCluster _ hdown hwOB => exact from_encapDir_ob hdown hwOB
            | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
          | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
    | co h =>
      -- co: case split on co.cases
      have hw₁ : h.w₁_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.w₂_lin = h₂_lin := Subsingleton.elim _ _
      cases h.ordering with
      | sameGle gle_eq cle_cases =>
        cases cle_cases with
        | sameCle cle_eq cache_ob =>
          -- Same CLE + e₁ OB e₂ → secondary advances
          right
          constructor
          · -- CLE₁.oEnd = CLE₂.oEnd (from CLE₁ = CLE₂)
            rw [← hw₁, ← hw₂]; exact congrArg (Event.oEnd n) cle_eq
          · -- e₁.oEnd < e₂.oEnd from OB
            exact Nat.lt_trans cache_ob (Event.oWellFormed n e₂)
        | diffCle cle_ord =>
          -- Different CLEs → CLE ordering → primary advances
          left
          cases cle_ord with
          | wImmPredRCle w =>
            cases w with
            | sameCluster _ hob =>
              -- CLE₁ OB CLE₂ directly
              rw [← hw₁, ← hw₂]
              exact Nat.lt_trans hob (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
            | diffCluster hdiff hdown hwObRDown =>
              -- CLE₁ OB e_r_cdir_down (from wObRDown) + e_r_cdir_down.oEnd < CLE₂.oEnd
              -- Chain: CLE₁ → e_r_cdir_down → CLE₂ gives CLE₁.oEnd < CLE₂.oEnd
              rw [← hw₁, ← hw₂]
              have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
              have hcdir_encap_rel := hcdir_spec.2.2.2
              have hcle₂_eq : h.w₂_lin.hreq's_dir_access.choose = h₂_lin.hreq's_dir_access.choose := by
                rw [hw₂]
              have hcdir_lt : hdown.existsRClusterDirDown.choose.oEnd <
                  h.w₂_lin.hreq's_dir_access.choose.oEnd := by
                cases hcdir_encap_rel with
                | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
                | gcacheEncap _ hlt => exact hlt
              exact Nat.lt_trans (Nat.lt_trans hwObRDown
                (Event.oWellFormed n hdown.existsRClusterDirDown.choose)) hcdir_lt
          | evictOrReadBetweenWAndRCleSameCluster evict =>
            -- wObR: CLE₁ OB CLE₂
            rw [← hw₁, ← hw₂]
            exact Nat.lt_trans evict.wObR (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
      | wObRGle gle_ob cle_cases =>
        -- GLE₁ OB GLE₂ with CLE sub-cases
        left
        rw [← hw₁, ← hw₂]
        cases cle_cases with
        | sameCluster same_cluster same_cluster_cases =>
          -- Same cluster: reuse sameGle.diffCle logic
          cases same_cluster_cases with
          | wImmPredRCle w =>
            cases w with
            | sameCluster _ hob =>
              exact Nat.lt_trans hob (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
            | diffCluster hdiff hdown =>
              -- Vacuous: sameCluster (e_w.protocol = e_r.protocol) contradicts
              -- diffCluster (e_w.protocol ≠ e_r.protocol)
              exact absurd same_cluster hdiff
          | evictOrReadBetweenWAndRCleSameCluster evict =>
            exact Nat.lt_trans evict.wObR (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
        | diffCluster diff_cluster diff_cluster_cases =>
          -- Different cluster: both sub-cases carry wObRDown + encapDirRelation
          cases diff_cluster_cases with
          | wCleImmPredDown w =>
            -- wObRDown: CLE₁ OB e_r_cdir_down → CLE₁.oEnd < e_r_cdir_down.oStart
            -- encapDirRelation: e_r_cdir_down.oEnd < CLE₂.oEnd
            have hob := w.wObRDown  -- CLE₁ OB e_r_cdir_down
            have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.2.2
            have hcdir_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd
                < h.w₂_lin.hreq's_dir_access.choose.oEnd := by
              cases hencap_rel with
              | cleEncap henc =>
                simp [Event.Encapsulates] at henc
                exact henc.2
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
              | cleEncap henc =>
                simp [Event.Encapsulates] at henc
                exact henc.2
              | gcacheEncap _ hlt => exact hlt
            exact Nat.lt_trans (Nat.lt_trans hob
              (Event.oWellFormed n evict.rDown.encapDir.existsRClusterDirDown.choose)) hcdir_lt
    | fr h =>
      -- fr: same address. CLE ordering from dir_ordered.
      have hw₁ : h.e₁_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.e₂_lin = h₂_lin := Subsingleton.elim _ _
      have hdir₁ := h.e₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      have hdir₂ := h.e₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      rw [← hw₁, ← hw₂]
      match hc₁ : h.e₁_lin.hreq's_dir_access.choose, hdir₁ with
      | .directoryEvent de₁, _ =>
        match hc₂ : h.e₂_lin.hreq's_dir_access.choose, hdir₂ with
        | .directoryEvent de₂, _ =>
          -- dir_ordered gives total ordering on CLEs (same address in model)
          have hordered := b.orderedAtEntry.dir_ordered de₁ de₂
          by_cases hde_eq : de₁ = de₂
          · -- Same DirectoryEvent: dir_ordered on equal events gives False
            -- (de.oEnd < de.oStart from Ordered contradicts de.oWellFormed)
            exfalso
            rw [hde_eq] at hordered
            cases hordered.ordered with
            | inl h => exact Nat.lt_asymm de₂.oWellFormed h
            | inr h => exact Nat.lt_asymm de₂.oWellFormed h
          · -- Different CLEs: dir_ordered gives ordering
            left
            simp only [Event.oEnd, hc₁, hc₂]
            cases hordered.ordered with
            | inl hob => exact Nat.lt_trans hob de₂.oWellFormed
            | inr hob =>
              -- CLE₂ OB CLE₁ with fr → protocol impossibility
              sorry
        | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
      | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h

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
