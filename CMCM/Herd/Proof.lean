import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Proof strategy: OB chains on protocol events

Each edge (PPOi or com) gives OrderedBefore / EncapsulatedBy relationships
between specific protocol events (e_w, e_r_down, e_r_cdir_down, CLE).
A cycle chains these into a loop of strict inequalities on oEnd values:

  e₁.oEnd < e_r_down.oEnd < e_r_cdir_down.oEnd < CLE.oEnd < e₂.oEnd < ...

Since EncapsulatedBy and OrderedBefore both give strict oEnd increase,
and the chain loops back, we get X.oEnd < X.oEnd — contradiction.

This matches the protocol: each PPOi step gives e₁ OB e₂, and each
COM step gives the specific communication events (e_w OB e_r_down,
e_r_cdir_down encaps e_r_down, etc.) ordered via the protocol axioms.
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

/-! ## Main theorem: acyclicity via OB chains on protocol events

Each edge gives OrderedBefore between specific protocol events.
Both OB and EncapsulatedBy give strict oEnd increase.
A cycle creates a chain of strict inequalities on oEnd that loops. -/

/-- For PPOi: e₁ OB e₂ directly gives e₁.oEnd < e₂.oEnd.
    For COM: the communication chain (e_w OB e_r_down, EncapsulatedBy chain
    to CLE, CLE inside e₂) gives e₁.oEnd < e₂.oEnd.
    Both OB and EncapsulatedBy give strict oEnd increase:
    - OB: e₁.oEnd < e₂.oStart < e₂.oEnd
    - EncapsulatedBy: e₁.oEnd < e₂.oEnd (inner ends before outer) -/
theorem step_ordered
    (hstep : (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.oEnd n < e₂.oEnd n := by
  cases hstep with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ (same cache)
    -- e₁.oEnd < e₂.oStart (OB) < e₂.oEnd (well-formedness)
    exact Nat.lt_trans hppoi.orderedBefore (Event.oWellFormed n e₂)
  | inr hcom =>
    -- COM: the OB/EncapsulatedBy chain on protocol events gives
    -- e₁.oEnd < ... < e₂.oEnd via the communication at a common level.
    -- Each step in the chain: OB gives e₁.oEnd < e₂.oStart ≤ e₂.oEnd,
    -- EncapsulatedBy gives e₁.oEnd < e₂.oEnd (inner ends before outer).
    cases hcom with
    | rfe h =>
      -- rfe: trace protocol event chain.
      -- wObRGle.diffCluster cases carry encapProxyAndDirAndCDown or similar.
      -- Chain: e_w OB e_r_down inside e_r_cdir_down inside CLE(e_r) inside e_r.
      cases h.readsFrom with
      | wEqRGle _ hsc _ => exact absurd hsc h.diffProtocol
      | wObRGle _ hw_cases =>
        cases hw_cases with
        | sameCluster hsc _ => exact absurd hsc h.diffProtocol
        | diffCluster _ _ _ hcase =>
          cases hcase with
          | wHasPermsAfter _ hcoh =>
            cases hcoh with
            | immPred _ hpdc =>
              -- immPred: full encapProxyAndDirAndCDown chain
              have hw_ob := hpdc.existsRDownAtW.choose_spec.2.2.2
              have hdown_cdir := hpdc.cdirEncapsDown.2
              have hcdir_cle : hpdc.encapDir.existsRClusterDirDown.choose.oEnd n <
                  h.r_lin.hreq's_dir_access.choose.oEnd n := by
                cases hpdc.encapDir.existsRClusterDirDown.choose_spec.2.2.2 with
                | cleEncap henc => exact henc.2
                | gcacheEncap _ hlt => exact hlt
              have hcle_e2 : h.r_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
                cases h.r_lin.hreq's_dir_access.choose_spec.2 with
                | encapDir _ he => exact he.reqEncapDir.2
                | orderBeforeDir _ hp hd _ _ _ _ _ =>
                  exact Nat.lt_trans (Nat.lt_trans hd.reqEncapDir.2
                    hp.choose_spec.2.isImmPred.bPred.isPred) (Event.oWellFormed n e₂)
                | orderAfterDir _ _ _ _ => sorry -- nc.weak orderAfterDir
              exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
                (Nat.lt_trans hw_ob (Event.oWellFormed n _)) hdown_cdir) hcdir_cle) hcle_e2
            | notImmPred hcase =>
              cases hcase with
              | noEvictBetween w =>
                -- noEvictBetween carries gdownEncapProxyAndDirAndCDown (full chain)
                have hpdc := w.gdownEncapProxyAndDirAndCDown
                have hw_ob := hpdc.existsRDownAtW.choose_spec.2.2.2
                have hdown_cdir := hpdc.cdirEncapsDown.2
                have hcdir_cle : hpdc.encapDir.existsRClusterDirDown.choose.oEnd n <
                    h.r_lin.hreq's_dir_access.choose.oEnd n := by
                  cases hpdc.encapDir.existsRClusterDirDown.choose_spec.2.2.2 with
                  | cleEncap henc => exact henc.2
                  | gcacheEncap _ hlt => exact hlt
                have hcle_e2 : h.r_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
                  cases h.r_lin.hreq's_dir_access.choose_spec.2 with
                  | encapDir _ he => exact he.reqEncapDir.2
                  | orderBeforeDir _ hp hd _ _ _ _ _ =>
                    exact Nat.lt_trans (Nat.lt_trans hd.reqEncapDir.2
                      hp.choose_spec.2.isImmPred.bPred.isPred) (Event.oWellFormed n e₂)
                  | orderAfterDir _ _ _ _ => sorry -- nc.weak orderAfterDir
                exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
                  (Nat.lt_trans hw_ob (Event.oWellFormed n _)) hdown_cdir) hcdir_cle) hcle_e2
              | evictBetween _ => sorry -- evictBetween: CLE ordering
          | wNoPermsAfter _ _ _ => sorry -- nc write: CLE ordering
          | wCleAfter hr_cle =>
            -- wCleAfter: e_w's CLE is after e_w. e_w uses orderAfterDir.
            -- e_w.oEnd < CLE(e_w).oStart (from orderAfterDir).
            -- rCleOrDownAtWAfterWCle gives CLE ordering or encapDir.
            sorry -- needs: e_w.oEnd < CLE(e_w).oStart + CLE chain to e_r
    | co h =>
      cases h.ordering with
      | sameGle _ cle_cases =>
        cases cle_cases with
        | sameCle _ cache_ob => exact Nat.lt_trans cache_ob (Event.oWellFormed n e₂)
        | diffCle _ => sorry -- CLE ordering: needs protocol temporal argument
      | wObRGle _ cle_cases =>
        cases cle_cases with
        | sameCluster _ _ => sorry -- sameCluster: CLE ordering
        | diffCluster _ dcases =>
          -- diffCluster: ReadDowngradeAtWrite carries encapProxyAndDirAndCDown
          cases dcases with
          | wCleImmPredDown wp =>
            have hw_ob := wp.rDown.existsRDownAtW.choose_spec.2.2.2
            have hdown_cdir := wp.rDown.cdirEncapsDown.2
            have hcdir_cle : wp.rDown.encapDir.existsRClusterDirDown.choose.oEnd n <
                h.w₂_lin.hreq's_dir_access.choose.oEnd n := by
              cases wp.rDown.encapDir.existsRClusterDirDown.choose_spec.2.2.2 with
              | cleEncap henc => exact henc.2
              | gcacheEncap _ hlt => exact hlt
            have hcle_e2 : h.w₂_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
              cases h.w₂_lin.hreq's_dir_access.choose_spec.2 with
              | encapDir _ he => exact he.reqEncapDir.2
              | orderBeforeDir _ hp hd _ _ _ _ _ =>
                exact Nat.lt_trans (Nat.lt_trans hd.reqEncapDir.2
                  hp.choose_spec.2.isImmPred.bPred.isPred) (Event.oWellFormed n e₂)
              | orderAfterDir _ _ _ _ => sorry -- nc.weak orderAfterDir
            exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
              (Nat.lt_trans hw_ob (Event.oWellFormed n _)) hdown_cdir) hcdir_cle) hcle_e2
          | evictOrReadBetweenWAndRDown we =>
            have hw_ob := we.rDown.existsRDownAtW.choose_spec.2.2.2
            have hdown_cdir := we.rDown.cdirEncapsDown.2
            have hcdir_cle : we.rDown.encapDir.existsRClusterDirDown.choose.oEnd n <
                h.w₂_lin.hreq's_dir_access.choose.oEnd n := by
              cases we.rDown.encapDir.existsRClusterDirDown.choose_spec.2.2.2 with
              | cleEncap henc => exact henc.2
              | gcacheEncap _ hlt => exact hlt
            have hcle_e2 : h.w₂_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
              cases h.w₂_lin.hreq's_dir_access.choose_spec.2 with
              | encapDir _ he => exact he.reqEncapDir.2
              | orderBeforeDir _ hp hd _ _ _ _ _ =>
                exact Nat.lt_trans (Nat.lt_trans hd.reqEncapDir.2
                  hp.choose_spec.2.isImmPred.bPred.isPred) (Event.oWellFormed n e₂)
              | orderAfterDir _ _ _ _ => sorry -- nc.weak orderAfterDir
            exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
              (Nat.lt_trans hw_ob (Event.oWellFormed n _)) hdown_cdir) hcdir_cle) hcle_e2
    | fr h => sorry -- fr: rf⁻¹;co composition → e₁.oEnd < e₂.oEnd

theorem transgen_ordered
    (hpath : Relation.TransGen (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.oEnd n < e₂.oEnd n := by
  induction hpath with
  | single hstep => exact step_ordered hstep
  | tail _ hstep ih => exact Nat.lt_trans ih (step_ordered hstep)

theorem cmcm_acyclic
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  exact Nat.lt_irrefl _ (transgen_ordered hcycle)

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init'

/-! ## PartialOrder (consequence of acyclicity) -/

/-- The PartialOrder on events (GMO): constructed from cmcm_acyclic.
    lt = TransGen (PPOi ∪ com), le = (· = ·) ∨ TransGen (PPOi ∪ com).
    Antisymmetry from acyclicity. Transitivity from TransGen. -/
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
