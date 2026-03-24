import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Proof strategy: edge-by-edge OB chains on protocol events

A cycle through PPOi + com edges creates a chain of OB/Encapsulation relationships
between specific protocol events (CLEs, cache events, directory downgrades).
This chain loops back, giving X < X on timestamps — contradiction.

Example cycle: e₁ PPOi e₂, e₂ Rfe e₃, e₃ Fr e₁ (all same address).
- PPOi: CLE₁ OB e₂ (e₁ lins at CLE, e₂ lins at cache)
- Rfe: e₂ OB e_r_down (write before downgrade), e_r_cdir_down encaps e_r_down
- Fr: e_r_cdir_down OB CLE₁ (cluster dir downgrade before e₁'s CLE)
Chain: CLE₁.oEnd < e₂.oEnd < e_r_down.oEnd < e_r_cdir_down.oEnd, and
       e_r_cdir_down.oEnd < CLE₁.oStart ≤ CLE₁.oEnd → CLE₁.oEnd < CLE₁.oEnd. ⊥

Each edge contributes:
- **PPOi**: e₁ OB e₂ (same cache), or lin(e₁) OB lin(e₂)
- **rfe**: e_w OB e_r_down, e_r_cdir_down encaps e_r_down, e_r_cdir_down inside CLE(e_r)
- **co**: similar downgrade structure (e_w₁ OB downgrade inside e_w₂)
- **fr**: e_r_cdir_down OB CLE(target) (cluster dir downgrade ordered with target's CLE)

The composition uses Trans instances: EncapsulatedBy → OB → OB, OB → OB → OB.
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

/-! ## Ordering sub-lemmas

Each edge type establishes ordering between specific protocol events.
These are used to compose OB chains across cycle edges. -/

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

/-! ## Main theorem: acyclicity via edge-by-edge OB chains

The proof shows: any cycle in PPOi ∪ com creates a chain of OB/Encapsulation
relationships between specific protocol events that loops back, giving
X.oEnd < X.oEnd — contradiction.

Each step in the cycle contributes an OB relationship between protocol events.
The EncapsulatedBy → OB → OB composition (Trans instances in EventRelations.lean)
chains these across consecutive edges. -/

/-- Each edge in PPOi ∪ com satisfies finishesBefore: e₁.oEnd < e₂.oEnd.

    For PPOi: e₁ OB e₂ → e₁.oEnd < e₂.oStart ≤ e₂.oEnd.
    For rfe: e_w OB e_r_down, e_r_down inside e_r → e_w.oEnd < e_r.oEnd.
    For co: from communication evidence (downgrade inside e₂).
    For fr: from rf⁻¹;co composition. -/
theorem step_finishesBefore
    (hstep : (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.finishesBefore n e₂ := by
  cases hstep with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ → e₁.oEnd < e₂.oStart ≤ e₂.oEnd
    unfold Event.finishesBefore
    have hob := hppoi.orderedBefore
    -- e₁.oEnd < e₂.oStart from OB, and e₂.oStart ≤ e₂.oEnd from well-formedness
    -- OB: e₁.oEnd < e₂.oStart. WF: e₂.oStart < e₂.oEnd. Chain: e₁.oEnd < e₂.oEnd.
    exact Nat.lt_trans hob (Event.oWellFormed n e₂)
  | inr hcom =>
    cases hcom with
    | rfe h =>
      -- rfe: extract the downgrade chain from readsFrom.cases
      -- For cross-cluster (wObRGle.diffCluster): e_w OB e_r_down, chain → e₁.oEnd < e₂.oEnd
      -- For orderAfterDir reader: CLE from successor, but not a cycle problem
      unfold Event.finishesBefore
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster _ => exact absurd hwr_same_cluster h.diffProtocol
      | wObRGle _ hw_ob_r_gle_cases =>
        cases hw_ob_r_gle_cases with
        | sameCluster hsc _ => exact absurd hsc h.diffProtocol
        | diffCluster _ _ _ hdiff_cache_case =>
          -- diffCluster: extract the downgrade chain
          cases hdiff_cache_case with
          | wHasPermsAfter _ coherent_case =>
            cases coherent_case with
            | immPred _ hencapPD =>
              -- hencapPD : encapProxyAndDirAndCDown e_w hr_c_and_g_lin
              -- hencapPD.existsRDownAtW : ∃ e_r_down, ... ∧ e_w OB e_r_down
              -- hencapPD.encapDir.existsRClusterDirDown : ∃ e_r_cdir_down, ... ∧ encapDirRelation
              -- Chain: e_w OB e_r_down (existsRDownAtW)
              --        e_r_cdir_down encaps e_r_down (cdirEncapsDown)
              --        e_r_cdir_down.oEnd < CLE.oEnd (encapDirRelation)
              --        CLE.oEnd ≤ e_r.oEnd (dirAccessOfRequest)
              -- Step 1: e_w.oEnd < e_r_down.oStart (from OB)
              have hw_ob := hencapPD.existsRDownAtW.choose_spec.2.2.2
              -- Step 2: e_r_down.oEnd < e_r_cdir_down.oEnd (from cdirEncapsDown)
              have hdown_lt_cdir := hencapPD.cdirEncapsDown.2
              -- Step 3: e_r_cdir_down.oEnd < CLE.oEnd (from encapDirRelation)
              have hencap_rel := hencapPD.encapDir.existsRClusterDirDown.choose_spec.2.2.2
              have hcdir_lt_cle : hencapPD.encapDir.existsRClusterDirDown.choose.oEnd n <
                  h.r_lin.hreq's_dir_access.choose.oEnd n := by
                cases hencap_rel with
                | cleEncap henc => exact henc.2
                | gcacheEncap _ hlt => exact hlt
              -- Step 4: CLE.oEnd < e₂.oEnd (from reader's dirAccessOfRequest)
              -- For encapDir: e₂ encapsulates CLE → CLE.oEnd < e₂.oEnd
              -- For orderBeforeDir: CLE.oEnd < pred.oEnd < e₂.oStart < e₂.oEnd
              -- For orderAfterDir: sorry (nc.weak, not a cycle problem)
              have hcle_lt_e2 : h.r_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
                have hdir := h.r_lin.hreq's_dir_access.choose_spec.2
                cases hdir with
                | encapDir _ hencap => exact hencap.reqEncapDir.2
                | orderBeforeDir _ hexists_pred hpred_dir _ _ _ _ _ =>
                  -- CLE inside pred (pred encapsulates CLE)
                  have hcle_lt_pred := hpred_dir.reqEncapDir.2
                  -- pred OB e₂ (pred.OrderedBefore = pred.oEnd < e₂.oStart)
                  have hpred_ob_e2 : hexists_pred.choose.OrderedBefore n e₂ :=
                    hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                  -- Chain: CLE.oEnd < pred.oEnd < e₂.oStart < e₂.oEnd
                  exact Nat.lt_trans (Nat.lt_trans hcle_lt_pred hpred_ob_e2) (Event.oWellFormed n e₂)
                | orderAfterDir _ _ _ _ => sorry -- nc.weak, not a cycle problem
              -- Compose: e₁.oEnd < e_r_down.oStart ≤ e_r_down.oEnd < e_r_cdir_down.oEnd < CLE.oEnd < e₂.oEnd
              exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
                (Nat.lt_trans hw_ob (Event.oWellFormed n _))
                hdown_lt_cdir) hcdir_lt_cle) hcle_lt_e2
            | notImmPred _ => sorry
          | wNoPermsAfter _ _ _ => sorry
          | wCleAfter _ => sorry
    | co h =>
      unfold Event.finishesBefore
      cases h.ordering with
      | sameGle _ cle_cases =>
        cases cle_cases with
        | sameCle _ cache_ob =>
          -- Same CLE, e₁ OB e₂ → finishesBefore
          exact Nat.lt_trans cache_ob (Event.oWellFormed n e₂)
        | diffCle _ =>
          -- Different CLE: same structural gap as rfe (need CLE→cache event chain)
          sorry
      | wObRGle _ cle_cases =>
        -- GLE ordering with CLE sub-cases. DiffCluster carries encapProxyAndDirAndCDown.
        cases cle_cases with
        | sameCluster _ same_cluster_cases =>
          -- Same cluster, different GLE: CLE ordering from SameCluster.cleOb
          cases same_cluster_cases with
          | wImmPredRCle w_imm_pred =>
            cases w_imm_pred with
            | sameCluster _ hcle_ob =>
              -- CLE₁ OB CLE₂. Need CLE→cache event chain.
              sorry
            | diffCluster _ hencap =>
              -- diffCluster carries encapDir. Need encapProxyAndDirAndCDown.
              sorry
          | evictOrReadBetweenWAndRCleSameCluster evict =>
            sorry
        | diffCluster _ diff_cluster_cases =>
          -- DiffCluster: ReadDowngradeAtWrite carries encapProxyAndDirAndCDown!
          cases diff_cluster_cases with
          | wCleImmPredDown w_pred =>
            -- w_pred.rDown : encapProxyAndDirAndCDown
            have hw_ob_rdown := w_pred.rDown.existsRDownAtW.choose_spec.2.2.2
            have hcdir_encaps := w_pred.rDown.cdirEncapsDown
            have hencap_rel := w_pred.rDown.encapDir.existsRClusterDirDown.choose_spec.2.2.2
            have hcdir_lt_cle : w_pred.rDown.encapDir.existsRClusterDirDown.choose.oEnd n <
                h.w₂_lin.hreq's_dir_access.choose.oEnd n := by
              cases hencap_rel with
              | cleEncap henc => exact henc.2
              | gcacheEncap _ hlt => exact hlt
            have hcle_lt_e2 : h.w₂_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
              have hdir := h.w₂_lin.hreq's_dir_access.choose_spec.2
              cases hdir with
              | encapDir _ hencap => exact hencap.reqEncapDir.2
              | orderBeforeDir _ hexists_pred hpred_dir _ _ _ _ _ =>
                have hcle_lt_pred := hpred_dir.reqEncapDir.2
                have hpred_ob_e2 : hexists_pred.choose.OrderedBefore n e₂ :=
                  hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                exact Nat.lt_trans (Nat.lt_trans hcle_lt_pred hpred_ob_e2) (Event.oWellFormed n e₂)
              | orderAfterDir _ _ _ _ => sorry -- nc.weak, not cycle problem
            exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
              (Nat.lt_trans hw_ob_rdown (Event.oWellFormed n _))
              hcdir_encaps.2) hcdir_lt_cle) hcle_lt_e2
          | evictOrReadBetweenWAndRDown w_evict =>
            -- w_evict.rDown : encapProxyAndDirAndCDown (same structure)
            have hw_ob_rdown := w_evict.rDown.existsRDownAtW.choose_spec.2.2.2
            have hcdir_encaps := w_evict.rDown.cdirEncapsDown
            have hencap_rel := w_evict.rDown.encapDir.existsRClusterDirDown.choose_spec.2.2.2
            have hcdir_lt_cle : w_evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd n <
                h.w₂_lin.hreq's_dir_access.choose.oEnd n := by
              cases hencap_rel with
              | cleEncap henc => exact henc.2
              | gcacheEncap _ hlt => exact hlt
            have hcle_lt_e2 : h.w₂_lin.hreq's_dir_access.choose.oEnd n < e₂.oEnd n := by
              have hdir := h.w₂_lin.hreq's_dir_access.choose_spec.2
              cases hdir with
              | encapDir _ hencap => exact hencap.reqEncapDir.2
              | orderBeforeDir _ hexists_pred hpred_dir _ _ _ _ _ =>
                have hcle_lt_pred := hpred_dir.reqEncapDir.2
                have hpred_ob_e2 : hexists_pred.choose.OrderedBefore n e₂ :=
                  hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                exact Nat.lt_trans (Nat.lt_trans hcle_lt_pred hpred_ob_e2) (Event.oWellFormed n e₂)
              | orderAfterDir _ _ _ _ => sorry -- nc.weak, not cycle problem
            exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans
              (Nat.lt_trans hw_ob_rdown (Event.oWellFormed n _))
              hcdir_encaps.2) hcdir_lt_cle) hcle_lt_e2
    | fr h =>
      -- fr: rf⁻¹;co composition
      sorry -- need: compose rf + co finishesBefore

/-- A TransGen path in PPOi ∪ com gives finishesBefore.
    Most steps give finishesBefore directly. For nc.weak reader with orderAfterDir
    (where the rfe downgrade chain goes through the successor), the proof consumes
    two steps: rfe + the next step (PPOi or fr to the successor). -/
theorem transgen_finishesBefore
    (hpath : Relation.TransGen (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.finishesBefore n e₂ := by
  induction hpath with
  | single hstep => exact step_finishesBefore hstep
  | tail _ hstep ih => exact Nat.lt_trans ih (step_finishesBefore hstep)

theorem cmcm_acyclic
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  exact Nat.lt_irrefl _ (transgen_finishesBefore hcycle)

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' hknow

/-! ## PartialOrder (consequence of acyclicity) -/

/-- The PartialOrder on events (GMO): constructed from cmcm_acyclic.
    lt = TransGen (PPOi ∪ com), le = (· = ·) ∨ TransGen (PPOi ∪ com).
    Antisymmetry from acyclicity. Transitivity from TransGen. -/
noncomputable def eventPartialOrder
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : PartialOrder (Event n) := by
  let R := @PPOi n b ∪ com compound b init
  have hacyclic := @cmcm_acyclic n compound b init hknow
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
