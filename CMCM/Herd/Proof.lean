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

/-! ## StepOrdering: the Global Memory Order derived from each edge

Each edge in PPOi ∪ com gives an ordering relationship between protocol events,
composed via OB + Encapsulates/EncapsulatedBy transitivity.

Two constructors:
- `ob`: direct OrderedBefore (e₁ OB e₂). From PPOi or same-cache COM.
- `obThenEncap`: e₁ OB p, p EncapsulatedBy e₂. From cross-cache COM where
  the communication chain reaches a protocol event p (e_r_down, e_r_cdir_down, CLE)
  that is inside e₂ (via the Encapsulates bridge).

Transitivity uses the Trans instances:
- OB → OB → OB
- EncapsulatedBy → OB → OB (the key junction rule)
- EncapsulatedBy → EncapsulatedBy → EncapsulatedBy

A cycle gives StepOrdering e e, which is irreflexive → contradiction. -/

/-- StepOrdering: the ordering relationship derived from each edge.
    Three cases following the OB/Encapsulates chain through protocol events. -/
inductive StepOrdering : Event n → Event n → Prop where
  /-- Direct OB: e₁ OB e₂ -/
  | ob (h : e₁.OrderedBefore n e₂) : StepOrdering e₁ e₂
  /-- OB then EncapsulatedBy: e₁ OB p, p inside e₂ -/
  | obEncap (p : Event n) (h_ob : e₁.OrderedBefore n p) (h_encap : p.EncapsulatedBy n e₂)
      : StepOrdering e₁ e₂
  /-- Inner OB external: p inside e₁, p OB e₂ -/
  | encapOb (p : Event n) (h_encap : p.EncapsulatedBy n e₁) (h_ob : p.OrderedBefore n e₂)
      : StepOrdering e₁ e₂
  /-- Both encapsulated: p₁ inside e₁, p₁ OB p₂, p₂ inside e₂ -/
  | encapObEncap (p₁ p₂ : Event n) (h_e₁ : p₁.EncapsulatedBy n e₁) (h_ob : p₁.OrderedBefore n p₂)
      (h_e₂ : p₂.EncapsulatedBy n e₂) : StepOrdering e₁ e₂

/-- StepOrdering is transitive.
    The junction at e₂ composes "output at e₂" with "input from e₂"
    using OB/Encapsulates Trans instances.
    The hard cases (both inner events EncapsulatedBy e₂) need
    protocol hierarchy (dir_ordered at same cluster). -/
theorem StepOrdering.trans {e₁ e₂ e₃ : Event n}
    (h₁₂ : StepOrdering e₁ e₂) (h₂₃ : StepOrdering e₂ e₃) : StepOrdering e₁ e₃ := by
  -- Helper: compose OB to e₂ with step from e₂
  -- (handles ob and encapOb outputs meeting ob/obEncap/encapOb/encapObEncap inputs)
  have from_ob (p : Event n) (hp_ob : p.OrderedBefore n e₂) :
      StepOrdering p e₃ := by
    cases h₂₃ with
    | ob h => exact .ob (Trans.trans hp_ob h)
    | obEncap q hq hqe => exact .obEncap q (Trans.trans hp_ob hq) hqe
    | encapOb q hqe hq =>
      exact .ob (Trans.trans (Trans.trans hp_ob hqe) hq)
    | encapObEncap q₁ q₂ hq₁ hq hq₂ =>
      exact .obEncap q₂ (Trans.trans (Trans.trans hp_ob hq₁) hq) hq₂
  -- Helper: compose EncapsulatedBy e₂ with step from e₂
  -- (handles obEncap and encapObEncap outputs meeting ob/obEncap inputs)
  have from_encap (p : Event n) (hp_enc : p.EncapsulatedBy n e₂) :
      StepOrdering p e₃ := by
    cases h₂₃ with
    | ob h =>
      -- p EncapBy e₂, e₂ OB e₃ → p OB e₃ (EncapsulatedBy → OB → OB)
      exact .ob (Trans.trans hp_enc h)
    | obEncap q hq hqe =>
      -- p EncapBy e₂, e₂ OB q → p OB q
      exact .obEncap q (Trans.trans hp_enc hq) hqe
    | encapOb q hqe hq =>
      -- p EncapBy e₂, q EncapBy e₂: both inside e₂.
      -- Protocol: p and q at same cluster → dir_ordered gives ordering.
      sorry
    | encapObEncap q₁ q₂ hq₁ hq hq₂ =>
      -- p EncapBy e₂, q₁ EncapBy e₂: both inside e₂.
      sorry
  -- Main proof: case split on h₁₂
  cases h₁₂ with
  | ob h₁₂ =>
    exact from_ob e₁ h₁₂
  | obEncap p hp hpe =>
    -- e₁ OB p, p EncapBy e₂ → from_encap gives StepOrdering p e₃
    -- Then prepend e₁ OB p
    have h := from_encap p hpe
    cases h with
    | ob h => exact .ob (Trans.trans hp h)
    | obEncap q hq hqe => exact .obEncap q (Trans.trans hp hq) hqe
    | encapOb q hqe hq =>
      -- p EncapBy something, q OB e₃. Compose: e₁ OB p, ... → e₁ OB e₃
      sorry
    | encapObEncap q₁ q₂ hq₁ hq hq₂ =>
      sorry
  | encapOb p hpe hp =>
    -- p EncapBy e₁, p OB e₂ → from_ob gives StepOrdering p e₃
    -- Then wrap with p EncapBy e₁
    have h := from_ob p hp
    cases h with
    | ob h => exact .encapOb p hpe h
    | obEncap q hq hqe => exact .encapObEncap p q hpe hq hqe
    | encapOb q hqe hq =>
      sorry
    | encapObEncap q₁ q₂ hq₁ hq hq₂ =>
      sorry
  | encapObEncap p₁ p₂ hp₁ hp hp₂ =>
    -- p₁ EncapBy e₁, p₁ OB p₂, p₂ EncapBy e₂ → from_encap gives StepOrdering p₂ e₃
    -- Then prepend p₁ OB p₂ and wrap with p₁ EncapBy e₁
    have h := from_encap p₂ hp₂
    cases h with
    | ob h => exact .encapOb p₁ hp₁ (Trans.trans hp h)
    | obEncap q hq hqe => exact .encapObEncap p₁ q hp₁ (Trans.trans hp hq) hqe
    | encapOb q hqe hq =>
      sorry
    | encapObEncap q₁ q₂ hq₁ hq hq₂ =>
      sorry

/-- StepOrdering is irreflexive. -/
theorem StepOrdering.irrefl {e : Event n} (h : StepOrdering e e) : False := by
  cases h with
  | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
  | obEncap p h_ob h_encap =>
    exact Nat.lt_irrefl _
      (Nat.lt_trans (Nat.lt_trans h_ob (Event.oWellFormed n p)) h_encap.right)
  | encapOb p h_encap h_ob =>
    exact Nat.lt_irrefl _
      (Nat.lt_trans h_ob (Nat.lt_trans h_encap.left (Event.oWellFormed n p)))
  | encapObEncap p₁ p₂ hp₁ h_ob hp₂ =>
    -- Two inner events of same event, ordered. No direct contradiction.
    sorry
/-- Chain StepOrdering through TransGen: produces a single StepOrdering. -/
theorem StepOrdering.of_transGen
    (h : Relation.TransGen (@StepOrdering n) e₁ e₂) : StepOrdering e₁ e₂ := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact StepOrdering.trans ih h

/-- StepOrdering is acyclic: no event can reach itself. -/
theorem StepOrdering.acyclic : Relation.Acyclic (@StepOrdering n) := by
  intro e hcycle
  exact StepOrdering.irrefl (StepOrdering.of_transGen hcycle)

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
  -- co: case split on co.ordering (communication level)
  have hw₁ : h.w₁_lin = h₁_lin := Subsingleton.elim _ _
  have hw₂ : h.w₂_lin = h₂_lin := Subsingleton.elim _ _
  -- Helper: wObRDown + encapDirRelation → CLE₁.oEnd < CLE₂.oEnd
  have chain_wObRDown :
      ∀ (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.w₂_lin)
        (hwOB : h.w₁_lin.hreq's_dir_access.choose.OrderedBefore n
          hdown.existsRClusterDirDown.choose),
      h.w₁_lin.hreq's_dir_access.choose.oEnd < h.w₂_lin.hreq's_dir_access.choose.oEnd := by
    intro hdown hwOB
    have hcdir_encap_rel := hdown.existsRClusterDirDown.choose_spec.2.2.2
    have hcdir_lt : hdown.existsRClusterDirDown.choose.oEnd <
        h.w₂_lin.hreq's_dir_access.choose.oEnd := by
      cases hcdir_encap_rel with
      | cleEncap henc => simp [Event.Encapsulates] at henc; exact henc.2
      | gcacheEncap _ hlt => exact hlt
    exact Nat.lt_trans (Nat.lt_trans hwOB
      (Event.oWellFormed n hdown.existsRClusterDirDown.choose)) hcdir_lt
  cases h.comm with
  | sameCache cle_eq cache_ob =>
    -- Same cache: secondary advance from e₁ OB e₂
    right; constructor
    · rw [← hw₁, ← hw₂]; exact congrArg (Event.oEnd n) cle_eq
    · exact Nat.lt_trans cache_ob (Event.oWellFormed n e₂)
  | sameClusDiffCache _ cle_ord =>
    -- Same cluster, diff cache: CLE ordering from cluster dir serialization
    left; rw [← hw₁, ← hw₂]
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob =>
        exact Nat.lt_trans hob (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
      | diffCluster hdiff hdown hwObRDown =>
        exact chain_wObRDown hdown hwObRDown
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact Nat.lt_trans evict.wObR (Event.oWellFormed n h.w₂_lin.hreq's_dir_access.choose)
  | diffClus _ diff_cluster_cases =>
    -- Different cluster: cross-cluster downgrade chain
    left; rw [← hw₁, ← hw₂]
    cases diff_cluster_cases with
    | wCleImmPredDown w =>
      exact chain_wObRDown w.rDown.encapDir w.wObRDown
    | evictOrReadBetweenWAndRDown evict =>
      exact chain_wObRDown evict.rDown.encapDir evict.wObRDown

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
              | noEvictBetween w =>
                -- noEvictBetween: use dir_ordered on CLE₁ and e_r_cdir_down
                -- to derive wObRDown. Two sub-cases from dir_ordered:
                -- CLE₁ OB de_cdir → gives wObRDown → chain_from_ob
                -- de_cdir OB CLE₁ → chain through cache-level evidence
                have hPDC := w.gdownEncapProxyAndDirAndCDown
                have hcdir_is_dir' := hPDC.encapDir.existsRClusterDirDown.choose_spec.2.1
                have hcle₁_is_dir := h.w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                match hcd' : hPDC.encapDir.existsRClusterDirDown.choose, hcdir_is_dir' with
                | .directoryEvent de_cdir', _ =>
                  match hcw₁ : h.w_lin.hreq's_dir_access.choose, hcle₁_is_dir with
                  | .directoryEvent de_w₁, _ =>
                    simp only [Event.oEnd, hcw₁]
                    cases (b.orderedAtEntry.dir_ordered de_w₁ de_cdir').ordered with
                    | inl hob_cdir =>
                      have hwOB' : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                          hPDC.encapDir.existsRClusterDirDown.choose := by
                        simp only [Event.OrderedBefore, Event.oEnd, Event.oStart, hcw₁, hcd']
                        exact hob_cdir
                      have := chain_from_ob hPDC.encapDir hwOB'
                      simp only [Event.oEnd, hcw₁] at this; exact this
                    | inr hob_cdir =>
                      -- de_cdir' OB de_w₁: chain through cache-level evidence
                      exfalso
                      have he₁_ob_rdown := hPDC.existsRDownAtW.choose_spec.2.2.2
                      have hrdown_lt_cdir : hPDC.existsRDownAtW.choose.oEnd <
                          de_cdir'.oEnd := by
                        have hcdirEncaps := hPDC.cdirEncapsDown
                        simp [Event.Encapsulates, Event.oEnd, hcd'] at hcdirEncaps
                        exact hcdirEncaps.2
                      have hda₁ := h.w_lin.hreq's_dir_access.choose_spec.2
                      rw [hcw₁] at hda₁
                      cases hda₁ with
                      | encapDir _ hencap_e₁ =>
                        have : de_w₁.oEnd < de_w₁.oEnd :=
                          calc de_w₁.oEnd < e₁.oEnd := hencap_e₁.reqEncapDir.right
                            _ < hPDC.existsRDownAtW.choose.oStart := he₁_ob_rdown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir'.oEnd := hrdown_lt_cdir
                            _ < de_w₁.oStart := hob_cdir
                            _ ≤ de_w₁.oEnd := Nat.le_of_lt de_w₁.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderBeforeDir _ hexists_pred hpred _ _ _ _ _ =>
                        have : de_w₁.oEnd < de_w₁.oEnd :=
                          calc de_w₁.oEnd < hexists_pred.choose.oEnd := hpred.reqEncapDir.right
                            _ < e₁.oStart := hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                            _ < e₁.oEnd := Event.oWellFormed n e₁
                            _ < hPDC.existsRDownAtW.choose.oStart := he₁_ob_rdown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir'.oEnd := hrdown_lt_cdir
                            _ < de_w₁.oStart := hob_cdir
                            _ ≤ de_w₁.oEnd := Nat.le_of_lt de_w₁.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderAfterDir _ _ _ _ =>
                        -- e₁ orderAfterDir with wHasPermsAfter: nc.weak CLE sharing
                        sorry
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
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
      -- FR: DERIVE from rf⁻¹;co⁺ + NoInterveningWrites composition.
      -- co⁺ chain gives CLE_w ≤ CLE₂. rf gives CLE_w ≤ CLE₁.
      -- dir_ordered on CLE₁ and CLE₂: CLE₂ < CLE₁ → e₂ is intervening write → contradiction.
      have hw₁ : h.e₁_lin = h₁_lin := Subsingleton.elim _ _
      have hw₂ : h.e₂_lin = h₂_lin := Subsingleton.elim _ _
      rw [← hw₁, ← hw₂]
      -- Extract rf + co chain from fr.comm
      obtain ⟨e_w, _, e_w_lin, _, h_rf, h_no_between, h_co_chain⟩ := h.comm
      -- co⁺ chain gives CLE_w lex≤ CLE₂
      have hlin := fun e => h.hknow_dir_access compound b init e
      have hco_lex := co_chain_cle_advance hlin h_co_chain
      -- CLE_w.oEnd ≤ CLE₂.oEnd from co chain
      have hcw_le_c₂ : (hlin e_w).hreq's_dir_access.choose.oEnd ≤
          (hlin e₂).hreq's_dir_access.choose.oEnd := by
        rcases hco_lex with h | ⟨h, _⟩
        · exact Nat.le_of_lt h
        · exact Nat.le_of_eq h
      -- Use dir_ordered on CLE₁ and CLE₂
      have hdir₁ := h.e₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      have hdir₂ := h.e₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
      match hfc₁ : h.e₁_lin.hreq's_dir_access.choose, hdir₁ with
      | .directoryEvent de₁, _ =>
        match hfc₂ : h.e₂_lin.hreq's_dir_access.choose, hdir₂ with
        | .directoryEvent de₂, _ =>
          by_cases hde_eq : de₁ = de₂
          · -- Same CLE: dir_ordered on equal events → False → anything
            exfalso
            rw [hde_eq] at *
            cases (b.orderedAtEntry.dir_ordered de₂ de₂).ordered with
            | inl h => exact Nat.lt_asymm de₂.oWellFormed h
            | inr h => exact Nat.lt_asymm de₂.oWellFormed h
          · simp only [Event.oEnd, hfc₁, hfc₂]
            cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
            | inl hob => exact Or.inl (Nat.lt_trans hob de₂.oWellFormed)
            | inr hob =>
              -- CLE₂ OB CLE₁: use dir_ordered on CLE₁ and CLE_w
              exfalso
              have hdir_w := (hlin e_w).hreq's_dir_access.choose_spec.2.isDirEvent
              match hfcw : (hlin e_w).hreq's_dir_access.choose, hdir_w with
              | .directoryEvent de_w, _ =>
                cases (b.orderedAtEntry.dir_ordered de₁ de_w).ordered with
                | inl hob_w =>
                  -- CLE₁ OB CLE_w: chain CLE₁ → CLE_w → CLE₂ → CLE₁
                  have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                    simp [Event.oEnd, hfcw,
                      show (hlin e₂) = h.e₂_lin from Subsingleton.elim _ _, hfc₂] at hcw_le_c₂
                    exact hcw_le_c₂
                  have : de₁.oEnd < de₁.oEnd :=
                    calc de₁.oEnd < de_w.oStart := hob_w
                      _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed
                      _ ≤ de₂.oEnd := hcw_le
                      _ < de₁.oStart := hob
                      _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                  exact Nat.lt_irrefl _ this
                | inr hob_w =>
                  -- CLE_w OB CLE₁ and CLE₂ between CLE_w and CLE₁.
                  -- Apply NoInterveningWrites to e₂ to get constraints,
                  -- then show CLE₂ IS between → contradiction.
                  --
                  -- We have: de_w OB de₁ (CLE_w before CLE₁)
                  --          de₂ OB de₁ (hob: CLE₂ before CLE₁)
                  --          de_w.oEnd ≤ de₂.oEnd (from co chain)
                  -- Need: e₂ ∈ b, isClusterCache, ¬down to apply h_no_between.
                  -- Then notBetweenGles/notBetweenCles excludes CLE₂ between CLE_w and CLE₁.
                  sorry
              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh

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
