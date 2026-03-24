import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Proof strategy: OB chains on protocol events (NOT per-edge)

Each edge gives OB/EncapsulatedBy relationships between specific protocol events
(e_w, e_r_down, e_r_cdir_down, CLE). A cycle chains these relationships
across ALL edges simultaneously. The chain of strict inequalities on oEnd
values loops back, giving X < X — contradiction.

IMPORTANT: Per-edge measures (finishesBefore, e.oEnd) do NOT work for all cases.
The proof MUST compose across edges. The OB chain on protocol events is the
correct approach — it goes through CLE, cache events, and directory downgrades
at the appropriate level for each edge.
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

/-! ## Main theorem: acyclicity

The acyclicity proof shows: any cycle through PPOi + com edges leads to
a contradiction, because the protocol's OB/EncapsulatedBy relationships
between communication events (e_w OB e_r_down, e_r_cdir_down encaps e_r_down,
CLE₁ OB CLE₂, etc.) form a chain that loops, giving X < X.

The proof composes across edges using the Trans instances:
- OB → OB → OB (transitivity)
- EncapsulatedBy → OB → OB
- OB → Encapsulates → OB -/

/-- Each PPOi/com edge gives e₁ OB e₂ (on the cache events themselves)
    or e₁.oEnd < some protocol event's oEnd inside/past e₂.
    For PPOi: e₁ OB e₂ directly (same cache, guaranteed). -/
theorem step_ob_or_inside
    (hstep : (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.OrderedBefore n e₂ ∨ (e₁.oEnd n < e₂.oEnd n) := by
  cases hstep with
  | inl hppoi =>
    -- PPOi: e₁ OB e₂ (same cache, PPO pair)
    exact Or.inl hppoi.orderedBefore
  | inr hcom =>
    -- COM: the communication chain gives OB between protocol events.
    -- For most cases: the chain gives e₁.oEnd < e₂.oEnd (OB on protocol events
    -- that are inside e₂ via EncapsulatedBy).
    -- For orderAfterDir/CLE gap: the chain goes past e₂ to CLE or successor.
    -- In either case: Or.inl (OB) or Or.inr (oEnd comparison).
    sorry

theorem cmcm_acyclic
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  -- Two-case argument:
  -- Case 1: cycle contains PPOi or COM-with-downgrade edge.
  --   Max-oEnd argument: event with maximum oEnd can't have outgoing
  --   PPOi (OB to larger target) or COM-with-downgrade (OB to protocol
  --   event inside target). Both contradict maximality.
  -- Case 2: cycle contains only CO-CLE-ordering edges.
  --   CLE chain argument: CLEs form a monotone chain CLE₁.oEnd < ... < CLEₖ.oEnd.
  --   The cycle loops: CLEₖ OB CLE₁ gives CLEₖ.oEnd < CLE₁.oEnd.
  --   Combined with chain: CLE₁.oEnd < CLEₖ.oEnd < CLE₁.oEnd. Contradiction.
  sorry

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init'

/-! ## PartialOrder (consequence of acyclicity) -/

/-- The PartialOrder on events (GMO): constructed from cmcm_acyclic. -/
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
