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

/-! ## Custom protocol event chain for acyclicity

The standard TransGen + per-edge measures don't work (oEnd dead end).
We define a custom inductive that tracks OB on specific protocol events
at two communication levels: cluster cache and cluster directory.

Each constructor represents a junction between edges (PPOi↔COM) at a
specific communication level, carrying the protocol events and their
OB/EncapsulatedBy relationships. The chain has strictly increasing oEnd
on the protocol events it tracks. A cycle loops: X.oEnd < X.oEnd. -/

/-- Custom transitive closure tracking OB on protocol events at two levels.
    Each constructor is a 2-step composition (PPOi→COM or COM→PPOi)
    with the specific protocol events at the applicable communication level.

    The `lb` parameter tracks a lower bound on oEnd values in the chain.
    Each constructor proves lb < final.oEnd. A cycle gives lb < lb. -/
inductive ProtocolChain (lb : Nat) : Event n → Event n → Prop where
  /-- PPOi step: e₁ OB e₂ (same cache). lb ≤ e₁.oEnd, e₁.oEnd < e₂.oEnd. -/
  | ppoi_step (hppoi : @PPOi n b e₁ e₂) (hlb : lb ≤ e₁.oEnd n)
    : ProtocolChain lb e₁ e₂
  /-- COM step with OB on cache events (e.g. co.sameCle): e₁ OB e₂ directly. -/
  | com_cache_ob (hcom : com compound b init e₁ e₂) (hob : e₁.OrderedBefore n e₂)
    (hlb : lb ≤ e₁.oEnd n) : ProtocolChain lb e₁ e₂
  /-- COM step with OB on protocol events: e₁ OB e_r_down inside e₂.
      The chain through e_r_down/e_r_cdir_down gives e₁.oEnd < e₂.oEnd. -/
  | com_downgrade (hcom : com compound b init e₁ e₂)
    (e_down : Event n) (hob : e₁.OrderedBefore n e_down)
    (hdown_in_e₂ : e_down.oEnd n < e₂.oEnd n)
    (hlb : lb ≤ e₁.oEnd n) : ProtocolChain lb e₁ e₂
  /-- COM step with CLE ordering: CLE₁ OB CLE₂.
      If CLE₁ EncapsulatedBy e₁ or e₁ OB CLE₁: chain through CLEs. -/
  | com_cle_order (hcom : com compound b init e₁ e₂)
    (cle₁ cle₂ : Event n) (hcle_ob : cle₁.OrderedBefore n cle₂)
    (hcle₂_in_e₂ : cle₂.oEnd n < e₂.oEnd n)
    (hlb_cle : lb ≤ cle₁.oEnd n) : ProtocolChain lb e₁ e₂
  -- Note: trans is NOT a constructor (Lean kernel restriction on nested occurrence).
  -- Transitivity is proven as a separate theorem.

/-- Every ProtocolChain gives lb < e₂.oEnd. -/
theorem chain_lb_lt_end (hchain : @ProtocolChain n compound b init lb e₁ e₂)
    : lb < e₂.oEnd n := by
  induction hchain with
  | ppoi_step hppoi hlb =>
    exact Nat.lt_of_le_of_lt hlb (Nat.lt_trans hppoi.orderedBefore (Event.oWellFormed n e₂))
  | com_cache_ob _ hob hlb =>
    exact Nat.lt_of_le_of_lt hlb (Nat.lt_trans hob (Event.oWellFormed n e₂))
  | com_downgrade _ _ hob hdown_in hlb =>
    exact Nat.lt_of_le_of_lt hlb (Nat.lt_trans (Nat.lt_trans hob (Event.oWellFormed n _)) hdown_in)
  | com_cle_order _ _ _ hcle_ob hcle₂_in hlb_cle =>
    exact Nat.lt_of_le_of_lt hlb_cle (Nat.lt_trans (Nat.lt_trans hcle_ob (Event.oWellFormed n _)) hcle₂_in)
  -- (no trans constructor — transitivity is external)

/-- Chain composition: if lb < mid.oEnd and mid.oEnd < end.oEnd,
    then lb < end.oEnd. Used in place of trans constructor. -/
theorem chain_lb_lt_end_trans
    (h₁₂ : @ProtocolChain n compound b init lb e₁ e₂)
    (h₂₃ : @ProtocolChain n compound b init (Event.oEnd n e₂) e₂ e₃)
    : lb < e₃.oEnd n :=
  Nat.lt_trans (chain_lb_lt_end h₁₂) (chain_lb_lt_end h₂₃)

/-- Each PPOi step gives e₁.oEnd < e₂.oEnd (from OB + well-formedness). -/
theorem ppoi_oEnd_lt (hppoi : @PPOi n b e₁ e₂) : e₁.oEnd n < e₂.oEnd n :=
  Nat.lt_trans hppoi.orderedBefore (Event.oWellFormed n e₂)

/-- Each PPOi step gives e₁.oEnd < e₂.oStart (from OB). -/
theorem ppoi_oEnd_lt_oStart (hppoi : @PPOi n b e₁ e₂) : e₁.oEnd n < e₂.oStart n :=
  hppoi.orderedBefore

-- For encapDir: e.oStart < CLE.oStart (protocol property from reqEncapDir)

/-- TransGen path gives e₁.oEnd < e₂.oEnd by consuming 1 or 2 steps.
    For PPOi: single step gives oEnd increase.
    For COM with OB: single step gives oEnd increase.
    For COM with CLE ordering: 2-step (PPOi then COM) bridges via
    e₁.oEnd < e₂.oStart < CLE₂.oStart ≤ CLE₂.oEnd < CLE₃.oEnd < e₃.oEnd. -/
theorem transgen_lb_lt
    (hpath : Relation.TransGen (@PPOi n b ∪ com compound b init) e₁ e₂)
    : e₁.oEnd n < e₂.oEnd n := by
  -- Use head induction: decompose into first step + remaining path.
  -- For PPOi first: single step gives oEnd increase, compose with ih.
  -- For COM first with direct OB: single step gives oEnd increase.
  -- For COM first with CLE ordering: need 2-step with the NEXT step.
  sorry

theorem cmcm_acyclic
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  exact Nat.lt_irrefl _ (transgen_lb_lt hcycle)

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
