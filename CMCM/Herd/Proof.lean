import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

## Architecture

`hierarchicallyOrdered` (in Relations.lean) = PPOi ∪ com, carrying communication evidence.
This IS the relation whose acyclicity we prove — and whose transitive closure gives
the PartialOrder (GMO).

## Proof structure

The acyclicity proof decomposes into sub-lemmas for each edge type.
Each sub-lemma shows the edge's communication evidence implies a strict ordering
that prevents cycles.

### Sub-lemmas (each edge type → ordering constraint)

- `ppoi_irrefl`: PPOi(e, e) is impossible (e OB e contradicts irreflexivity)
- `rfe_irrefl`: rfe(e, e) is impossible (diffProtocol for same event)
- `co_irrefl`: co(e, e) is impossible (from co.cases ordering)
- `fr_irrefl`: fr(e, e) is impossible (read ≠ write for same event)

- `ppoi_ordered`: PPOi(e₁, e₂) → CompoundLinearizationOrder
- `rfe_ordered`: rfe(e₁, e₂) → ordering from readsFrom.cases
- `co_ordered`: co(e₁, e₂) → ordering from co.cases
- `fr_ordered`: fr(e₁, e₂) → ordering from rf⁻¹;co composition

### Main theorem

`cmcm_acyclic`: compose sub-lemmas to show any cycle leads to contradiction.
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Irreflexivity sub-lemmas

Each edge type is irreflexive — no event can be related to itself. -/

/-- PPOi is irreflexive: e OB e is impossible. -/
theorem ppoi_irrefl (h : @PPOi n b e e) : False :=
  Event.contradiction_of_reflexive_ordered_before n h.orderedBefore

/-- rfe is irreflexive: diffProtocol for same event is impossible. -/
theorem rfe_irrefl (h : @Herd.rfe n compound b init e e) : False := by
  exact absurd rfl h.diffProtocol

/-- co is irreflexive: co.cases ordering on same event is impossible. -/
theorem co_irrefl (h : @Herd.co n compound b init e e) : False := by
  cases h.ordering with
  | sameGle _ cle_cases =>
    cases cle_cases with
    | sameCle _ hob => exact Event.contradiction_of_reflexive_ordered_before n hob
    | diffCle cle_ord =>
      cases cle_ord with
      | wImmPredRCle w =>
        cases w with
        | sameCluster _ hob =>
          exact Event.contradiction_of_reflexive_ordered_before n hob
        | diffCluster hdiff _ =>
          have : h.w₁_lin = h.w₂_lin := Subsingleton.elim _ _
          exact hdiff (by rw [← same_gle_implies_same_protocol h.w₁_lin h.w₂_lin
            (by cases h.ordering with | sameGle h _ => exact h | wObRGle h _ => rfl)])
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        exact Event.contradiction_of_reflexive_ordered_before n evict.wObR
  | wObRGle hob _ =>
    exact Event.contradiction_of_reflexive_ordered_before n hob

/-- fr is irreflexive: e.isRead ∧ e.isWrite is impossible (read ↔ rw=.r, write ↔ rw=.w). -/
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

/-- com is irreflexive. -/
theorem com_irrefl (h : com compound b init e e) : False := by
  cases h with
  | rfe h => exact rfe_irrefl h
  | co h => exact co_irrefl h
  | fr h => exact fr_irrefl h

/-- hierarchicallyOrdered is irreflexive. -/
theorem hierarchicallyOrdered_irrefl
    (h : @hierarchicallyOrdered n compound b init e e) : False := by
  cases h with
  | ppoi h => exact ppoi_irrefl h
  | com h => exact com_irrefl h

/-! ## Ordering sub-lemmas

Each edge type establishes an ordering constraint from its communication evidence.
These constraints compose to show cycles are impossible. -/

/-- PPOi → compound linearization ordering (for different-address pairs).
    Uses CompoundMCM's `enforce_compound_consistency`. -/
theorem ppoi_compound_lin_order
    (hppoi : @PPOi n b e₁ e₂)
    (hdiff_addr : e₁.addr ≠ e₂.addr)
    : compound.CompoundLinearizationOrder n b init e₁ e₂ :=
  CompoundProtocol.enforce_compound_consistency n compound
    hppoi.sameProtocol hppoi.notDown₁ hppoi.notDown₂
    hppoi.cache₁ hppoi.cache₂ hppoi.in_b₁ hppoi.in_b₂
    hppoi.sameCid' hdiff_addr hppoi.orderedBefore

/-- rfe → GLE ordering from readsFrom.cases.
    wObRGle gives GLE(e_w) OB GLE(e_r); wEqRGle is absurd for rfe (same cluster). -/
theorem rfe_gle_ordered
    (h : @Herd.rfe n compound b init e₁ e₂)
    : h.w_lin.hreq's_global_lin.choose.OrderedBefore n
      h.r_lin.hreq's_global_lin.choose := by
  cases h.readsFrom with
  | wEqRGle _ hwr_same_cluster _ =>
    exact absurd hwr_same_cluster h.diffProtocol
  | wObRGle hw_r_gle_ob _ =>
    exact hw_r_gle_ob

/-! ## Compound linearization event extraction

The compound linearization event for a request is where it "meets" the protocol
hierarchy. This is the ranking witness for the acyclicity proof. -/

/-- Extract the compound linearization event for a request event. -/
noncomputable def compoundLinEvent (e : Event n) : Event n :=
  (compound.compoundLinearizationEvent compound.shimAxioms b init e
    (compound.linearizationOfEvent b init e)).linearizationEvent

/-! ## Each edge type advances compound linearization events

These are the key composition lemmas. Each shows the edge's communication
evidence implies the compound lin event strictly advances. -/

/-- PPOi → compound lin events ordered.
    For diff-addr: CompoundMCM's enforce_compound_consistency gives CompoundLinearizationOrder.
    For same-addr: cache events encapsulate their compound lin events, so e₁ OB e₂ propagates.
    The lazy case (finishesBefore, not OB) needs separate handling. -/
theorem ppoi_advances_compoundLin
    (hppoi : @PPOi n b e₁ e₂)
    : (@compoundLinEvent n compound b init e₁).OrderedBefore n (@compoundLinEvent n compound b init e₂) := by
  -- CompoundLinearizationOrder gives: isPPOPair → e_lin₁ OB e_lin₂ ∨ lazy
  -- For diff-addr: ppoi_compound_lin_order provides this directly.
  -- For same-addr: the same encapsulation argument works (e₁ OB e₂ + encap → e_lin₁ OB e_lin₂).
  -- Both cases: cache events either ARE or ENCAPSULATE their compound lin events.
  -- Combined with e₁.OrderedBefore n e₂, this gives compoundLinEvent e₁ OB compoundLinEvent e₂.
  sorry

/-- rfe → compound lin events ordered.
    rfe gives GLE ordering. Bridge: GLE ordering → compound lin event ordering. -/
theorem rfe_advances_compoundLin
    (h : @Herd.rfe n compound b init e₁ e₂)
    : (@compoundLinEvent n compound b init e₁).OrderedBefore n (@compoundLinEvent n compound b init e₂) := by
  sorry

/-- co → compound lin events ordered. -/
theorem co_advances_compoundLin
    (h : @Herd.co n compound b init e₁ e₂)
    : (@compoundLinEvent n compound b init e₁).OrderedBefore n (@compoundLinEvent n compound b init e₂) := by
  sorry

/-- fr → compound lin events ordered. -/
theorem fr_advances_compoundLin
    (h : @Herd.fr n compound b init e₁ e₂)
    : (@compoundLinEvent n compound b init e₁).OrderedBefore n (@compoundLinEvent n compound b init e₂) := by
  sorry

/-! ## Main theorem

The acyclicity proof:
1. Each edge advances compound linearization events
2. OB on events is irreflexive and transitive
3. A cycle would require OB to form a loop → contradiction -/

/-- Every step in PPOi ∪ com advances the compound linearization event. -/
private theorem step_advances_compoundLin
    (hstep : (@PPOi n b ∪ com compound b init) e₁ e₂)
    : (@compoundLinEvent n compound b init e₁).OrderedBefore n (@compoundLinEvent n compound b init e₂) := by
  cases hstep with
  | inl hppoi => exact ppoi_advances_compoundLin hppoi
  | inr hcom => cases hcom with
    | rfe h => exact rfe_advances_compoundLin h
    | co h => exact co_advances_compoundLin h
    | fr h => exact fr_advances_compoundLin h

/-- The CMCM theorem: `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

    Every edge advances compound linearization events. Since OB is irreflexive
    and transitive, a cycle through TransGen would give e_lin OB e_lin — contradiction. -/
theorem cmcm_acyclic
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  suffices h : ∀ e', Relation.TransGen (@PPOi n b ∪ com compound b init) e e' →
      (@compoundLinEvent n compound b init e).OrderedBefore n (@compoundLinEvent n compound b init e') from
    Event.contradiction_of_reflexive_ordered_before n (h e hcycle)
  intro e' hpath
  induction hpath with
  | single hstep => exact step_advances_compoundLin hstep
  | tail _ hstep ih => exact Trans.trans ih (step_advances_compoundLin hstep)

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' hknow

/-! ## PartialOrder (consequence of acyclicity)

Once acyclicity is established, the PartialOrder follows:
- lt = TransGen (PPOi ∪ com)
- le = (· = ·) ∨ TransGen (PPOi ∪ com)
- Antisymmetry from acyclicity
- Transitivity from TransGen
- Reflexivity from = -/

/-- The PartialOrder on events (GMO): constructed from cmcm_acyclic.
    le = (· = ·) ∨ TransGen (PPOi ∪ com)
    lt = TransGen (PPOi ∪ com)
    Antisymmetry from acyclicity. Transitivity from TransGen. -/
noncomputable def eventPartialOrder
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : PartialOrder (Event n) := by
  have _hacyclic := @cmcm_acyclic n compound b init hknow
  sorry

end Herd
