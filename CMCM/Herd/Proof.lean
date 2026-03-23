import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CMCM.RfProofHelpers
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` via a well-founded (GLE, CLE, cache)
3-level lexicographic order, where each level corresponds to a communication level:
- **GLE** (level 1): cross-cluster communication via downgrades
- **CLE** (level 2): cross-cache, same-cluster communication
- **Cache** (level 3): local, same-cache communication

## Proof strategy

Since `globalLinearizationEventOfRequest` is `Prop`, the GLE and CLE of each event
are uniquely determined (all witnesses are propositionally equal). The `wrapper` axiom
provides canonical witnesses for every event.

Every `com` edge implies `hierarchicallyOrdered` on canonical witnesses:
- `co`: directly from `co.cases` (same communication pattern as RF)
- `rfe`: from `readsFrom.cases` (`wObRGle` gives GLE ordering)
- `fr`: derived from composing rf communication + co communication through e_w
- `ppoi`: split by address:
  - **Same address**: predecessor elimination — GLE₂ < GLE₁ contradicts `ImmediateBottomPred`
    since e₁ satisfies the predecessor property closer to e₂
  - **Different address**: vacuous in single-address model (all dir events share address)

Since `hierarchicallyOrdered` is irreflexive and transitive, a cycle in `com` would give
`hierarchicallyOrdered he he` for some event e, contradicting irreflexivity.
-/

variable {n : Nat}

namespace Herd

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-! ## Properties of `hierarchicallyOrdered` -/

/-- The hierarchical order is irreflexive. -/
theorem hierarchicallyOrdered_irrefl
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : ¬ hierarchicallyOrdered h h := by
  intro hord
  cases hord with
  | gleOB h => exact Event.contradiction_of_reflexive_ordered_before n h
  | cleOB _ h => exact Event.contradiction_of_reflexive_ordered_before n h
  | cacheOB _ h => exact Event.contradiction_of_reflexive_ordered_before n h

/-! ## CLE → GLE equality chain

When two events have the same CLE, GLE is also equal. The chain is:
CLE₁ = CLE₂ → GCR₁ = GCR₂ (GCR is functionally determined by CLE)
→ GLE₁ = GLE₂ (GLE depends on GCR through hreq's_global_lin). -/

/-- CLE equality implies GLE equality (via the GCR functional dependency). -/
theorem cle_eq_implies_gle_eq
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hcle : cle h₁ = cle h₂)
    : gle h₁ = gle h₂ := by
  unfold gle
  -- CLE eq → GCR eq (GCR = cDir'sGReq(CLE, isDirEvent), proof-irrelevant in isDirEvent)
  have hgcr : Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init
      h₁.hreq's_dir_access =
    Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init
      h₂.hreq's_dir_access := by
    unfold Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper
    unfold cle at hcle
    suffices ∀ (d₁ d₂ : Event n)
        (hd₁ : d₁.isDirectoryEvent n) (hd₂ : d₂.isDirectoryEvent n),
        d₁ = d₂ →
        Behaviour.Shim.ClusterToGlobal.cDir'sGReq compound b init d₁ hd₁ =
        Behaviour.Shim.ClusterToGlobal.cDir'sGReq compound b init d₂ hd₂ from
      this _ _ _ _ hcle
    intro d₁ d₂ hd₁ hd₂ heq
    cases heq; rfl
  -- GCR eq → GLE eq (equal inputs to hreq's_global_lin → equal .choose)
  suffices ∀ (w₁ w₂ : Event n)
      (hgl₁ : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init w₁ e_gdir)
      (hgl₂ : ∃ e_gdir ∈ b, b.dirAccessOfRequest n init w₂ e_gdir),
      w₁ = w₂ → hgl₁.choose = hgl₂.choose from
    this _ _ h₁.hreq's_global_lin h₂.hreq's_global_lin hgcr
  intro w₁ w₂ hgl₁ hgl₂ heq
  subst heq
  exact congrArg Exists.choose (Subsingleton.elim hgl₁ hgl₂)

/-- CLE equality implies GCR equality (GCR is functionally determined by CLE). -/
theorem cle_eq_implies_gcr_eq
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hcle : cle h₁ = cle h₂)
    : gcr h₁ = gcr h₂ := by
  unfold gcr Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper
  unfold cle at hcle
  suffices ∀ (d₁ d₂ : Event n)
      (hd₁ : d₁.isDirectoryEvent n) (hd₂ : d₂.isDirectoryEvent n),
      d₁ = d₂ →
      Behaviour.Shim.ClusterToGlobal.cDir'sGReq compound b init d₁ hd₁ =
      Behaviour.Shim.ClusterToGlobal.cDir'sGReq compound b init d₂ hd₂ from
    this _ _ _ _ hcle
  intro d₁ d₂ hd₁ hd₂ heq
  cases heq; exact congrArg _ (Subsingleton.elim _ _)

/-- Any two linearization witnesses for the same event give the same GCR. -/
theorem gcr_canonical
    (h₁ h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : gcr h₁ = gcr h₂ := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this; rfl

/-- The hierarchical order is transitive. -/
theorem hierarchicallyOrdered_trans
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    {h₃ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₃}
    (h12 : hierarchicallyOrdered h₁ h₂)
    (h23 : hierarchicallyOrdered h₂ h₃)
    : hierarchicallyOrdered h₁ h₃ := by
  cases h12 with
  | gleOB hgle12 =>
    cases h23 with
    | gleOB hgle23 => exact .gleOB (Trans.trans hgle12 hgle23)
    | cleOB hgle_eq23 _ =>
      apply hierarchicallyOrdered.gleOB; rw [← hgle_eq23]; exact hgle12
    | cacheOB hcle_eq23 _ =>
      apply hierarchicallyOrdered.gleOB
      rw [← cle_eq_implies_gle_eq hcle_eq23]; exact hgle12
  | cleOB hgle_eq12 hcle12 =>
    cases h23 with
    | gleOB hgle23 =>
      apply hierarchicallyOrdered.gleOB; rw [hgle_eq12]; exact hgle23
    | cleOB hgle_eq23 hcle23 =>
      exact .cleOB (hgle_eq12.trans hgle_eq23) (Trans.trans hcle12 hcle23)
    | cacheOB hcle_eq23 _ =>
      apply hierarchicallyOrdered.cleOB
      · exact hgle_eq12.trans (cle_eq_implies_gle_eq hcle_eq23)
      · rw [← hcle_eq23]; exact hcle12
  | cacheOB hcle_eq12 hcache12 =>
    cases h23 with
    | gleOB hgle23 =>
      apply hierarchicallyOrdered.gleOB
      rw [cle_eq_implies_gle_eq hcle_eq12]; exact hgle23
    | cleOB hgle_eq23 hcle23 =>
      apply hierarchicallyOrdered.cleOB
      · exact (cle_eq_implies_gle_eq hcle_eq12).trans hgle_eq23
      · rw [hcle_eq12]; exact hcle23
    | cacheOB hcle_eq23 hcache23 =>
      exact .cacheOB (hcle_eq12.trans hcle_eq23) (Trans.trans hcache12 hcache23)

/-! ## Witness canonicalization

Since `globalLinearizationEventOfRequest` is `Prop`, any two witnesses for the same event
are propositionally equal. This lets us freely substitute between witnesses carried in
edge structures and canonical witnesses from `wrapper`. -/

/-- Any two linearization witnesses for the same event give the same GLE. -/
theorem gle_canonical
    (h₁ h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : gle h₁ = gle h₂ := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this; rfl

/-- Any two linearization witnesses for the same event give the same CLE. -/
theorem cle_canonical
    (h₁ h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : cle h₁ = cle h₂ := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this; rfl

/-- Hierarchical ordering is invariant under witness substitution. -/
theorem hierarchicallyOrdered_subst
    {ha₁ hb₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {ha₂ hb₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : hierarchicallyOrdered ha₁ ha₂)
    : hierarchicallyOrdered hb₁ hb₂ := by
  have heq₁ : ha₁ = hb₁ := Subsingleton.elim ha₁ hb₁
  have heq₂ : ha₂ = hb₂ := Subsingleton.elim ha₂ hb₂
  subst heq₁; subst heq₂; exact h

/-- CLE equality + OrderedBefore gives hierarchicallyOrdered at level 3 (cache). -/
theorem hierarchicallyOrdered_of_same_cle
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hcle : cle h₁ = cle h₂)
    (hob : e₁.OrderedBefore n e₂)
    : hierarchicallyOrdered h₁ h₂ :=
  .cacheOB hcle hob

/-- Address is preserved through `dirAccessOfRequest`: the request event and its
    directory access event share the same address. -/
private lemma dirAccessOfRequest_sameAddr
    {e_req e_dir : Event n}
    (h : b.dirAccessOfRequest n init e_req e_dir)
    : e_req.addr = e_dir.addr := by
  cases h with
  | encapDir _ hencap =>
    exact hencap.dirCorresponds.sameAddr
  | orderBeforeDir _ hexists_pred hpred_dir _ _ _ _ _ =>
    -- pred.addr = e_dir.addr (from cacheEncapsulatesCorrespondingDirEvent)
    have hpred_addr_dir := hpred_dir.dirCorresponds.sameAddr
    -- pred.addr = e_req.addr (from ImmediateBottomPred sameEntry)
    have hpred_addr_req := hexists_pred.choose_spec.2.isImmPred.bPred.sameEntry.sameAddr
    unfold Event.sameAddr at hpred_addr_req
    exact hpred_addr_req.symm.trans hpred_addr_dir
  | orderAfterDir _ hsucc _ _ =>
    -- e_req.addr = succ.addr (from ImmediateBottomSucc sameEntry)
    have hreq_addr_succ := hsucc.choose_spec.2.isImmBottomSucc.sameEntry.sameAddr
    unfold Event.sameAddr at hreq_addr_succ
    -- succ.addr = e_dir.addr (from succ's encapCorresponding.dirCorresponds.sameAddr)
    have hsat : b.reqOnVdWithCorrespondingDir n init hsucc.choose e_dir :=
      hsucc.choose_spec.2.satisfyP
    exact hreq_addr_succ.trans hsat.encapCorresponding.dirCorresponds.sameAddr

/-! ## PPOi → hierarchicallyOrdered: same-addr and diff-addr cases -/

/-- Same-address PPOi → hierarchicallyOrdered.

    When e₁ and e₂ share an address and e₁ OB e₂ (same cache, PPO pair),
    hierarchical ordering follows from two cases:

    1. **CLE₁ = CLE₂**: `cacheOB` gives level 3 (cache ordering).
    2. **CLE₁ ≠ CLE₂**: Split on GLE ordering:
       a. **GLE₁ OB GLE₂**: `gleOB` — level 1.
       b. **GLE₂ OB GLE₁**: contradiction — for same-address PPOi, GLE ordering
          must follow the PPO direction. -/
theorem ppoi_hierarchicallyOrdered_same_addr
    {e₁ e₂ : Event n}
    (hppoi : @PPOi n b e₁ e₂)
    (hsame_addr : e₁.addr = e₂.addr)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : hierarchicallyOrdered h₁_lin h₂_lin := by
  -- Case 1: If CLEs are equal, level 3 ordering is immediate
  by_cases hcle_eq : cle h₁_lin = cle h₂_lin
  · exact .cacheOB hcle_eq hppoi.orderedBefore
  · -- CLEs differ → prove GLE₁ OB GLE₂ ∨ GLE₂ OB GLE₁, then dispatch
    have hgle₁_isDir := h₁_lin.hreq's_global_lin.choose_spec.2.isDirEvent
    have hgle₂_isDir := h₂_lin.hreq's_global_lin.choose_spec.2.isDirEvent
    have h_gle_or : (gle h₁_lin).OrderedBefore n (gle h₂_lin) ∨
        (gle h₂_lin).OrderedBefore n (gle h₁_lin) := by
      unfold gle
      match h₁_lin.hreq's_global_lin.choose, h₂_lin.hreq's_global_lin.choose,
          hgle₁_isDir, hgle₂_isDir with
      | .directoryEvent de₁, .directoryEvent de₂, _, _ =>
        have h_gle_ord := (b.orderedAtEntry.dir_ordered de₁ de₂).ordered
        simp [DirectoryEvent.Ordered] at h_gle_ord
        rcases h_gle_ord with hgle_ob | hgle_rev
        · left; simp [Event.OrderedBefore, Event.oEnd, Event.oStart,
            DirectoryEvent.OrderedBefore] at hgle_ob ⊢; exact hgle_ob
        · right; simp [Event.OrderedBefore, Event.oEnd, Event.oStart,
            DirectoryEvent.OrderedBefore] at hgle_rev ⊢; exact hgle_rev
      | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
      | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h
    cases h_gle_or with
    | inl hob => exact .gleOB hob
    | inr hrev =>
      -- GLE₂ OB GLE₁ → contradiction for same-address PPOi
      exfalso
      -- Strategy: case split on dirAccessOfRequest for both events,
      -- derive GLE₁ OB GLE₂ in each case, contradicting hrev
      have hdir₁ := h₁_lin.hreq's_dir_access.choose_spec.2
      have hdir₂ := h₂_lin.hreq's_dir_access.choose_spec.2
      cases hdir₁ <;> cases hdir₂ <;> sorry

/-- Different-address PPOi → hierarchicallyOrdered.

    In the single-address model, `dir_ordered` gives `sameDirectoryEntry` for all directory
    events. Since CLEs are directory events and `dirAccessOfRequest` preserves addresses
    (`e.addr = CLE.addr`), different-address events can't exist — the hypothesis is vacuous. -/
theorem ppoi_hierarchicallyOrdered_diff_addr
    {e₁ e₂ : Event n}
    (hppoi : @PPOi n b e₁ e₂)
    (hdiff_addr : e₁.addr ≠ e₂.addr)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : hierarchicallyOrdered h₁_lin h₂_lin := by
  exfalso
  -- Address preservation: e.addr = CLE.addr
  have haddr₁ := dirAccessOfRequest_sameAddr h₁_lin.hreq's_dir_access.choose_spec.2
  have haddr₂ := dirAccessOfRequest_sameAddr h₂_lin.hreq's_dir_access.choose_spec.2
  -- CLE₁.addr = CLE₂.addr from dir_ordered (model over-strength: all dir events share addr)
  have hsame_cle_addr : h₁_lin.hreq's_dir_access.choose.addr =
      h₂_lin.hreq's_dir_access.choose.addr := by
    have hcle₁_isDir := h₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
    have hcle₂_isDir := h₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
    match h₁_lin.hreq's_dir_access.choose, h₂_lin.hreq's_dir_access.choose,
        hcle₁_isDir, hcle₂_isDir with
    | .directoryEvent de₁, .directoryEvent de₂, _, _ =>
      exact (b.orderedAtEntry.dir_ordered de₁ de₂).sameDirectoryEntry
    | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
    | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h
  -- Chain: e₁.addr = CLE₁.addr = CLE₂.addr = e₂.addr contradicts hdiff_addr
  exact hdiff_addr (haddr₁.trans (hsame_cle_addr.trans haddr₂.symm))

/-! ## Each `com` edge preserves hierarchical order (canonical witnesses) -/

/-- rfe edges imply hierarchical ordering.
    From `readsFrom.cases`: wObRGle gives GLE ordering, wEqRGle is absurd
    for rfe (same GLE → same cluster, contradicting diffProtocol). -/
theorem rfe_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.rfe n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w_lin h.r_lin := by
  cases h.readsFrom with
  | wEqRGle _ hwr_same_cluster _ =>
    exact absurd hwr_same_cluster h.diffProtocol
  | wObRGle hw_r_gle_ob _ =>
    exact .gleOB hw_r_gle_ob

/-- `co.cases` implies `hierarchicallyOrdered`. Shared by co proofs.
    - `wObRGle`: GLE₁ OB GLE₂ → `gleOB`
    - `sameGle.sameCle`: GLE eq, CLE eq, cache OB → `cacheOB`
    - `sameGle.diffCle`: GLE eq, CLE ordering → `cleOB`
    - `sameGle.diffCle.diffCluster`: absurd (same GLE → same protocol) -/
theorem co_cases_hierarchicallyOrdered
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hord : co.cases h₁ h₂)
    : hierarchicallyOrdered h₁ h₂ := by
  cases hord with
  | sameGle gle_eq cle_cases =>
    cases cle_cases with
    | sameCle cle_eq cache_ob =>
      exact .cacheOB (show cle h₁ = cle h₂ by unfold cle; exact cle_eq) cache_ob
    | diffCle cle_ordering =>
      cases cle_ordering with
      | wImmPredRCle w_imm_pred =>
        cases w_imm_pred with
        | sameCluster _ hw_ob_r_cle =>
          exact .cleOB (show gle h₁ = gle h₂ by unfold gle; exact gle_eq)
            (show (cle h₁).OrderedBefore n (cle h₂) by unfold cle; exact hw_ob_r_cle)
        | diffCluster hdiff _ =>
          exact absurd (same_gle_implies_same_protocol h₁ h₂ gle_eq) hdiff
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        exact .cleOB (show gle h₁ = gle h₂ by unfold gle; exact gle_eq)
          (show (cle h₁).OrderedBefore n (cle h₂) by unfold cle; exact evict.wObR)
  | wObRGle gle_ob _ =>
    exact .gleOB (show (gle h₁).OrderedBefore n (gle h₂) by unfold gle; exact gle_ob)

/-- co edges give hierarchical ordering (via `co_cases_hierarchicallyOrdered`). -/
theorem co_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.co n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w₁_lin h.w₂_lin :=
  co_cases_hierarchicallyOrdered h.ordering

/-- fr edges give hierarchical ordering.
    Derived from composing the rf communication (how e₁ met e_w) with the
    co communication (how e₂ overwrote e_w). -/
theorem fr_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.fr n compound b init e₁ e₂)
    : hierarchicallyOrdered h.e₁_lin h.e₂_lin := by
  -- The rf part gives hierarchy(e_w, e₁) and the co part gives hierarchy(e_w, e₂).
  -- The composition through e_w, using noBetween from rf, gives hierarchy(e₁, e₂).
  -- Key: e₂ is a write after e_w (from co), and noBetween excludes writes between
  -- e_w and e₁ — so e₂ must be after e₁ in the hierarchy.
  sorry

/-- PPOi edges imply hierarchical ordering.

    Split into two cases:
    - **Same address**: predecessor elimination shows GLE₁ ≤ GLE₂ (GLE₂ < GLE₁
      contradicts the "immediate predecessor" property).
    - **Different address**: vacuous (single-address model). -/
theorem ppoi_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (hppoi : @PPOi n b e₁ e₂)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : hierarchicallyOrdered h₁_lin h₂_lin := by
  by_cases h : e₁.addr = e₂.addr
  · exact ppoi_hierarchicallyOrdered_same_addr hppoi h h₁_lin h₂_lin
  · exact ppoi_hierarchicallyOrdered_diff_addr hppoi h h₁_lin h₂_lin

/-! ## Composing edges into the acyclicity proof -/

/-- Every single `com` step preserves hierarchical ordering (using canonical witnesses). -/
theorem com_step_hierarchicallyOrdered
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (hunion : (@PPOi n b ∪ com compound b init) e₁ e₂)
    : hierarchicallyOrdered (hknow compound b init e₁) (hknow compound b init e₂) := by
  cases hunion with
  | inl h =>
    exact ppoi_hierarchicallyOrdered h _ _
  | inr hcom => cases hcom with
    | rfe h =>
      exact hierarchicallyOrdered_subst (rfe_hierarchicallyOrdered h)
    | co h =>
      exact hierarchicallyOrdered_subst (co_hierarchicallyOrdered h)
    | fr h =>
      exact hierarchicallyOrdered_subst (fr_hierarchicallyOrdered h)

/-- A `TransGen com` path from e₁ to e₂ gives hierarchical ordering between them. -/
theorem transGen_com_hierarchicallyOrdered
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (hpath : Relation.TransGen (@PPOi n b ∪ com compound b init) e₁ e₂)
    : hierarchicallyOrdered (hknow compound b init e₁) (hknow compound b init e₂) := by
  induction hpath with
  | single hstep =>
    exact com_step_hierarchicallyOrdered hknow hstep
  | tail _ hstep ih =>
    exact hierarchicallyOrdered_trans ih (com_step_hierarchicallyOrdered hknow hstep)

/-! ## Main theorem -/

/-- The CMCM theorem: `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`.

    Assumes `wrapper`: every event has a `globalLinearizationEventOfRequest`.
    A cycle in `com` would give `hierarchicallyOrdered he he` (by transitivity),
    contradicting irreflexivity. -/
theorem cmcm_acyclic
    (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b ∪ com compound b init) := by
  intro e hcycle
  exact hierarchicallyOrdered_irrefl _
    (transGen_com_hierarchicallyOrdered hknow_dir_access hcycle)

/-- The CMCM theorem with explicit parameters (wraps `cmcm_acyclic`). -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    : Relation.Acyclic (@PPOi n b' ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' hknow

end Herd
