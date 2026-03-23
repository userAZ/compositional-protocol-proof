import CMCM.Herd.Relations
import CMCM.Herd.RelationCycles
import CompositionalProtocolProof.CompoundPPOs

/-!
# CMCM Acyclicity Proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` via a well-founded (GLE, CLE, cache)
3-level lexicographic order.

## Proof strategy

Since `globalLinearizationEventOfRequest` is `Prop`, the GLE and CLE of each event
are uniquely determined (all witnesses are propositionally equal). The `wrapper` axiom
provides canonical witnesses for every event.

Every `com` edge implies `hierarchicallyOrdered` on canonical witnesses:
- `co`: directly from definition (witnesses are propositionally equal to canonical)
- `rfe`: from `readsFrom.cases` (GLE ordering via `wObRGle`)
- `fr`: from the fr structure (carries hierarchicallyOrdered directly)
- `ppoi`: split by address:
  - **Same address**: predecessor elimination — GLE₂ < GLE₁ contradicts `ImmediateBottomPred`
    since e₁ satisfies the predecessor property closer to e₂
  - **Different address**: `CompoundLinearizationOrder` (proven in CompoundPPOs.lean) gives
    CLE-level ordering; a GMO bridge lemma converts to `hierarchicallyOrdered`

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
  simp only [hierarchicallyOrdered, gleOrderedBefore] at hord
  rcases hord with hgle | ⟨_, hgcr | ⟨_, hcle | ⟨_, hcache⟩⟩⟩
  · exact Event.contradiction_of_reflexive_ordered_before n hgle
  · exact Event.contradiction_of_reflexive_ordered_before n hgcr
  · exact Event.contradiction_of_reflexive_ordered_before n hcle
  · exact Event.contradiction_of_reflexive_ordered_before n hcache

/-- The hierarchical order is transitive. -/
theorem hierarchicallyOrdered_trans
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    {h₃ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₃}
    (h12 : hierarchicallyOrdered h₁ h₂)
    (h23 : hierarchicallyOrdered h₂ h₃)
    : hierarchicallyOrdered h₁ h₃ := by
  simp only [hierarchicallyOrdered, gleOrderedBefore] at *
  -- Level 1: GLE
  rcases h12 with hgle12 | ⟨hgle_eq12, hsub12⟩
  · rcases h23 with hgle23 | ⟨hgle_eq23, _⟩
    · exact Or.inl (Trans.trans hgle12 hgle23)
    · rw [← hgle_eq23]; exact Or.inl hgle12
  · rcases h23 with hgle23 | ⟨hgle_eq23, hsub23⟩
    · rw [hgle_eq12]; exact Or.inl hgle23
    · refine Or.inr ⟨hgle_eq12.trans hgle_eq23, ?_⟩
      -- Level 2: GCR
      rcases hsub12 with hgcr12 | ⟨hgcr_eq12, hsub12'⟩
      · rcases hsub23 with hgcr23 | ⟨hgcr_eq23, _⟩
        · exact Or.inl (Trans.trans hgcr12 hgcr23)
        · rw [← hgcr_eq23]; exact Or.inl hgcr12
      · rcases hsub23 with hgcr23 | ⟨hgcr_eq23, hsub23'⟩
        · rw [hgcr_eq12]; exact Or.inl hgcr23
        · refine Or.inr ⟨hgcr_eq12.trans hgcr_eq23, ?_⟩
          -- Level 3: CLE
          rcases hsub12' with hcle12 | ⟨hcle_eq12, hcache12⟩
          · rcases hsub23' with hcle23 | ⟨hcle_eq23, _⟩
            · exact Or.inl (Trans.trans hcle12 hcle23)
            · rw [← hcle_eq23]; exact Or.inl hcle12
          · rcases hsub23' with hcle23 | ⟨hcle_eq23, hcache23⟩
            · rw [hcle_eq12]; exact Or.inl hcle23
            · -- Level 4: cache event
              exact Or.inr ⟨hcle_eq12.trans hcle_eq23, Trans.trans hcache12 hcache23⟩

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

/-- CLE equality + OrderedBefore gives hierarchicallyOrdered at level 4 (cache). -/
theorem hierarchicallyOrdered_of_same_cle
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hcle : cle h₁ = cle h₂)
    (hob : e₁.OrderedBefore n e₂)
    : hierarchicallyOrdered h₁ h₂ := by
  have hgle := cle_eq_implies_gle_eq hcle
  have hgcr := cle_eq_implies_gcr_eq hcle
  exact Or.inr ⟨hgle, Or.inr ⟨hgcr, Or.inr ⟨hcle, hob⟩⟩⟩

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

    1. **CLE₁ = CLE₂**: `hierarchicallyOrdered_of_same_cle` gives level 3 (cache ordering).
    2. **CLE₁ ≠ CLE₂**: Split on GLE ordering:
       a. **GLE₁ OB GLE₂**: level 1 (GLE ordering) — works regardless of CLE direction.
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
  · exact hierarchicallyOrdered_of_same_cle hcle_eq hppoi.orderedBefore
  · -- CLEs differ → GLE ordering determines the result
    show hierarchicallyOrdered h₁_lin h₂_lin
    unfold hierarchicallyOrdered gleOrderedBefore gle
    have hgle₁_isDir := h₁_lin.hreq's_global_lin.choose_spec.2.isDirEvent
    have hgle₂_isDir := h₂_lin.hreq's_global_lin.choose_spec.2.isDirEvent
    match h₁_lin.hreq's_global_lin.choose, h₂_lin.hreq's_global_lin.choose,
        hgle₁_isDir, hgle₂_isDir with
    | .directoryEvent de₁, .directoryEvent de₂, _, _ =>
      have h_gle_ord := (b.orderedAtEntry.dir_ordered de₁ de₂).ordered
      simp [DirectoryEvent.Ordered] at h_gle_ord
      rcases h_gle_ord with hgle_ob | hgle_rev
      · -- GLE₁ OB GLE₂ → level 1
        left
        simp only [Event.OrderedBefore, Event.oEnd, Event.oStart]
        simp only [DirectoryEvent.OrderedBefore] at hgle_ob
        exact hgle_ob
      · -- GLE₂ OB GLE₁ → contradiction for same-address PPOi
        exfalso
        simp only [DirectoryEvent.OrderedBefore] at hgle_rev
        -- hgle_rev : de₂.oEnd < de₁.oStart
        -- Strategy: case split on dirAccessOfRequest, derive GLE₁.oEnd < GLE₂.oStart,
        -- combine with hgle_rev and well-formedness for contradiction
        have hdir₁ := h₁_lin.hreq's_dir_access.choose_spec.2
        have hdir₂ := h₂_lin.hreq's_dir_access.choose_spec.2
        cases hdir₁ with
        | encapDir hmissing₁ hencap₁ =>
          cases hdir₂ with
          | encapDir hmissing₂ hencap₂ =>
            -- e₁ encap CLE₁, e₂ encap CLE₂, e₁ OB e₂
            -- → CLE₁ OB CLE₂ → chain through shim to GLE₁ OB GLE₂ → contradiction
            have he₁_encap_cle₁ := hencap₁.reqEncapDir
            have he₂_encap_cle₂ := hencap₂.reqEncapDir
            -- CLE₁ OB CLE₂ via: CLE₁ EncapsulatedBy e₁, e₁ OB e₂, e₂ Encapsulates CLE₂
            have hcle_ob : (h₁_lin.hreq's_dir_access.choose).OrderedBefore n
                (h₂_lin.hreq's_dir_access.choose) :=
              calc (h₁_lin.hreq's_dir_access.choose).EncapsulatedBy n e₁ := he₁_encap_cle₁
                e₁.OrderedBefore n e₂ := hppoi.orderedBefore
                e₂.Encapsulates n (h₂_lin.hreq's_dir_access.choose) := he₂_encap_cle₂
            -- Chain through shim: CLE₁ OB CLE₂ → GCR₁ OB/= GCR₂ → GLE₁ OB/= GLE₂
            -- Combined with GLE₂ OB GLE₁ (hgle_rev), derive contradiction
            sorry
          | orderBeforeDir _ _ _ _ _ _ _ _ => sorry
          | orderAfterDir _ _ _ _ => sorry
        | orderBeforeDir _ _ _ _ _ _ _ _ =>
          cases hdir₂ with
          | encapDir _ _ => sorry
          | orderBeforeDir _ _ _ _ _ _ _ _ => sorry
          | orderAfterDir _ _ _ _ => sorry
        | orderAfterDir _ _ _ _ =>
          cases hdir₂ with
          | encapDir _ _ => sorry
          | orderBeforeDir _ _ _ _ _ _ _ _ => sorry
          | orderAfterDir _ _ _ _ => sorry
    | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
    | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h

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
    From `readsFrom.cases`: wObRGle gives GLE ordering, wEqRGle gives same GLE + CLE ordering. -/
theorem rfe_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.rfe n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w_lin h.r_lin := by
  simp only [hierarchicallyOrdered, gleOrderedBefore]
  cases h.readsFrom with
  | wEqRGle _ hwr_same_cluster _ =>
    exact absurd hwr_same_cluster h.diffProtocol
  | wObRGle hw_r_gle_ob _ =>
    exact Or.inl hw_r_gle_ob

/-- co edges give hierarchical ordering.
    From `gleOrdering.Cases` (via Nonempty):
    - `wObRGle`: GLE₁ OB GLE₂ → level 1 of hierarchicallyOrdered
    - `sameGle`: same GLE with CLE sub-cases → needs CLE→hierarchy bridge -/
theorem co_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.co n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w₁_lin h.w₂_lin := by
  sorry

/-- fr edges give hierarchical ordering.
    Composed from rf⁻¹ (readsFrom.cases) and co (gleOrdering.Cases) on the
    intermediate write e_w. -/
theorem fr_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.fr n compound b init e₁ e₂)
    : hierarchicallyOrdered h.e₁_lin h.e₂_lin := by
  sorry

/-- PPOi edges imply hierarchical ordering.

    Split into two cases:
    - **Same address**: predecessor elimination shows GLE₁ ≤ GLE₂ (GLE₂ < GLE₁
      contradicts the "immediate predecessor" property).
    - **Different address**: `CompoundLinearizationOrder` (already proven) gives
      CLE-level ordering; the GMO bridge converts to hierarchicallyOrdered. -/
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
    (hunion : (PPOi ∪ com compound b init) e₁ e₂)
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
    (hpath : Relation.TransGen (PPOi ∪ com compound b init) e₁ e₂)
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
    : Relation.Acyclic (PPOi ∪ com compound b init) := by
  intro e hcycle
  exact hierarchicallyOrdered_irrefl _
    (transGen_com_hierarchicallyOrdered hknow_dir_access hcycle)

instance : PartialOrder (Event n) := sorry

theorem cmcm (cmp : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) :
  Relation.Acyclic (PPOi ∪ com cmp b init) := by
  apply CMCM.suffices_inclusion
  · case hppo => sorry -- This should be the original main theorem
  · case hcom => sorry -- This should be the Rf stuff.

end Herd
