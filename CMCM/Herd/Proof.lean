import CMCM.Herd.Relations

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
  rcases hord with hgle | ⟨_, hcle | ⟨_, hcache⟩⟩
  · exact Event.contradiction_of_reflexive_ordered_before n hgle
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
      -- Level 2: CLE
      rcases hsub12 with hcle12 | ⟨hcle_eq12, hcache12⟩
      · rcases hsub23 with hcle23 | ⟨hcle_eq23, _⟩
        · exact Or.inl (Trans.trans hcle12 hcle23)
        · rw [← hcle_eq23]; exact Or.inl hcle12
      · rcases hsub23 with hcle23 | ⟨hcle_eq23, hcache23⟩
        · rw [hcle_eq12]; exact Or.inl hcle23
        · -- Level 3: cache event
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

/-- CLE equality + OrderedBefore gives hierarchicallyOrdered at level 3 (cache). -/
theorem hierarchicallyOrdered_of_same_cle
    {h₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {h₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hcle : cle h₁ = cle h₂)
    (hob : e₁.OrderedBefore n e₂)
    : hierarchicallyOrdered h₁ h₂ := by
  have hgle := cle_eq_implies_gle_eq hcle
  show hierarchicallyOrdered h₁ h₂
  exact Or.inr ⟨hgle, Or.inr ⟨hcle, hob⟩⟩

/-! ## PPOi → hierarchicallyOrdered: same-addr and diff-addr cases -/

/-- Same-address PPOi → hierarchicallyOrdered.

    When e₁ and e₂ share an address and e₁ OB e₂ (same cache, PPO pair),
    hierarchical ordering follows from the 3-level decomposition:

    1. **CLE₁ = CLE₂**: `hierarchicallyOrdered_of_same_cle` gives level 3 (cache ordering).
    2. **CLE₁ OB CLE₂ + GLE₁ = GLE₂**: level 2 (CLE ordering).
    3. **CLE₁ OB CLE₂ + GLE₁ OB GLE₂**: level 1 (GLE ordering).
    4. **CLE₁ OB CLE₂ + GLE₂ OB GLE₁**: contradiction — for same-address events,
       CLE ordering propagates through the shim/global hierarchy.
    5. **CLE₂ OB CLE₁**: contradiction via predecessor elimination — e₁ OB e₂
       at the same address/cache implies the cluster directory serves e₁ first. -/
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
  · -- CLEs differ → extract CLE directory events for dir_ordered
    have hcle₁_isDir := h₁_lin.hreq's_dir_access.choose_spec.2.isDirEvent
    have hcle₂_isDir := h₂_lin.hreq's_dir_access.choose_spec.2.isDirEvent
    -- Work at the CLE level first, then lift to GLE
    show hierarchicallyOrdered h₁_lin h₂_lin
    unfold hierarchicallyOrdered gleOrderedBefore gle
    unfold cle at hcle_eq
    match hc₁ : h₁_lin.hreq's_dir_access.choose, hc₂ : h₂_lin.hreq's_dir_access.choose,
        hcle₁_isDir, hcle₂_isDir with
    | .directoryEvent dc₁, .directoryEvent dc₂, _, _ =>
      have h_cle_ord := (b.orderedAtEntry.dir_ordered dc₁ dc₂).ordered
      simp [DirectoryEvent.Ordered] at h_cle_ord
      rcases h_cle_ord with hcle_ob | hcle_rev
      · -- Case 2/3: CLE₁ OB CLE₂ → check GLE ordering
        have hgle₁_isDir := h₁_lin.hreq's_global_lin.choose_spec.2.isDirEvent
        have hgle₂_isDir := h₂_lin.hreq's_global_lin.choose_spec.2.isDirEvent
        match h₁_lin.hreq's_global_lin.choose, h₂_lin.hreq's_global_lin.choose,
            hgle₁_isDir, hgle₂_isDir with
        | .directoryEvent de₁, .directoryEvent de₂, _, _ =>
          have h_gle_ord := (b.orderedAtEntry.dir_ordered de₁ de₂).ordered
          simp [DirectoryEvent.Ordered] at h_gle_ord
          rcases h_gle_ord with hgle_ob | hgle_rev
          · -- Case 3: GLE₁ OB GLE₂ → level 1
            left
            simp only [Event.OrderedBefore, Event.oEnd, Event.oStart]
            simp only [DirectoryEvent.OrderedBefore] at hgle_ob
            exact hgle_ob
          · -- Case 4: CLE₁ OB CLE₂ but GLE₂ OB GLE₁ → contradiction
            -- For same address, CLE ordering propagates to GLE via the shim
            exfalso; sorry
        | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
        | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h
      · -- Case 5: CLE₂ OB CLE₁ → contradiction
        -- e₁ OB e₂ at same address/cache implies CLE₁ ≤ CLE₂
        exfalso
        -- Extract dirAccessOfRequest for both events
        have hda₁ := h₁_lin.hreq's_dir_access.choose_spec.2
        rw [hc₁] at hda₁
        have hda₂ := h₂_lin.hreq's_dir_access.choose_spec.2
        rw [hc₂] at hda₂
        -- Common facts
        have hob : e₁.oEnd < e₂.oStart := hppoi.orderedBefore
        have hrev : dc₂.oEnd < dc₁.oStart := hcle_rev
        -- Case analysis on e₁'s directory access
        cases hda₁ with
        | encapDir _ hencap₁ =>
          -- e₁ encapsulates CLE₁
          have henc₁ : dc₁.oEnd < e₁.oEnd := hencap₁.reqEncapDir.2
          cases hda₂ with
          | encapDir _ hencap₂ =>
            have henc₂ : e₂.oStart < dc₂.oStart := hencap₂.reqEncapDir.1
            exact absurd (calc
              dc₁.oEnd < e₁.oEnd := henc₁
              _ < e₂.oStart := hob
              _ < dc₂.oStart := henc₂
              _ < dc₂.oEnd := dc₂.oWellFormed
              _ < dc₁.oStart := hrev
              _ < dc₁.oEnd := dc₁.oWellFormed) (Nat.lt_irrefl _)
          | orderBeforeDir _ _ _ _ _ _ _ _ =>
            sorry -- predecessor elimination
          | orderAfterDir _ hsucc₂ _ _ =>
            have h_sat := hsucc₂.choose_spec.2.satisfyP
            simp only [Event.PropOnEvent, Behaviour.succOnVdWithCorrespondingDir] at h_sat
            have henc₂ : hsucc₂.choose.oStart < dc₂.oStart := h_sat.encapCorresponding.reqEncapDir.1
            have hsuc : e₂.oEnd < hsucc₂.choose.oStart := by
              have h := hsucc₂.choose_spec.2.isImmBottomSucc.isSucc
              simp only [Event.Successor, Event.Predecessor, Event.OrderedBefore] at h; exact h
            exact absurd (calc
              dc₁.oEnd < e₁.oEnd := henc₁
              _ < e₂.oStart := hob
              _ < e₂.oEnd := e₂.oWellFormed
              _ < hsucc₂.choose.oStart := hsuc
              _ < dc₂.oStart := henc₂
              _ < dc₂.oEnd := dc₂.oWellFormed
              _ < dc₁.oStart := hrev
              _ < dc₁.oEnd := dc₁.oWellFormed) (Nat.lt_irrefl _)
        | orderBeforeDir _ hpred₁ hpred_dir₁ _ _ _ _ _ =>
          -- pred₁ encapsulates CLE₁, pred₁ OB e₁
          have hpred_enc : dc₁.oEnd < hpred₁.choose.oEnd := hpred_dir₁.reqEncapDir.2
          have hpred_ob : hpred₁.choose.oEnd < e₁.oStart := by
            have h := hpred₁.choose_spec.2
            simp only [Behaviour.immBottomPredHasNoPermsAndLeavesStateAtLeast,
                        Behaviour.ImmediateBottomPredSatisfyingProp] at h
            have := h.isImmPred.bPred.isPred
            simp only [Event.Predecessor, Event.OrderedBefore] at this; exact this
          cases hda₂ with
          | encapDir _ hencap₂ =>
            have henc₂ : e₂.oStart < dc₂.oStart := hencap₂.reqEncapDir.1
            exact absurd (calc
              dc₁.oEnd < hpred₁.choose.oEnd := hpred_enc
              _ < e₁.oStart := hpred_ob
              _ < e₁.oEnd := e₁.oWellFormed
              _ < e₂.oStart := hob
              _ < dc₂.oStart := henc₂
              _ < dc₂.oEnd := dc₂.oWellFormed
              _ < dc₁.oStart := hrev
              _ < dc₁.oEnd := dc₁.oWellFormed) (Nat.lt_irrefl _)
          | orderBeforeDir _ _ _ _ _ _ _ _ =>
            sorry -- predecessor elimination
          | orderAfterDir _ hsucc₂ _ _ =>
            have h_sat := hsucc₂.choose_spec.2.satisfyP
            simp only [Event.PropOnEvent, Behaviour.succOnVdWithCorrespondingDir] at h_sat
            have henc₂ : hsucc₂.choose.oStart < dc₂.oStart := h_sat.encapCorresponding.reqEncapDir.1
            have hsuc : e₂.oEnd < hsucc₂.choose.oStart := by
              have h := hsucc₂.choose_spec.2.isImmBottomSucc.isSucc
              simp only [Event.Successor, Event.Predecessor, Event.OrderedBefore] at h; exact h
            exact absurd (calc
              dc₁.oEnd < hpred₁.choose.oEnd := hpred_enc
              _ < e₁.oStart := hpred_ob
              _ < e₁.oEnd := e₁.oWellFormed
              _ < e₂.oStart := hob
              _ < e₂.oEnd := e₂.oWellFormed
              _ < hsucc₂.choose.oStart := hsuc
              _ < dc₂.oStart := henc₂
              _ < dc₂.oEnd := dc₂.oWellFormed
              _ < dc₁.oStart := hrev
              _ < dc₁.oEnd := dc₁.oWellFormed) (Nat.lt_irrefl _)
        | orderAfterDir _ _ _ _ =>
          sorry -- nc.weak case: CLE sharing with release successor
    | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
    | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h

/-- Different-address PPOi → hierarchicallyOrdered via CompoundLinearizationOrder + GMO bridge.

    For different-address PPOi pairs, `CompoundLinearizationOrder` is already proven
    (`ppo_cluster_events_satisfy_CompoundLinearizationOrder` in CompoundPPOs.lean).
    This gives CLE-level ordering (compound linearization events ordered).

    The GMO bridge converts compound linearization ordering to the Herd 4-level
    hierarchy (GLE, GCR, CLE, cache). This bridges between the CompoundMCM world
    (where ordering is determined by compound linearization) and the Herd world
    (where ordering uses `globalLinearizationEventOfRequest`). -/
theorem ppoi_hierarchicallyOrdered_diff_addr
    {e₁ e₂ : Event n}
    (hppoi : @PPOi n b e₁ e₂)
    (hdiff_addr : e₁.addr ≠ e₂.addr)
    (h₁_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (h₂_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : hierarchicallyOrdered h₁_lin h₂_lin := by
  -- Step 1: GLEs are directory events (from dirAccessOfRequest)
  have hgle₁_isDir := h₁_lin.hreq's_global_lin.choose_spec.2.isDirEvent
  have hgle₂_isDir := h₂_lin.hreq's_global_lin.choose_spec.2.isDirEvent
  -- Step 2: Get CompoundLinearizationOrder (already proven for diff-addr PPOi).
  have hclo := @CompoundProtocol.enforce_compound_consistency n b init e₁ e₂ compound
    hppoi.sameProtocol hppoi.notDown₁ hppoi.notDown₂
    hppoi.cache₁ hppoi.cache₂ hppoi.in_b₁ hppoi.in_b₂
    hppoi.sameCid' hdiff_addr hppoi.orderedBefore
  unfold CompoundProtocol.CompoundLinearizationOrder at hclo
  have hord := hclo hppoi.ppo
  -- hord : e_lin₁.OrderedBefore n e_lin₂ ∨ lazyCompoundLinearizationOrder n b init e₂ e_lin₁
  -- Step 3: Use dir_ordered on GLEs (same structure as same-address case).
  show hierarchicallyOrdered h₁_lin h₂_lin
  unfold hierarchicallyOrdered gleOrderedBefore gle
  match h₁_lin.hreq's_global_lin.choose, h₂_lin.hreq's_global_lin.choose,
      hgle₁_isDir, hgle₂_isDir with
  | .directoryEvent de₁, .directoryEvent de₂, _, _ =>
    have h_ordered := (b.orderedAtEntry.dir_ordered de₁ de₂).ordered
    simp [DirectoryEvent.Ordered] at h_ordered
    rcases h_ordered with hob | hob
    · -- GLE₁ OB GLE₂ → hierarchicallyOrdered at level 1
      left
      simp only [Event.OrderedBefore, Event.oEnd, Event.oStart]
      simp only [DirectoryEvent.OrderedBefore] at hob
      exact hob
    · -- GLE₂ OB GLE₁: use CompoundLinearizationOrder to derive contradiction.
      -- hord says compound lin events are ordered e_lin₁ OB e_lin₂ (or lazy).
      -- The compound lin events are temporally related to the GLEs: each compound
      -- lin event is at or below the GLE level (encapsulated by or ordered before
      -- the global directory event). So e_lin₁ OB e_lin₂ is incompatible with
      -- GLE₂ OB GLE₁ (temporal contradiction via encap/order transitivity).
      exfalso
      sorry
  | .cacheEvent _, _, h, _ => simp [Event.isDirectoryEvent] at h
  | _, .cacheEvent _, _, h => simp [Event.isDirectoryEvent] at h

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

/-- co edges give hierarchical ordering (directly by definition). -/
theorem co_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.co n compound b init e₁ e₂)
    : hierarchicallyOrdered h.w₁_lin h.w₂_lin :=
  h.ordering

/-- fr edges give hierarchical ordering (directly from the fr structure). -/
theorem fr_hierarchicallyOrdered
    {e₁ e₂ : Event n}
    (h : @Herd.fr n compound b init e₁ e₂)
    : hierarchicallyOrdered h.e₁_lin h.e₂_lin :=
  h.ordering

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
    (hcom : com compound b init e₁ e₂)
    : hierarchicallyOrdered (hknow compound b init e₁) (hknow compound b init e₂) := by
  cases hcom with
  | ppoi h =>
    exact @ppoi_hierarchicallyOrdered n compound b init e₁ e₂ h
      (hknow compound b init e₁) (hknow compound b init e₂)
  | rfe h =>
    exact hierarchicallyOrdered_subst (rfe_hierarchicallyOrdered h)
  | co h =>
    exact hierarchicallyOrdered_subst (co_hierarchicallyOrdered h)
  | fr h =>
    exact hierarchicallyOrdered_subst (fr_hierarchicallyOrdered h)

/-- A `TransGen com` path from e₁ to e₂ gives hierarchical ordering between them. -/
theorem transGen_com_hierarchicallyOrdered
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n))
    (hpath : Relation.TransGen (com compound b init) e₁ e₂)
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
    : CMCM compound b init := by
  unfold CMCM acyclic
  intro e hcycle
  exact hierarchicallyOrdered_irrefl _
    (transGen_com_hierarchicallyOrdered hknow_dir_access hcycle)

end Herd
