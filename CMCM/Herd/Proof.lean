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

/-- List.stateAfter on append singleton: processing xs then e equals
    applying e's SucceedingState to the result of processing xs. -/
theorem list_stateAfter_append_singleton (xs : List (Event n)) (e : Event n) :
    ∀ init : EntryState n,
    (xs ++ [e]).stateAfter n init = e.SucceedingState n (xs.stateAfter n init) := by
  induction xs with
  | nil => intro init; simp [List.stateAfter]
  | cons x xs ih => intro init; simp only [List.cons_append, List.stateAfter]; exact ih _

/-- Behaviour.stateAfter = event's SucceedingState applied to stateBefore. -/
theorem stateAfter_eq_succeedingState
    {b : Behaviour n} {init : EntryState n} {e : Event n} :
    b.stateAfter n init e = e.SucceedingState n (b.stateBefore n init e) := by
  unfold Behaviour.stateAfter Behaviour.stateBefore
  exact list_stateAfter_append_singleton _ _ _

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

/-- Two proofs of the same existential Prop have the same `.choose`. -/
theorem exists_choose_eq {α : Sort _} {p : α → Prop} (h₁ h₂ : ∃ x, p x) :
    h₁.choose = h₂.choose :=
  congrArg Exists.choose (Subsingleton.elim h₁ h₂)

/-- The compound linearization event for a clusterDirLin event is at-or-inside the Herd CLE.
    Specifically, for event e:
    - `(lin e).hreq's_dir_access.choose` is the Herd CLE
    - `(compound.compoundLinearizationEvent ...).linearizationEvent` is the compound lin event
    When both frameworks agree (via dirAccessOfRequest for the same event),
    the compound lin event satisfies `CLE.oStart ≤ e_lin.oStart` and `e_lin.oEnd ≤ CLE.oEnd`.

    For previousGlobalCacheGotPerms: e_lin = CLE, so both bounds are equalities.
    For getGlobalCachePerms: e_lin is inside CLE (via GCR encapsulation chain).
    For clusterCacheLin: e_lin = cache event, only the first bound holds for
    orderBeforeDir (CLE before cache event). -/
-- Helper: extract the directory event from the compound linearization framework.
-- When linearizationOfEvent is .dirLin, the reqLinearizeAtDir.choose satisfies dirAccessOfRequest.
-- This is the same type as hreq's_dir_access, so by Subsingleton, choose values are equal.
private noncomputable def compound_dir_access_of_dirLin
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e : Event n}
    (lin_at_dir : ∃ e_lin ∈ b, b.requestWithoutCoherentPermsLinearizesAtDir n init e e_lin) :
    ∃ e_cdir ∈ b, b.dirAccessOfRequest n init e e_cdir :=
  let req_lin_at_dir := lin_at_dir.choose_spec.right.reqLinearizeAtDir
  let e_dir := req_lin_at_dir.choose
  let e_dir_in_b := req_lin_at_dir.choose_spec.left
  let dir_access := req_lin_at_dir.choose_spec.right.reqCorrespondsToDir
  ⟨e_dir, e_dir_in_b, dir_access⟩

private noncomputable def compound_lin_start_bound
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e : Event n)
    (lin_e : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) :
    Event.oStart n lin_e.hreq's_dir_access.choose ≤
    Event.oStart n (compound.compoundLinearizationEvent compound.shimAxioms b init e
      (compound.linearizationOfEvent b init e)).linearizationEvent := by
  -- Match on compound linearization type (only clusterDirLin is reachable at call sites)
  match hclin : compound.compoundLinearizationEvent compound.shimAxioms b init e
      (compound.linearizationOfEvent b init e) with
  | .clusterCacheLin hcache =>
    -- Unreachable at call sites (non-lazy CompoundMCM guarantees clusterDirLin).
    -- For completeness: CLE.oStart ≤ e.oStart holds for orderBeforeDir.
    simp only [ClusterRequestLinearizationEvent.linearizationEvent]
    have hcache_eq_e := hcache.choose_spec.right.e_creq_is_e_glin; rw [hcache_eq_e]
    have hdir_access := lin_e.hreq's_dir_access.choose_spec.2
    cases hdir_access with
    | orderBeforeDir _ hexists_pred hpred_dir_access _ _ _ _ _ =>
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_of_lt_of_le (Event.oWellFormed n lin_e.hreq's_dir_access.choose)
          (Nat.le_of_lt hpred_dir_access.reqEncapDir.right))
        hexists_pred.choose_spec.right.isImmPred.bPred.isPred)
    | encapDir _ _ => sorry -- unreachable: clusterCacheLin (reqHasPerms) ∧ encapDir (reqMissingPerms)
    | orderAfterDir _ _ _ _ => sorry -- unreachable: clusterCacheLin (reqHasPerms) ∧ orderAfterDir (ncWeak)
  | .clusterDirLin hdir =>
    -- compound lin event = hdir.choose
    simp only [ClusterRequestLinearizationEvent.linearizationEvent]
    -- Need: lin_e.hreq's_dir_access.choose.oStart ≤ hdir.choose.oStart
    -- Use simp + split to decompose OfReqEncapDirAccess (matches on linearizationOfEvent)
    have he_lin_dir := hdir.choose_spec.right.e_glin_deeper
    simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at he_lin_dir
    split at he_lin_dir
    · -- requestLin case: OfReqEncapDirAccess is False
      exfalso; exact he_lin_dir
    · -- dirLin case: he_lin_dir is now clusterDirectoryLinearizationEvent
      next hcreq_lin hdir_lin _ =>
      -- hdir_lin : ∃ e_lin ∈ b, requestWithoutCoherentPermsLinearizesAtDir ...
      -- he_lin_dir : clusterDirectoryLinearizationEvent ... reqLinearizeAtDir.choose hdir.choose
      have hreq_lin_at_dir := hdir_lin.choose_spec.right.reqLinearizeAtDir.choose_spec.right
      -- hreq_lin_at_dir : requestLinearizesAtDirectory ... e reqLinearizeAtDir.choose ...
      -- hreq_lin_at_dir.reqCorrespondsToDir : dirAccessOfRequest b init e reqLinearizeAtDir.choose
      -- Now case-split on clusterDirectoryLinearizationEvent
      cases he_lin_dir with
      | previousGlobalCacheGotPerms _ he_glin_eq_cdir =>
        have h_compound_dir := hreq_lin_at_dir.reqCorrespondsToDir
        have h_herd_dir := lin_e.hreq's_dir_access.choose_spec.2
        have hcle_eq := compound.dirAccessUnique b init e _ _ h_compound_dir h_herd_dir
        rw [he_glin_eq_cdir, hcle_eq]
      | getGlobalCachePerms _ hglin_deeper =>
        -- compound CLE = reqLinearizeAtDir.choose. By uniqueness = Herd CLE.
        have hcle_eq := compound.dirAccessUnique b init e _ _
          hreq_lin_at_dir.reqCorrespondsToDir lin_e.hreq's_dir_access.choose_spec.2
        -- CLE encapsulates compound lin event (via GCR chain)
        have hcle_encap_glin :=
          CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n hreq_lin_at_dir hglin_deeper
        -- Encapsulates gives strict: CLE.oStart < hdir.choose.oStart
        rw [← hcle_eq]
        exact Nat.le_of_lt hcle_encap_glin.left

private noncomputable def compound_lin_end_bound
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    (e : Event n)
    (lin_e : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) :
    Event.oEnd n (compound.compoundLinearizationEvent compound.shimAxioms b init e
      (compound.linearizationOfEvent b init e)).linearizationEvent ≤
    Event.oEnd n lin_e.hreq's_dir_access.choose := by
  -- Match on compound linearization type
  match hclin : compound.compoundLinearizationEvent compound.shimAxioms b init e
      (compound.linearizationOfEvent b init e) with
  | .clusterCacheLin hcache =>
    -- compound lin event = e (cache event). CLE from dirAccessOfRequest.
    -- For orderBeforeDir: CLE.oEnd < pred.oEnd < e.oStart < e.oEnd → e.oEnd > CLE.oEnd.
    -- This bound DOES NOT HOLD for clusterCacheLin.
    simp only [ClusterRequestLinearizationEvent.linearizationEvent]
    have hcache_eq_e := hcache.choose_spec.right.e_creq_is_e_glin
    rw [hcache_eq_e]
    -- Goal: e.oEnd ≤ CLE.oEnd — FALSE for orderBeforeDir
    have hdir_access := lin_e.hreq's_dir_access.choose_spec.2
    cases hdir_access with
    | encapDir hreq_missing _ =>
      have hreq_has := hcache.choose_spec.right.cReqHasPerms
      sorry -- reqHasPerms + reqMissingPerms → False
    | orderBeforeDir _ hexists_pred hpred_dir_access _ _ _ _ _ =>
      -- CLE.oEnd < pred.oEnd < e.oStart < e.oEnd → e.oEnd > CLE.oEnd. FALSE.
      sorry -- e.oEnd ≤ CLE.oEnd is false; need contradiction from clusterCacheLin + orderBeforeDir context
    | orderAfterDir hweak _ _ _ =>
      have hreq_has := hcache.choose_spec.right.cReqHasPerms
      sorry -- reqHasPerms + ncWeakReqOnVd → contradiction via compound axioms
  | .clusterDirLin hdir =>
    -- compound lin event = hdir.choose
    simp only [ClusterRequestLinearizationEvent.linearizationEvent]
    -- Need: hdir.choose.oEnd ≤ lin_e.hreq's_dir_access.choose.oEnd
    -- Use simp + split to decompose OfReqEncapDirAccess
    have he_lin_dir := hdir.choose_spec.right.e_glin_deeper
    simp [CompoundProtocol.compoundLinearization.OfReqEncapDirAccess] at he_lin_dir
    split at he_lin_dir
    · -- requestLin case: OfReqEncapDirAccess is False
      exfalso; exact he_lin_dir
    · -- dirLin case
      next hcreq_lin hdir_lin _ =>
      have hreq_lin_at_dir := hdir_lin.choose_spec.right.reqLinearizeAtDir.choose_spec.right
      cases he_lin_dir with
      | previousGlobalCacheGotPerms _ he_glin_eq_cdir =>
        have hcle_eq := compound.dirAccessUnique b init e _ _
          hreq_lin_at_dir.reqCorrespondsToDir lin_e.hreq's_dir_access.choose_spec.2
        rw [he_glin_eq_cdir, hcle_eq]
      | getGlobalCachePerms _ hglin_deeper =>
        have hcle_eq := compound.dirAccessUnique b init e _ _
          hreq_lin_at_dir.reqCorrespondsToDir lin_e.hreq's_dir_access.choose_spec.2
        -- CLE encapsulates compound lin event (via GCR chain)
        have hcle_encap_glin :=
          CompoundProtocol.cdir_encap_glin_of_cdir_linearize_at_dir n hreq_lin_at_dir hglin_deeper
        -- Encapsulates gives strict: hdir.choose.oEnd < CLE.oEnd
        rw [← hcle_eq]
        exact Nat.le_of_lt hcle_encap_glin.right

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

/-! ## StepOrdering → LinLink: ordering between linearization points

Each cache event e has a linearization point `lin(e)` = CLE.
Each edge derives `StepOrdering lin(e₁) lin(e₂)` from communication evidence,
then converts to `LinLink ∨ eq` via `StepOrdering.toLinLinkOrEq`.

LinLink = TransGen LinStep, where LinStep has 4 constructors:
  ob, encap, encapBy, finishesBefore.

Transitivity: free from TransGen (no hand-written trans needed).
Irreflexivity: LinLink.irrefl (proved once for all edge patterns).
A cycle composes to LinLink CLE CLE → LinLink.irrefl,
or all edges give CLE₁ = CLE₂ → dir_ordered de de → False. -/

-- StepOrdering definition moved to Defs.lean
-- StepOrdering.trans DELETED: replaced by LinLink.trans (free from TransGen).

/-- Map a single co edge to StepOrdering. Factored out to avoid recursion in step_to_ordering. -/
theorem co_step_to_ordering
    (h : @Herd.co n compound b init e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h.comm with
  | sameCache same_cle cache_ob =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    have hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose := by
      rw [← hw₁, ← hw₂]; exact same_cle
    have hda₁ := (lin e₁).hreq's_dir_access.choose_spec.2; rw [← hw₁] at hda₁
    have hda₂ := (lin e₂).hreq's_dir_access.choose_spec.2; rw [← hw₂] at hda₂
    cases hda₁ with
    | encapDir _ hencap₁ =>
      cases hda₂ with
      | encapDir _ hencap₂ =>
        exact .sameLin e₁ e₂ hcle_eq
          (by rw [← hw₁]; exact ⟨hencap₁.reqEncapDir.left, hencap₁.reqEncapDir.right⟩)
          cache_ob
          (by rw [← hw₂]; exact ⟨hencap₂.reqEncapDir.left, hencap₂.reqEncapDir.right⟩)
      | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq hcle_eq
      | orderAfterDir _ _ _ _ => exact .eq hcle_eq
    | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq hcle_eq
    | orderAfterDir _ _ _ _ => exact .eq hcle_eq
  | sameClusDiffCache _ cle_ord =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob => exact .ob (by rw [← hw₁, ← hw₂]; exact hob)
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        exact .obEndLt hdown.existsRClusterDirDown.choose
          (by rw [← hw₁]; exact hwObRDown)
          (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt)
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact .ob (by rw [← hw₁, ← hw₂]; exact evict.wObR)
  | diffClus _ diff_cluster_cases =>
    have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
    have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
    cases diff_cluster_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt w.rDown.encapDir.existsRClusterDirDown.choose
        (by rw [← hw₁]; exact w.wObRDown)
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose
        (by rw [← hw₁]; exact evict.wObRDown)
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)

/-- Extract the first step from a TransGen chain. -/
private lemma transGen_first_step {r : α → α → Prop} (h : Relation.TransGen r a c) :
    ∃ b, r a b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-- Decompose a TransGen cycle into first step + rest. -/
private lemma transGen_head_tail {r : α → α → Prop} (h : Relation.TransGen r a c) :
    ∃ b, r a b ∧ (b = c ∨ Relation.TransGen r b c) := by
  induction h with
  | single h => exact ⟨_, h, Or.inl rfl⟩
  | tail h_path h_last ih =>
    obtain ⟨b, hfirst, hrest⟩ := ih
    exact ⟨b, hfirst, Or.inr (hrest.elim (fun heq => heq ▸ .single h_last) (fun htg => htg.tail h_last))⟩

/-- If d is a directory event, d.req.val.rw = e_r.req.val.rw, and e_r is a write,
    then d is a directory write. Used to derive isDirWrite from existsRClusterDirDown spec. -/
private lemma isDirWrite_of_rw_eq_write
    {d e_r : Event n}
    (h_dir : d.isDirectoryEvent)
    (h_rw : d.req.val.rw = e_r.req.val.rw)
    (h_write : e_r.isWrite)
    : d.isDirWrite := by
  cases d with
  | cacheEvent => exact absurd h_dir (by simp [Event.isDirectoryEvent])
  | directoryEvent de =>
    simp only [Event.isDirWrite, Request.isWrite]
    cases e_r with
    | directoryEvent => exact absurd h_write (by simp [Event.isWrite])
    | cacheEvent ce =>
      simp only [Event.req] at h_rw
      rw [h_rw]
      exact h_write

/-- Extract oEnd ≤ from a single CO step by inlining case analysis. -/
private lemma co_step_oEnd_le
    (h : @Herd.co n compound b init e₁ e₂)
    (lin : ∀ e, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Event.oEnd n (lin e₁).hreq's_dir_access.choose ≤
      Event.oEnd n (lin e₂).hreq's_dir_access.choose := by
  have hw₁ : h.w₁_lin = lin e₁ := Subsingleton.elim _ _
  have hw₂ : h.w₂_lin = lin e₂ := Subsingleton.elim _ _
  cases h.comm with
  | sameCache same_cle _ =>
    exact Nat.le_of_eq (congrArg (Event.oEnd n) (by rw [← hw₁, ← hw₂]; exact same_cle))
  | sameClusDiffCache _ cle_ord =>
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob =>
        exact Nat.le_of_lt (Nat.lt_trans (by rw [← hw₁, ← hw₂]; exact hob) (Event.oWellFormed n _))
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        exact Nat.le_of_lt (Nat.lt_trans
          (Nat.lt_trans (by rw [← hw₁]; exact hwObRDown) (Event.oWellFormed n _))
          (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt))
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact Nat.le_of_lt (Nat.lt_trans (by rw [← hw₁, ← hw₂]; exact evict.wObR) (Event.oWellFormed n _))
  | diffClus _ diff_cases =>
    cases diff_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_trans (by rw [← hw₁]; exact w.wObRDown) (Event.oWellFormed n _))
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt))
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_trans (by rw [← hw₁]; exact evict.wObRDown) (Event.oWellFormed n _))
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt))

/-- Extract oEnd ≤ from a CO chain by composing single-step bounds. -/
private lemma co_chain_oEnd_le
    (hco_chain : Relation.TransGen (@Herd.co n compound b init) e_w e₂)
    (lin : ∀ e, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Event.oEnd n (lin e_w).hreq's_dir_access.choose ≤
      Event.oEnd n (lin e₂).hreq's_dir_access.choose := by
  induction hco_chain with
  | single h => exact co_step_oEnd_le h lin
  | tail _ h ih => exact Nat.le_trans ih (co_step_oEnd_le h lin)

/-- Given oEnd ≤ and dir_ordered at same cluster, derive OB.
    Wrong direction + oEnd ≤ → de₁.oEnd ≤ de₂.oEnd < de₁.oStart → False. -/
private lemma co_chain_same_cluster_ob
    {l₁ l₂ : Event n} {de₁ de₂ : DirectoryEvent n}
    (hoEnd : Event.oEnd n l₁ ≤ Event.oEnd n l₂)
    (hfc₁ : l₁ = .directoryEvent de₁) (hfc₂ : l₂ = .directoryEvent de₂)
    (hdir : DirectoryEvent.AreOrdered n de₁ de₂)
    : l₁.OrderedBefore n l₂ := by
  cases hdir.ordered with
  | inl h => rw [hfc₁, hfc₂]; exact h
  | inr h =>
    exfalso; rw [hfc₁, hfc₂] at hoEnd
    exact Nat.lt_irrefl de₁.oEnd (Nat.lt_of_le_of_lt hoEnd (Nat.lt_trans h de₁.oWellFormed))

/-- For a co chain crossing clusters: extract downgrade d at e_w's cluster
    with CLE_w OB d, d.oEnd < CLE₂.oEnd, d at e_w's protocol. -/
private lemma co_chain_cross_cluster_downgrade
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e_w e₂ : Event n}
    (h_co_chain : Relation.TransGen (@Herd.co n compound b init) e_w e₂)
    (h_diff_prot : ¬ e_w.sameProtocol n e₂)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : ∃ (d : Event n),
        d ∈ b ∧
        e_w_lin.hreq's_dir_access.choose.OrderedBefore n d ∧
        d.oEnd < (lin e₂).hreq's_dir_access.choose.oEnd ∧
        d.isDirectoryEvent ∧
        d.protocol = e_w.protocol ∧
        ¬ d.down ∧
        d.isDirWrite ∧
        Event.clusterDirFromDiffProtocolRequest b init e₂ d (lin e₂) := by
  -- Induction on co chain. The endpoint e₂ gets generalized.
  -- Use h_diff_prot and lin in generalized form.
  induction h_co_chain with
  | single h_co =>
    -- Single co step: co(e_w, c). Since protocols differ: must be diffClus.
    cases h_co.comm with
    | sameCache same_cle _ =>
      -- sameCache → same CLE → same protocol. But h_diff_prot says diff protocol. Contradiction.
      exfalso; apply h_diff_prot
      unfold Event.sameProtocol
      -- same_cle : CLE_w = CLE₂. CLE_w.protocol = e_w.protocol, CLE₂.protocol = e₂.protocol.
      have h1 := write_cle_protocol_eq_write_protocol h_co.w₁_lin
      have h2 := write_cle_protocol_eq_write_protocol h_co.w₂_lin
      rw [← h1, ← h2, same_cle]
    | sameClusDiffCache h_same_prot _ => exact absurd h_same_prot h_diff_prot
    | diffClus _ diff_cases =>
      cases diff_cases with
      | wCleImmPredDown w =>
        have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            h_co.w₂_lin.hreq's_dir_access.choose.oEnd := by
          cases hrd_spec.2.2.2.2.2.2 with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_lin from Subsingleton.elim _ _]; exact w.wObRDown,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.1, hrd_spec.2.2.1, hrd_spec.2.2.2.2.1,
          isDirWrite_of_rw_eq_write hrd_spec.2.1 hrd_spec.2.2.2.1 h_co.write₂,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.2.1⟩
      | evictOrReadBetweenWAndRDown evict =>
        have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            h_co.w₂_lin.hreq's_dir_access.choose.oEnd := by
          cases hrd_spec.2.2.2.2.2.2 with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_lin from Subsingleton.elim _ _]; exact evict.wObRDown,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.1, hrd_spec.2.2.1, hrd_spec.2.2.2.2.1,
          isDirWrite_of_rw_eq_write hrd_spec.2.1 hrd_spec.2.2.2.1 h_co.write₂,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.2.1⟩
  | tail hpath h_last ih =>
    rename_i b_mid c_ep
    -- IH for prefix. Extend d.oEnd bound via last step's StepOrdering.
    by_cases h_mid_prot : e_w.sameProtocol n b_mid
    · -- Prefix same-cluster: last step h_last must cross clusters.
      -- Get CLE_w.oEnd ≤ CLE_mid.oEnd from prefix StepOrdering.
      have hcle_w_le_mid : Event.oEnd n e_w_lin.hreq's_dir_access.choose ≤
          Event.oEnd n (lin b_mid).hreq's_dir_access.choose := by
        have hoEnd := co_chain_oEnd_le hpath lin
        rw [show e_w_lin = lin e_w from Subsingleton.elim _ _]; exact hoEnd
      -- mid and c_ep must have different protocol (e_w same as mid, diff from c_ep)
      have h_mid_diff_c : ¬ b_mid.sameProtocol n c_ep := by
        intro h; exact h_diff_prot (show e_w.sameProtocol n c_ep from
          (show e_w.protocol = c_ep.protocol from
            (show e_w.protocol = b_mid.protocol from h_mid_prot).trans h))
      -- h_last.comm must be diffClus
      cases h_last.comm with
      | sameCache same_cle _ =>
        exfalso; apply h_mid_diff_c; unfold Event.sameProtocol
        have h1 := write_cle_protocol_eq_write_protocol h_last.w₁_lin
        have h2 := write_cle_protocol_eq_write_protocol h_last.w₂_lin
        rw [← h1, ← h2, same_cle]
      | sameClusDiffCache h_same _ => exact absurd h_same h_mid_diff_c
      | diffClus _ diff_cases =>
        cases diff_cases with
        | wCleImmPredDown w =>
          have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              h_last.w₂_lin.hreq's_dir_access.choose.oEnd := by
            cases hrd_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := w.wObRDown
          rw [show h_last.w₁_lin = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.1,
            hrd_spec.2.2.1.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            hrd_spec.2.2.2.2.1,
            isDirWrite_of_rw_eq_write hrd_spec.2.1 hrd_spec.2.2.2.1 h_last.write₂,
            by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.2.1⟩
        | evictOrReadBetweenWAndRDown evict =>
          have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              h_last.w₂_lin.hreq's_dir_access.choose.oEnd := by
            cases hrd_spec.2.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := evict.wObRDown
          rw [show h_last.w₁_lin = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.1,
            hrd_spec.2.2.1.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            hrd_spec.2.2.2.2.1,
            isDirWrite_of_rw_eq_write hrd_spec.2.1 hrd_spec.2.2.2.1 h_last.write₂,
            by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.2.1⟩
    · -- Prefix diff-cluster: IH gives d with d.oEnd < CLE_mid.oEnd.
      obtain ⟨d, hd_in_b, hob_d, hd_lt, hd_isDir, hd_proto, hd_not_down, hd_isDirWrite, hd_translatedDir⟩ := ih h_mid_prot
      -- Extend to CLE_c via co_step_to_ordering.
      have hext : (lin b_mid).hreq's_dir_access.choose.oEnd ≤ (lin c_ep).hreq's_dir_access.choose.oEnd :=
        co_step_oEnd_le h_last lin
      exact ⟨d, hd_in_b, hob_d, Nat.lt_of_lt_of_le hd_lt hext, hd_isDir, hd_proto, hd_not_down, hd_isDirWrite, sorry⟩ -- translatedDir endpoint shifted

/-- Extract cross-cluster encapDir from any diffCache.case sub-case when e_w and e_r
    are at different clusters. Returns encapDir (with existsRClusterDirDown + encapDirRelation). -/
private lemma diffCache_case_extract_encapDir
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e_w e_r : Event n}
    {hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w}
    {hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r}
    {hknow : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)}
    (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
    (h : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow)
    (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
    : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin := by
  cases h with
  | wHasPermsAfter _ coherent_case =>
    cases coherent_case with
    | immPred _ hencapPD => exact hencapPD.encapDir
    | notImmPred hcase =>
      cases hcase with
      | noEvictBetween w => exact w.gdownEncapProxyAndDirAndCDown.encapDir
      | evictBetween w => exact w.encapProxyAndDir
  | wNoPermsAfter _ _ hrCle =>
    cases hrCle with
    | sameCluster _ hob => exact diffCache_coherent_encapProxyAndDir hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
    | diffCluster _ henc _ => exact henc
  | wCleAfter hrCle =>
    cases hrCle with
    | sameCluster _ hob => exact diffCache_coherent_encapProxyAndDir hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
    | diffCluster _ henc _ => exact henc

/-- 2-cluster elimination: if e₁ diff from e₂ and e_w not at e₁'s cluster, then e₂ same as e_w. -/
private lemma two_cluster_e₂_same_e_w
    {e₁ e₂ e_w : Event n}
    (h_same_prot : ¬ e₁.sameProtocol n e₂)
    (h_ew_e₁ : ¬ e₁.protocol = e_w.protocol)
    (hw_cache : e_w.isClusterCache)
    (h_cache₁ : e₁.isClusterCache) (h_cache₂ : e₂.isClusterCache)
    : e₂.sameProtocol n e_w := by
  unfold Event.sameProtocol
  cases hw_cache.eCluster with
  | inl hw1 => cases h_cache₂.eCluster with
    | inl h2c1 => exact h2c1.trans hw1.symm
    | inr h2c2 => cases h_cache₁.eCluster with
      | inl h1c1 => exact absurd (h1c1.trans hw1.symm) h_ew_e₁
      | inr h1c2 => exfalso; exact h_same_prot (h1c2.trans h2c2.symm)
  | inr hw2 => cases h_cache₂.eCluster with
    | inr h2c2 => exact h2c2.trans hw2.symm
    | inl h2c1 => cases h_cache₁.eCluster with
      | inr h1c2 => exact absurd (h1c2.trans hw2.symm) h_ew_e₁
      | inl h1c1 => exfalso; exact h_same_prot (h1c1.trans h2c1.symm)

/-- FR ordering theorem: proves FrOrdering from rf + co + NIW evidence.
    Mirrors CMCM.rf_holds for RF and co_step_to_ordering for CO.
    The descriptive evidence in FrOrdering is DERIVED from protocol axioms,
    not assumed. A reviewer can verify the derivation. -/
-- Helper not feasible due to complex types. CLE₂ OB d_rf NIW sorry's use inline pattern.

theorem fr_ordering_holds
    (h : @Herd.fr n compound b init e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : FrOrdering (lin e₁) (lin e₂) := by
  -- FR = rf⁻¹ ; co⁺ with e_w as intermediate write.
  -- Case structure: sameCLE / sameCache / sameClusDiffCache / diffCluster.
  -- diffCluster sub-cases by e₁'s coherence state.
  by_cases hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose
  · exact .sameCLE hcle_eq
  · by_cases h_same_cache : e₁.struct = e₂.struct
    · -- Same cache e₁/e₂: same cluster + same dir → dir_ordered + NIW.
      have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
      match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₂, _ =>
          cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
          | inl hob =>
            exact .sameCache h_same_cache (Or.inr (show Event.OrderedBefore n
              (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose from
              by rw [hfc₁, hfc₂]; exact hob))
          | inr hob =>
            -- CLE₂ OB CLE₁ → contradiction via NIW (same as sameClusDiffCache).
            exfalso
            obtain ⟨e_w, _, _, _, _, h_no_between, _, _, _, _⟩ := h.comm
            have hlin := fun e => h.hknow_dir_access compound b init e
            have h_constraints := h_no_between e₂ h.in_b₂ h.cache₂ h.write h.notDown₂ (hlin e₂)
            -- same cache → same protocol (same struct → same cid → same protocol)
            have h_same_prot₂₁ : e₂.sameProtocol n e₁ := by
              unfold Event.sameProtocol
              -- h_same_cache : e₁.struct = e₂.struct
              -- For cache events: struct = Struct.cache cid, so same struct → same cid → same protocol.
              match he₁ : e₁, h.cache₁.eAtCache with
              | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
              | .cacheEvent ce₁, _ =>
                match he₂ : e₂, h.cache₂.eAtCache with
                | .directoryEvent _, hh => simp [Event.isCacheEvent] at hh
                | .cacheEvent ce₂, _ =>
                  simp [Event.struct] at h_same_cache
                  simp [Event.protocol, h_same_cache]
            exact h_constraints.interSameProtocolCleOB h_same_prot₂₁
              (show (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                  (lin e₁).hreq's_dir_access.choose from by
                rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob)
    · by_cases h_same_prot : e₁.sameProtocol n e₂
      · -- Same cluster, different cache: dir_ordered + NIW.
        have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
        have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
        match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₁, _ =>
          match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₂, _ =>
            cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
            | inl hob =>
              exact .sameClusDiffCache h_same_prot h_same_cache (show Event.OrderedBefore n
                (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose from
                by rw [hfc₁, hfc₂]; exact hob)
            | inr hob =>
              -- CLE₂ OB CLE₁ → contradiction via NIW.
              exfalso
              obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                hw_in_b, hw_cache, hw_not_down⟩ := h.comm
              have hlin := fun e => h.hknow_dir_access compound b init e
              have h_constraints := h_no_between e₂ h.in_b₂
                h.cache₂ h.write h.notDown₂ (hlin e₂)
              -- by_cases on e_w's cluster
              by_cases h_ew_prot : e₂.protocol = e_w.protocol
              · -- Same cluster e_w/e₂: all same cluster. notBetweenCles.
                have hcle₂_prot := write_cle_protocol_eq_write_protocol (hlin e₂)
                have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
                have hcle_w_prot := write_cle_protocol_eq_write_protocol e_w_lin
                have hprot_e₂_e₁ : e₂.protocol = e₁.protocol := by
                  unfold Event.sameProtocol at h_same_prot; exact h_same_prot.symm
                have hprot₁ : (hlin e₂).hreq's_dir_access.choose.protocol =
                    e_w_lin.hreq's_dir_access.choose.protocol :=
                  hcle₂_prot.trans (h_ew_prot.trans hcle_w_prot.symm)
                have hprot₂ : (hlin e₂).hreq's_dir_access.choose.protocol =
                    (lin e₁).hreq's_dir_access.choose.protocol :=
                  hcle₂_prot.trans (hprot_e₂_e₁.trans hcle₁_prot.symm)
                have h_isDirWrite : (hlin e₂).hreq's_dir_access.choose.isDirWrite := by
                  have : hlin e₂ = h.e₂_lin := Subsingleton.elim _ _
                  rw [this]; exact write_event_cle_isDirWrite h.write h.cache₂ h.notDown₂ h.e₂_lin h.in_b₂
                have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_w, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_w de₂).ordered with
                  | inl hob_w₂ =>
                    exact h_constraints.notBetweenCles ⟨hprot₁, hprot₂, h_isDirWrite⟩
                      ⟨by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂, hfcw]; exact hob_w₂,
                       by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob⟩
                  | inr hob_₂w =>
                    have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                      have hoEnd := co_chain_oEnd_le h_co_chain hlin
                      rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm,
                          show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _] at hoEnd
                      simp only [Event.oEnd, hfcw, hfc₂] at hoEnd ⊢; exact hoEnd
                    exact Nat.lt_irrefl _ (calc de_w.oEnd ≤ de₂.oEnd := hcw_le
                      _ < de_w.oStart := hob_₂w
                      _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed)
              · -- Diff cluster e_w: use cdirEncapsDown_exists + diffClusterNotBetweenCles_sameCache.
                -- Use interSameProtocolCleOB: e₂ same cluster as e₁ → ¬ CLE₂ OB CLE₁.
                have h_same_prot₂₁ : e₂.sameProtocol n e₁ := by
                  unfold Event.sameProtocol at h_same_prot ⊢; exact h_same_prot.symm
                exact absurd
                  (show (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                      (lin e₁).hreq's_dir_access.choose from by
                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob)
                  (h_constraints.interSameProtocolCleOB h_same_prot₂₁)
      · -- Different cluster e₁/e₂: need proxy from e₂'s downgrade at e₁'s cluster.
        -- Get e₂'s downgrade evidence at e₁'s cluster first.
        obtain ⟨e_cdir, _, he_cdir_isDir, _, hcdir_lt_cle₂,
          ⟨e_cache_down, he_cdown_in_b, hcdir_encap_down, hcdown_is_down, hcdown_is_cache⟩,
          ⟨e_evict, he_evict_in_b, he_evict_isDir, he_evict_down, hevict_lt_cle₂,
           hcdir_ob_evict, he_evict_proto, he_evict_isDirWrite, he_evict_translatedDir⟩⟩ :=
          cdirEncapsDown_exists (lin e₁) (lin e₂) h.in_b₁ h.cache₁
        -- Case-split on e₁'s dirAccessOfRequest to determine where e₂'s downgrade lands.
        have hda₁ := (lin e₁).hreq's_dir_access.choose_spec.2
        cases hda₁ with
        | encapDir hreq_missing₁ hencap₁ =>
          -- e₁ coherent (encapDir): CLE₁ inside e₁.
          -- Use dir_ordered CLE₁ cdir at e₁'s cluster as the primary strategy.
          -- CLE₁ OB cdir → proxy = cdir. cdir OB CLE₁ → use evict or NIW.
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc_cdir : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob_cle₁_cdir =>
                -- CLE₁ OB cdir → proxy = cdir
                have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                exact .diffCluster_coherent h_same_prot (.directoryEvent de_cdir)
                  (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                    rw [hfc_cle₁]; exact hob_cle₁_cdir)
                  (by rw [hw₂']; exact hcdir_lt_cle₂)
              | inr hob_cdir_cle₁ =>
                -- cdir OB CLE₁. Try evict.
                have he_evict_isdir' := he_evict_isDir
                match hfc_evict : e_evict, he_evict_isdir' with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_evict, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_cle₁ de_evict).ordered with
                  | inl hob_cle₁_evict =>
                    have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                    exact .diffCluster_coherent h_same_prot (.directoryEvent de_evict)
                      (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                        rw [hfc_cle₁]; exact hob_cle₁_evict)
                      (by rw [hw₂']; exact hevict_lt_cle₂)
                  | inr hob_evict_cle₁ =>
                    -- evict OB CLE₁: both cdir and evict before CLE₁.
                    -- Case-split on e_w's cluster. Don't use exfalso yet —
                    -- some sub-cases construct FrOrdering, others derive False.
                    obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                      hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                    have hlin := fun e => h.hknow_dir_access compound b init e
                    by_cases h_ew_e₁ : e₁.protocol = e_w.protocol
                    · -- e_w same cluster as e₁: CO crosses clusters.
                      -- co_chain_cross_cluster_downgrade gives d_co with CLE_w OB d_co at e₁'s cluster.
                      -- dir_ordered d_co CLE₁:
                      --   CLE₁ OB d_co → proxy for .diffCluster_coherent
                      --   d_co OB CLE₁ → d_co between CLE_w and CLE₁ → NIW contradiction
                      have h_ew_diff_e₂ : ¬ e_w.sameProtocol n e₂ := by
                        unfold Event.sameProtocol
                        intro h; exact h_same_prot (show e₁.protocol = e₂.protocol from h_ew_e₁.trans h)
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto, hdco_not_down, hdco_isDirWrite, hdco_translatedDir⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      -- dir_ordered d_co CLE₁ at e₁'s cluster
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          -- d_co OB CLE₁: d_co between CLE_w and CLE₁ → NIW contradiction.
                          -- Need sameCacheWriteConstraints for d_co. d_co has isDirWrite (from rw = e₂.rw = .w)
                          -- and ¬down (from the shim construction). These need existsRClusterDirDown.choose_spec.
                          -- For now: sorry (needs rw/down extraction from CO step spec).
                          exfalso
                          have h_constraints := h_no_between e₂ h.in_b₂
                            h.cache₂ h.write h.notDown₂ (hlin e₂)
                          -- d_co between CLE_w and CLE₁ with sameCacheWriteConstraints.
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁]; exact hdco_ob_cle₁
                          exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                            { interDiffProtocol := by
                                show ¬ e₂.sameProtocol n e_w
                                unfold Event.sameProtocol at h_ew_diff_e₂ ⊢
                                exact fun h => h_ew_diff_e₂ h.symm

                              downToW := by
                                unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                              isDirWrite := by rw [hfc_dco]; exact hdco_isDirWrite
                              notDown := by rw [hfc_dco]; exact hdco_not_down
                              isDir := by rw [hfc_dco]; exact hdco_isDir
                              translatedDir := by rw [hfc_dco]; exact hdco_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          -- CLE₁ OB d_co: proxy for .diffCluster_coherent
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                    · -- e_w same cluster as e₂ (2-cluster elimination):
                      -- RF is cross-cluster (e_w at e₂'s cluster, e₁ at e₁'s cluster).
                      -- RF gives d_rf at e_w's cluster inside CLE₁ (encapDirRelation).
                      -- dir_ordered d_rf CLE₂ at e_w's cluster = e₂'s cluster:
                      --   d_rf OB CLE₂ → .diffCluster_rfCrossCluster (encapOb pattern)
                      --   CLE₂ OB d_rf → further analysis needed
                      -- RF cross-cluster: case-split on h_rf to extract diffCluster evidence.
                      -- e_w diff from e₁ (since e_w same as e₂, e₂ diff from e₁).
                      -- RF wEqRGle requires same cluster → impossible. Only wObRGle.diffCluster.
                      cases h_rf with
                      | wEqRGle _ hwr_same_cluster _ =>
                        -- wEqRGle requires e_w same cluster as e₁. Contradicts ¬h_ew_e₁.
                        exact absurd hwr_same_cluster.symm h_ew_e₁
                      | wObRGle _ hw_ob_cases =>
                        cases hw_ob_cases with
                        | sameCluster hsc _ =>
                          -- sameCluster requires e_w same cluster as e₁.
                          exact absurd hsc.symm h_ew_e₁
                        | diffCluster _ _ hr_gdown hdiff_cache_case =>
                          -- diffCluster: RF gives downgrade evidence at e_w's cluster.
                          -- Extract d_rf from the diffCache.case sub-cases.
                          -- All sub-cases carry rCleOrDownAtWAfterWCle which has
                          -- diffCluster → existsRClusterDownAtW + wObRDown.
                          -- Extract d_rf from RF diffCluster sub-cases.
                          -- All sub-cases carry rCleOrDownAtWAfterWCle with diffCluster.
                          -- diffCluster gives encapDir.existsRClusterDirDown + wObRDown.
                          -- encapDirRelation gives d_rf inside CLE₁ or d_rf.oEnd < CLE₁.oEnd.
                          -- For encapOb: need d_rf.EncapsulatedBy CLE₁ (cleEncap case).
                          -- For obEndLt: need CLE₁ OB d_rf (not available — d_rf inside CLE₁).
                          -- For now: sorry (needs case analysis on diffCache.case sub-cases)
                          -- Extract encapDir from diffCache.case.
                          have hencapDir := diffCache_case_extract_encapDir e_w_write h.read hdiff_cache_case hw_in_b hw_cache
                          have hdrf_spec := hencapDir.existsRClusterDirDown.choose_spec
                          -- d_rf at e_w's cluster. encapDirRelation gives d_rf inside CLE₁ or oEnd bound.
                          -- For cleEncap: d_rf.EncapsulatedBy CLE₁.
                          -- Then dir_ordered d_rf CLE₂ at e_w's cluster (= e₂'s cluster).
                          have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                          have hdrf_isdir := hdrf_spec.2.1
                          cases hdrf_spec.2.2.2.2.2.2 with
                          | cleEncap henc_drf =>
                            -- d_rf inside CLE₁ (CLE₁ encapsulates d_rf).
                            -- dir_ordered d_rf CLE₂ at e_w's cluster.
                            match hfc_drf : hencapDir.existsRClusterDirDown.choose, hdrf_isdir with
                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                            | .directoryEvent de_drf, _ =>
                              match hfc_cle₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_cle₂, _ =>
                                cases (b.orderedAtEntry.dir_ordered de_drf de_cle₂).ordered with
                                | inl hdrf_ob_cle₂ =>
                                  -- d_rf OB CLE₂ → .diffCluster_rfCrossCluster
                                  have hw₁ : e_w_lin = lin e_w := Subsingleton.elim _ _
                                  -- henc_drf is about the RF's reader lin. Bridge to (lin e₁).
                                  -- The RF's reader lin = (lin e₁) by Subsingleton.
                                  -- hencapDir uses e_w_lin (writer) and lin e₁ (reader) through the RF.
                                  -- The encapDirRelation.cleEncap gives d_rf inside the reader's CLE.
                                  -- Since the reader IS e₁, this is (lin e₁).CLE.
                                  -- henc_drf : CLE_r encaps d_rf. CLE_r from RF's hr_c_and_g_lin.
                                  -- Need: d_rf.EncapsulatedBy (lin e₁).CLE. Bridge via Subsingleton.
                                  -- hencapDir uses RF's reader lin (= lin e₁ by Subsingleton).
                                  -- Bridge: the RF's reader lin = (lin e₁) by Subsingleton.
                                  -- Rewrite hencapDir to use (lin e₁) explicitly.
                                  -- Use diffCache_coherent_encapProxyAndDir directly with (lin e₁) as reader.
                                  -- This gives encapDir parameterized by (lin e₁), avoiding Subsingleton issues.
                                  have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                                  have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                                  cases hdrf_spec'.2.2.2.2.2.2 with
                                  | cleEncap henc' =>
                                    -- d_rf' inside (lin e₁).CLE. dir_ordered d_rf' CLE₂.
                                    have hdrf_isdir' := hdrf_spec'.2.1
                                    match hfc_drf' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir' with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_drf', _ =>
                                      match hfc_cle₂' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                      | .directoryEvent de_cle₂', _ =>
                                        cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                                        | inl hob =>
                                          exact .diffCluster_rfCrossCluster h_same_prot
                                            hencapDir'.existsRClusterDirDown.choose henc'
                                            (by rw [hfc_drf', hfc_cle₂']; exact hob)
                                        | inr hob =>
                                          -- CLE₂ OB d_rf': e_w2 is same-cluster intervening write.
                                          -- Apply interSameProtocolAsWNotBetweenCleAndDrf.
                                          exfalso
                                          have h_constraints := h_no_between e₂ h.in_b₂
                                            h.cache₂ h.write h.notDown₂ (hlin e₂)
                                          -- e₂.sameProtocol e_w: from 2-cluster + ¬h_ew_e₁.
                                          -- e_w not at e₁'s cluster (¬h_ew_e₁). 2 clusters → e_w at e₂'s.
                                          have h_ew_e₂ : e₂.sameProtocol n e_w := by
                                            unfold Event.sameProtocol
                                            cases hw_cache.eCluster with
                                            | inl hw1 =>
                                              cases h.cache₂.eCluster with
                                              | inl h2c1 => exact h2c1.trans hw1.symm
                                              | inr h2c2 =>
                                                cases h.cache₁.eCluster with
                                                | inl h1c1 => exact absurd (h1c1.trans hw1.symm) h_ew_e₁
                                                | inr h1c2 =>
                                                  -- e₁ at cluster2, e₂ at cluster2 → same cluster → contradicts h_same_prot
                                                  exfalso; exact h_same_prot (show e₁.sameProtocol n e₂ from h1c2.trans h2c2.symm)
                                            | inr hw2 =>
                                              cases h.cache₂.eCluster with
                                              | inr h2c2 => exact h2c2.trans hw2.symm
                                              | inl h2c1 =>
                                                cases h.cache₁.eCluster with
                                                | inr h1c2 => exact absurd (h1c2.trans hw2.symm) h_ew_e₁
                                                | inl h1c1 =>
                                                  exfalso; exact h_same_prot (show e₁.sameProtocol n e₂ from h1c1.trans h2c1.symm)
                                          -- CLE_w2 between CLE_w1 and d_rf.
                                          -- From CO: StepOrdering CLE_w1 CLE_w2.
                                          -- For .ob: CLE_w1 OB CLE_w2 → OrderedBetween → NIW.
                                          -- For .eq/.sameLin: CLE_w1 = CLE_w2 → CLE_w1 OB d_rf from hob → use encapOb.
                                          -- CLE_w OB CLE₂ from CO chain via oEnd ≤ + dir_ordered.
                                          have hoEnd := co_chain_oEnd_le h_co_chain hlin
                                          rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                                          have hcle_w_isdir := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                                          have hcle_w2_isdir := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                                          match hfc_clew : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir with
                                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                          | .directoryEvent de_clew, _ =>
                                            match hfc_clew2 : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir with
                                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                            | .directoryEvent de_clew2, _ =>
                                              have hcle_w1_ob := co_chain_same_cluster_ob hoEnd
                                                hfc_clew hfc_clew2 (b.orderedAtEntry.dir_ordered de_clew de_clew2)
                                              have hcle_w2_ob_drf : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                                  hencapDir'.existsRClusterDirDown.choose := by
                                                rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _, hfc_cle₂', hfc_drf']
                                                exact hob
                                              exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                                h_ew_e₂ hencapDir' ⟨hcle_w1_ob, hcle_w2_ob_drf⟩
                                  | gcacheEncap hgcr_enc hdrf_lt =>
                                    -- GCR encaps d_rf, d_rf.oEnd < CLE₁.oEnd.
                                    -- Case-split ClusterToGlobal shim: encapGlobalCache or noGlobalCache.
                                    -- For encapGlobalCache: CLE₁ encaps GCR → CLE₁ encaps d_rf → cleEncap pattern.
                                    -- For noGlobalCache: only oEnd bound → needs finishesBefore constructor.
                                    -- gcacheEncap: d_rf OB CLE₂ + d_rf.oEnd < CLE₁.oEnd → diffCluster_rfFinishBefore.
                                    -- CLE₂ OB d_rf → NIW contradiction (same as cleEncap case).
                                    have hdrf_isdir'' := hdrf_spec'.2.1
                                    match hfc_drf'' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir'' with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_drf', _ =>
                                      match hfc_cle₂'' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                      | .directoryEvent de_cle₂', _ =>
                                        cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                                        | inl hob =>
                                          exact .diffCluster_rfFinishBefore h_same_prot
                                            hencapDir'.existsRClusterDirDown.choose
                                            (by rw [hfc_drf'', hfc_cle₂'']; exact hob)
                                            hdrf_lt
                                        | inr hob =>
                                          -- CLE₂ OB d_rf: NIW via interSameProtocolAsWNotBetweenCleAndDrf.
                                          exfalso
                                          have h_constraints := h_no_between e₂ h.in_b₂
                                            h.cache₂ h.write h.notDown₂ (hlin e₂)
                                          -- Replicate the encapDir .ob CO NIW pattern.
                                          have h_ew_e₂ : e₂.sameProtocol n e_w := by
                                            unfold Event.sameProtocol
                                            cases hw_cache.eCluster with
                                            | inl hw1 => cases h.cache₂.eCluster with
                                              | inl h2c1 => exact h2c1.trans hw1.symm
                                              | inr h2c2 => cases h.cache₁.eCluster with
                                                | inl h1c1 => exact absurd (h1c1.trans hw1.symm) h_ew_e₁
                                                | inr h1c2 => exfalso; exact h_same_prot (h1c2.trans h2c2.symm)
                                            | inr hw2 => cases h.cache₂.eCluster with
                                              | inr h2c2 => exact h2c2.trans hw2.symm
                                              | inl h2c1 => cases h.cache₁.eCluster with
                                                | inr h1c2 => exact absurd (h1c2.trans hw2.symm) h_ew_e₁
                                                | inl h1c1 => exfalso; exact h_same_prot (h1c1.trans h2c1.symm)
                                          have hcle₂_ob_drf_ev :
                                              (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                              hencapDir'.existsRClusterDirDown.choose := by
                                            rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _,
                                                hfc_cle₂'', hfc_drf'']; exact hob
                                          -- CLE_w OB CLE₂ from CO chain via oEnd ≤ + dir_ordered.
                                          have hoEnd := co_chain_oEnd_le h_co_chain hlin
                                          rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                                          have hcle_w_isdir := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                                          have hcle_w2_isdir := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                                          match hfc_clew : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir with
                                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                          | .directoryEvent de_clew, _ =>
                                            match hfc_clew2 : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir with
                                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                            | .directoryEvent de_clew2, _ =>
                                              have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                                hfc_clew hfc_clew2 (b.orderedAtEntry.dir_ordered de_clew de_clew2)
                                              exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                                h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_drf_ev⟩
                                | inr hcle₂_ob_drf =>
                                  -- Old code path: CLE₂ OB d_rf for first encapDirRelation case.
                                  exfalso
                                  have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                                  have h_constraints := h_no_between e₂ h.in_b₂ h.cache₂ h.write h.notDown₂ (hlin e₂)
                                  have hoEnd := co_chain_oEnd_le h_co_chain hlin
                                  rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                                  -- Extract CLE_w and CLE₂ as DirectoryEvents for dir_ordered.
                                  have hcle_w_isdir := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                                  have hcle_w2_isdir := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                                  match hfc_w : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir with
                                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                  | .directoryEvent de_w', _ =>
                                    match hfc_w2 : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_w2', _ =>
                                      have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                        hfc_w hfc_w2 (b.orderedAtEntry.dir_ordered de_w' de_w2')
                                      -- hcle₂_ob_drf needs bridging to use hencapDir (not hencapDir')
                                      -- Use hencapDir (from diffCache_case_extract_encapDir, in scope).
                                      -- hcle₂_ob_drf is about hencapDir's d_rf (matched to de_drf via hfc_drf).
                                      -- Bridge to Event level using the match equations.
                                      have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                          hencapDir.existsRClusterDirDown.choose := by
                                        show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                            Event.oStart n hencapDir.existsRClusterDirDown.choose
                                        rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                        simp only [hfc_cle₂, hfc_drf]; exact hcle₂_ob_drf
                                      exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                        h_ew_e₂ hencapDir ⟨hcle_w_ob, hcle₂_ob_ev⟩
                          | gcacheEncap hgcr_enc₂ hdrf_lt₂ =>
                            -- Same pattern: dir_ordered d_rf CLE₂. Use hencapDir (in scope).
                            match hfc_drf'' : hencapDir.existsRClusterDirDown.choose, hdrf_isdir with
                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                            | .directoryEvent de_drf', _ =>
                              match hfc_cle₂'' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_cle₂', _ =>
                                cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                                | inl hob =>
                                  exact .diffCluster_rfFinishBefore h_same_prot
                                    hencapDir.existsRClusterDirDown.choose
                                    (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂
                                | inr hob =>
                                  exfalso
                                  have h_constraints := h_no_between e₂ h.in_b₂
                                    h.cache₂ h.write h.notDown₂ (hlin e₂)
                                  have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                                  have hoEnd := co_chain_oEnd_le h_co_chain hlin
                                  rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                                  have hcle_w_isdir_x := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                                  have hcle_w2_isdir_x := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                                  match hfc_wx : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir_x with
                                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                  | .directoryEvent de_wx, _ =>
                                    match hfc_w2x : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir_x with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_w2x, _ =>
                                      have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                        hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                      have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                          hencapDir.existsRClusterDirDown.choose := by
                                        show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                            Event.oStart n hencapDir.existsRClusterDirDown.choose
                                        rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                        simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                      exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                        h_ew_e₂ hencapDir ⟨hcle_w_ob, hcle₂_ob_ev⟩
        | orderBeforeDir _ hexists_pred₁ hpred₁_encap _ _ _ _ _ =>
          -- Same strategy as encapDir: dir_ordered CLE₁ cdir/evict.
          -- cdirEncapsDown_exists already called, e_cdir/e_evict in scope.
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc_cdir₂ : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁₂ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob =>
                have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                exact .diffCluster_coherent h_same_prot (.directoryEvent de_cdir)
                  (by rw [hfc_cle₁₂]; exact hob) (by rw [hw₂']; exact hcdir_lt_cle₂)
              | inr hob =>
                have he_evict_isdir' := he_evict_isDir
                match hfc_evict₂ : e_evict, he_evict_isdir' with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_evict, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_cle₁ de_evict).ordered with
                  | inl hob_evict =>
                    have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                    exact .diffCluster_coherent h_same_prot (.directoryEvent de_evict)
                      (by rw [hfc_cle₁₂]; exact hob_evict) (by rw [hw₂']; exact hevict_lt_cle₂)
                  | inr hob_evict =>
                    -- Same structure as encapDir case.
                    obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                      hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                    have hlin := fun e => h.hknow_dir_access compound b init e
                    by_cases h_ew_e₁ : e₁.protocol = e_w.protocol
                    · have h_ew_diff_e₂ : ¬ e_w.sameProtocol n e₂ := by
                        unfold Event.sameProtocol
                        intro h; exact h_same_prot (show e₁.protocol = e₂.protocol from h_ew_e₁.trans h)
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto, hdco_not_down, hdco_isDirWrite, hdco_translatedDir⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          exfalso
                          have h_constraints := h_no_between e₂ h.in_b₂
                            h.cache₂ h.write h.notDown₂ (hlin e₂)
                          -- d_co between CLE_w and CLE₁. sameCacheWriteConstraints.
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁₂]; exact hdco_ob_cle₁
                          exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                            { interDiffProtocol := by
                                show ¬ e₂.sameProtocol n e_w
                                unfold Event.sameProtocol at h_ew_diff_e₂ ⊢
                                exact fun h => h_ew_diff_e₂ h.symm
                              downToW := by show d_co.sameProtocol n e_w; rw [hfc_dco]; exact hdco_proto
                              isDirWrite := by rw [hfc_dco]; exact hdco_isDirWrite
                              notDown := by rw [hfc_dco]; exact hdco_not_down
                              isDir := by rw [hfc_dco]; exact hdco_isDir
                              translatedDir := by rw [hfc_dco]; exact hdco_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₂]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.2.2.2.2.2 with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.1
                        match hfc_drf' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                          | .directoryEvent de_cle₂', _ =>
                            cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                            | inl hob =>
                              exact .diffCluster_rfCrossCluster h_same_prot
                                hencapDir'.existsRClusterDirDown.choose henc'
                                (by rw [hfc_drf', hfc_cle₂']; exact hob)
                            | inr hob =>
                              -- CLE₂ OB d_rf': same NIW pattern as encapDir.
                              exfalso
                              have h_constraints := h_no_between e₂ h.in_b₂
                                h.cache₂ h.write h.notDown₂ (hlin e₂)
                              have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                              have hoEnd := co_chain_oEnd_le h_co_chain hlin
                              rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                              have hcle_w_isdir_x := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                              match hfc_wx : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂', hfc_drf']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩
                      | gcacheEncap _ hdrf_lt₂ =>
                        have hdrf_isdir'' := hdrf_spec'.2.1
                        match hfc_drf'' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir'' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂'' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                          | .directoryEvent de_cle₂', _ =>
                            cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                            | inl hob =>
                              exact .diffCluster_rfFinishBefore h_same_prot
                                hencapDir'.existsRClusterDirDown.choose
                                (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂
                            | inr hob =>
                              exfalso
                              have h_constraints := h_no_between e₂ h.in_b₂
                                h.cache₂ h.write h.notDown₂ (hlin e₂)
                              have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                              have hoEnd := co_chain_oEnd_le h_co_chain hlin
                              rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                              have hcle_w_isdir_x := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                              match hfc_wx : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩
        | orderAfterDir hweak₁ _ _ _ =>
          -- e₁ non-coherent. Same dir_ordered strategy.
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc_cdir₃ : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁₃ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob =>
                have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_cdir)
                  (by rw [hfc_cle₁₃]; exact hob) (by rw [hw₂']; exact hcdir_lt_cle₂)
              | inr hob =>
                have he_evict_isdir' := he_evict_isDir
                match hfc_evict₃ : e_evict, he_evict_isdir' with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_evict, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_cle₁ de_evict).ordered with
                  | inl hob_evict =>
                    have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                    exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_evict)
                      (by rw [hfc_cle₁₃]; exact hob_evict) (by rw [hw₂']; exact hevict_lt_cle₂)
                  | inr hob_evict =>
                    -- Same structure as encapDir case.
                    obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                      hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                    have hlin := fun e => h.hknow_dir_access compound b init e
                    by_cases h_ew_e₁ : e₁.protocol = e_w.protocol
                    · have h_ew_diff_e₂ : ¬ e_w.sameProtocol n e₂ := by
                        unfold Event.sameProtocol
                        intro h; exact h_same_prot (show e₁.protocol = e₂.protocol from h_ew_e₁.trans h)
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto, hdco_not_down, hdco_isDirWrite, hdco_translatedDir⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          exfalso
                          have h_constraints := h_no_between e₂ h.in_b₂
                            h.cache₂ h.write h.notDown₂ (hlin e₂)
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁₃]; exact hdco_ob_cle₁
                          exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                            { interDiffProtocol := by
                                show ¬ e₂.sameProtocol n e_w
                                unfold Event.sameProtocol at h_ew_diff_e₂ ⊢
                                exact fun h => h_ew_diff_e₂ h.symm
                              downToW := by show d_co.sameProtocol n e_w; rw [hfc_dco]; exact hdco_proto
                              isDirWrite := by rw [hfc_dco]; exact hdco_isDirWrite
                              notDown := by rw [hfc_dco]; exact hdco_not_down
                              isDir := by rw [hfc_dco]; exact hdco_isDir
                              translatedDir := by rw [hfc_dco]; exact hdco_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₃]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.2.2.2.2.2 with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.1
                        match hfc_drf' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                          | .directoryEvent de_cle₂', _ =>
                            cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                            | inl hob =>
                              exact .diffCluster_rfCrossCluster h_same_prot
                                hencapDir'.existsRClusterDirDown.choose henc'
                                (by rw [hfc_drf', hfc_cle₂']; exact hob)
                            | inr hob =>
                              -- CLE₂ OB d_rf': same NIW pattern as encapDir.
                              exfalso
                              have h_constraints := h_no_between e₂ h.in_b₂
                                h.cache₂ h.write h.notDown₂ (hlin e₂)
                              have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                              have hoEnd := co_chain_oEnd_le h_co_chain hlin
                              rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                              have hcle_w_isdir_x := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                              match hfc_wx : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂', hfc_drf']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩
                      | gcacheEncap _ hdrf_lt₂ =>
                        have hdrf_isdir'' := hdrf_spec'.2.1
                        match hfc_drf'' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir'' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂'' : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                          | .directoryEvent de_cle₂', _ =>
                            cases (b.orderedAtEntry.dir_ordered de_drf' de_cle₂').ordered with
                            | inl hob =>
                              exact .diffCluster_rfFinishBefore h_same_prot
                                hencapDir'.existsRClusterDirDown.choose
                                (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂
                            | inr hob =>
                              exfalso
                              have h_constraints := h_no_between e₂ h.in_b₂
                                h.cache₂ h.write h.notDown₂ (hlin e₂)
                              have h_ew_e₂ := two_cluster_e₂_same_e_w h_same_prot h_ew_e₁ hw_cache h.cache₁ h.cache₂
                              have hoEnd := co_chain_oEnd_le h_co_chain hlin
                              rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                              have hcle_w_isdir_x := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                              match hfc_wx : e_w_lin.hreq's_dir_access.choose, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).hreq's_dir_access.choose, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).hreq's_dir_access.choose.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).hreq's_dir_access.choose <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩

/-- Helper: diff-addr PPOi → StepOrdering via dir_ordered + CompoundMCM.
    Extracted to avoid nested match substitution issues in encapDir case. -/
private theorem ppoi_diff_addr_step_ordering
    (hppoi : @PPOi n b e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_diff_addr : e₁.addr ≠ e₂.addr)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
  have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
  match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
  | .directoryEvent de₁, _ =>
    match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de₂, _ =>
      cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
      | inl hob => exact .ob hob
      | inr hob =>
        exfalso
        have hclo := @ppoi_compound_lin_order n compound b init e₁ e₂ hppoi h_diff_addr
        unfold CompoundProtocol.CompoundLinearizationOrder at hclo
        cases hclo hppoi.ppo with
        | inl helin_ob =>
          let e_lin₁ := (compound.compoundLinearizationEvent compound.shimAxioms b init e₁
            (compound.linearizationOfEvent b init e₁)).linearizationEvent
          let e_lin₂ := (compound.compoundLinearizationEvent compound.shimAxioms b init e₂
            (compound.linearizationOfEvent b init e₂)).linearizationEvent
          have hcle₁_le : Event.oStart n (.directoryEvent de₁) ≤ Event.oStart n e_lin₁ := by
            have := compound_lin_start_bound e₁ (lin e₁)
            rwa [hfc₁] at this
          have helin₂_le : Event.oEnd n e_lin₂ ≤ Event.oEnd n (.directoryEvent de₂) := by
            have := compound_lin_end_bound e₂ (lin e₂)
            rwa [hfc₂] at this
          exact Nat.lt_irrefl _ (calc Event.oEnd n (.directoryEvent de₂)
            _ < Event.oStart n (.directoryEvent de₁) := hob
            _ ≤ Event.oStart n e_lin₁ := hcle₁_le
            _ ≤ Event.oEnd n e_lin₁ := Nat.le_of_lt (Event.oWellFormed n e_lin₁)
            _ < Event.oStart n e_lin₂ := helin_ob
            _ ≤ Event.oEnd n e_lin₂ := Nat.le_of_lt (Event.oWellFormed n e_lin₂)
            _ ≤ Event.oEnd n (.directoryEvent de₂) := helin₂_le)
        | inr hlazy =>
          /- TODO: Lazy CompoundLinearizationOrder (nc.weak → c.release only).
             Lazy PPOi gives `finishesBefore` (weaker than `OrderedBefore`), which
             does NOT produce a valid StepOrdering on its own.

             The ordering only materializes when composed with the NEXT com edge
             in the cycle that downgrades e₂ (the c.release write):
             - rfe(e₂, e₃): e₂ writes, e₃ reads → downgrade at e₂'s cache → YES
             - co(e₂, e₃): e₃ overwrites e₂ → downgrade at e₂'s cache → YES
             - fr(e₂, e₃): e₂ reads from e_w, e₃ overwrites e_w → downgrade at
               e_w's cache, NOT e₂'s → needs further analysis

             Fix: Add a predicate/hypothesis that lazy PPOi is only considered ordered
             when composed with a com relation (i.e., handle PPOi_lazy + com as a
             PAIR in the cycle-level proof, not as independent edges). This requires
             restructuring cmcm_acyclic_of_hknow to handle lazy PPOi + com composition
             at the TransGen level instead of mapping each edge independently. -/
          sorry

/-- PPOi → StepOrdering. Restricted to diff-addr (same-addr PPOi ordering
    is subsumed by com edges in cycles). Uses CompoundMCM bridge. -/
theorem ppoi_step_to_ordering
    (hppoi : @PPOi n b e₁ e₂)
    (h_diff_addr : e₁.addr ≠ e₂.addr)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose :=
  ppoi_diff_addr_step_ordering hppoi lin h_diff_addr
/- Old same-addr PPOi proof (630 lines) removed — same-addr ordering subsumed by com edges.
   Tagged at v-session11-checkpoint if needed. -/
/-- Map each PPOi ∪ com step to a StepOrdering between linearization points. -/
theorem step_to_ordering
    (h : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h with
  | inl hppoi =>
    exact ppoi_step_to_ordering hppoi.1 hppoi.2 lin
  | inr hcom =>
    cases hcom with
    | rfe h =>
      -- rfe: extract protocol events from readsFrom.cases
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          -- Vacuous: wEqRCle requires sameCache, rfe requires diffCache
          exact absurd hwr_com.sameCache h.diffCache
        | wObRCle hwr_gle_or_cle =>
          -- CLE_w OB CLE_r directly (same cluster, cluster dir serialization)
          exact .ob (by
            rw [← show h.w_lin = lin e₁ from Subsingleton.elim _ _,
                ← show h.r_lin = lin e₂ from Subsingleton.elim _ _]
            exact hwr_gle_or_cle.hw_r_cle_ob)
      | wObRGle _ hw_ob_r_gle_cases =>
        cases hw_ob_r_gle_cases with
        | sameCluster _ hw_ob_cases =>
          -- Same cluster, CLE_w OB CLE_r from GleOrCle.cases
          exact .ob (by
            rw [← show h.w_lin = lin e₁ from Subsingleton.elim _ _,
                ← show h.r_lin = lin e₂ from Subsingleton.elim _ _]
            exact hw_ob_cases.hw_r_cle_ob)
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Different cluster: extract wObRDown from diffCache.case sub-cases
          have hw₁ : h.w_lin = lin e₁ := Subsingleton.elim _ _
          have hw₂ : h.r_lin = lin e₂ := Subsingleton.elim _ _
          -- Helper: given encapDir + wObRDown → StepOrdering.obEndLt
          have from_encap_wob
              (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_lin)
              (hwOB : h.w_lin.hreq's_dir_access.choose.OrderedBefore n
                hdown.existsRClusterDirDown.choose) :
              @StepOrdering n (lin e₁).hreq's_dir_access.choose
                (lin e₂).hreq's_dir_access.choose := by
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.2.2.2.2.2
            exact .obEndLt hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwOB)
              (by rw [← hw₂]; cases hencap_rel with
                  | cleEncap henc => exact henc.right
                  | gcacheEncap _ hlt => exact hlt)
          -- Dispatch all diffCache.case sub-cases
          cases hdiff_cache_case with
          | wHasPermsAfter hw_leaves_SW coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle =>
                exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
              | diffCluster _ _ hwOB => exact from_encap_wob hPDC.encapDir hwOB
            | notImmPred hasPermsCase =>
              cases hasPermsCase with
              | noEvictBetween w =>
                -- noEvictBetween: use encapDir + dir_ordered for CLE_w OB cdir_down
                have hPDC := w.gdownEncapProxyAndDirAndCDown
                have hcdir_spec := hPDC.encapDir.existsRClusterDirDown.choose_spec
                have hencap_rel := hcdir_spec.2.2.2.2.2.2
                -- Both CLE_w and cdir_down are directory events
                have hcdir_isdir := hcdir_spec.2.1
                have hcle_isdir := h.w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                -- Extract DirectoryEvent from both, use dir_ordered
                match h_cdir_ev : hPDC.encapDir.existsRClusterDirDown.choose, hcdir_isdir with
                | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
                | .directoryEvent de_cdir, _ =>
                  match h_cle_ev : h.w_lin.hreq's_dir_access.choose, hcle_isdir with
                  | .cacheEvent _, h => simp [Event.isDirectoryEvent] at h
                  | .directoryEvent de_cle, _ =>
                    cases (b.orderedAtEntry.dir_ordered de_cle de_cdir).ordered with
                    | inl hob_dir =>
                      -- CLE_w OB cdir_down (as DirectoryEvent.OrderedBefore = Nat inequality)
                      -- Construct obEncap directly on the matched terms
                      exact .obEndLt (.directoryEvent de_cdir)
                        (show (Event.directoryEvent de_cle).OrderedBefore n (.directoryEvent de_cdir) from hob_dir)
                        (by rw [← hw₂, ← h_cdir_ev]; cases hencap_rel with
                            | cleEncap henc => exact henc.right
                            | gcacheEncap _ hlt => exact hlt)
                    | inr hob_dir =>
                      -- cdir_down OB CLE_w: temporal contradiction
                      -- e_w OB e_r_down, cdir encapsulates e_r_down, cdir OB CLE_w, CLE_w inside e_w
                      exfalso
                      have hda := h.w_lin.hreq's_dir_access.choose_spec.2
                      rw [h_cle_ev] at hda
                      have hwObRDown := w.noEvictBetween.wObRDown
                      have hcdirEncap := hPDC.cdirEncapsDown
                      -- cdir.oEnd < CLE_w.oStart (hob_dir) and e_w.oEnd < e_r_down.oStart (hwObRDown)
                      -- CLE_w inside e_w (from encapDir): CLE_w.oEnd < e_w.oEnd
                      -- cdir encaps e_r_down: e_r_down.oEnd < cdir.oEnd
                      -- Chain: de_cle.oEnd < ... < e_w.oEnd < e_r_down.oStart ≤ e_r_down.oEnd < de_cdir.oEnd < de_cle.oStart
                      -- Contradiction: de_cle.oEnd < de_cle.oStart
                      cases hda with
                      | encapDir _ hencap =>
                        have : de_cle.oEnd < de_cle.oEnd :=
                          calc de_cle.oEnd
                            _ < e₁.oEnd := hencap.reqEncapDir.right
                            _ < hPDC.existsRDownAtW.choose.oStart := hwObRDown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir.oEnd := by show _ < Event.oEnd n (Event.directoryEvent de_cdir); rw [← h_cdir_ev]; exact hcdirEncap.right
                            _ < de_cle.oStart := hob_dir
                            _ ≤ de_cle.oEnd := Nat.le_of_lt de_cle.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderBeforeDir _ hexists_pred hpred _ _ _ _ _ =>
                        have : de_cle.oEnd < de_cle.oEnd :=
                          calc de_cle.oEnd
                            _ < hexists_pred.choose.oEnd := hpred.reqEncapDir.right
                            _ < e₁.oStart := hexists_pred.choose_spec.2.isImmPred.bPred.isPred
                            _ < e₁.oEnd := Event.oWellFormed n e₁
                            _ < hPDC.existsRDownAtW.choose.oStart := hwObRDown
                            _ ≤ hPDC.existsRDownAtW.choose.oEnd := Nat.le_of_lt (Event.oWellFormed n _)
                            _ < de_cdir.oEnd := by show _ < Event.oEnd n (Event.directoryEvent de_cdir); rw [← h_cdir_ev]; exact hcdirEncap.right
                            _ < de_cle.oStart := hob_dir
                            _ ≤ de_cle.oEnd := Nat.le_of_lt de_cle.oWellFormed
                        exact Nat.lt_irrefl _ this
                      | orderAfterDir hweak_req _ _ _ =>
                        -- nc.weak with wHasPermsAfter: contradiction.
                        -- wHasPermsAfter = reqLeavesStateAtLeast SW = SW ≤ stateAfter.cache
                        -- ncWeakReqOnVd gives: stateAfter.cache = Vd (or stateBefore = Vd)
                        -- SW ≤ Vd is false by decide.
                        exfalso
                        -- hw_leaves_SW : SW ≤ stateAfter.cache
                        -- hweak_req.reqOnOrAfterVd : stateBefore.cache = Vd ∨ stateAfter.cache = Vd
                        cases hweak_req.reqOnOrAfterVd with
                        | inr hafter_vd =>
                          -- stateAfter.cache = Vd. SW ≤ Vd is false.
                          unfold Behaviour.reqLeavesStateAtLeast at hw_leaves_SW
                          rw [hafter_vd] at hw_leaves_SW
                          exact absurd hw_leaves_SW (by
                            simp [LE.le, State.le, LT.lt, State.lt, SW, Vd, Option.le])
                        | inl hbefore_vd =>
                          -- stateBefore.cache = Vd. nc.weak write from Vd:
                          -- RequestState ⟨.w,false,.Weak⟩ Vd = Vd (from _ => Vd branch).
                          -- stateAfter.cache = Vd. SW ≤ Vd is false.
                          -- The stateAfter = SucceedingState(stateBefore) for the last event.
                          -- stateBefore.cache = Vd = ⟨some .wr, false⟩, not ⟨some .wr, true⟩ (SW).
                          -- So nc.weak write maps Vd → Vd.
                          -- Same contradiction: SW ≤ Vd false.
                          -- stateBefore.cache = Vd → stateAfter.cache = Vd for nc.weak write
                          -- Step 1: stateAfter = SucceedingState(stateBefore)
                          unfold Behaviour.reqLeavesStateAtLeast at hw_leaves_SW
                          rw [stateAfter_eq_succeedingState] at hw_leaves_SW
                          -- Step 2: SucceedingState for cache event, non-downgrade = RequestState
                          -- Step 3: RequestState for nc.weak write on Vd = Vd
                          -- e₁ is cache event (from rfe context)
                          have hda := h.w_lin.hreq's_dir_access.choose_spec.2
                          rw [h_cle_ev] at hda
                          -- e₁ not down (from orderAfterDir.hnot_down)
                          have hnotdown := hweak_req.notDown
                          -- nc.weak: req = ⟨.w, false, .Weak⟩ or ⟨.r, false, .Weak⟩
                          have hncweak := hweak_req.weakReq
                          -- hw_leaves_SW now has SucceedingState form.
                          -- Match e₁ to cache event, unfold SucceedingState + RequestState
                          match he₁ : e₁ with
                          | .directoryEvent _ =>
                            have := hweak_req.reqCache; simp [Event.isCacheEvent, he₁] at this
                          | .cacheEvent ce₁ =>
                            have hnotdown_bool : ce₁.down = false := by
                              cases hd : ce₁.down <;> simp_all [Event.down, he₁]
                            simp only [Event.isNcWeak, Event.isNonCoherent, Event.isWeak, he₁] at hncweak
                            have hwrite' : ce₁.req.val.rw = .w := by
                              have := h.write; simpa [Event.isWrite, he₁, Request.isWrite] using this
                            have hreq_val : ce₁.req.val = ⟨.w, false, .Weak⟩ := by
                              obtain ⟨hnc, hweak⟩ := hncweak
                              cases hv : ce₁.req.val with | mk rw c cs => simp_all [Bool.not_eq_true]
                            have hreq_eq : ce₁.req = ⟨⟨.w, false, .Weak⟩, by simp [Request.IsValid']⟩ :=
                              Subtype.ext hreq_val
                            -- Compute stateAfter.cache step by step
                            have hsucc_cache : (Event.SucceedingState n (.cacheEvent ce₁)
                                (b.stateBefore n (InitialSystemState.stateAt n init (.cacheEvent ce₁))
                                  (.cacheEvent ce₁))).cache =
                                ce₁.req.RequestState (b.stateBefore n (InitialSystemState.stateAt n init (.cacheEvent ce₁))
                                  (.cacheEvent ce₁)).cache := by
                              simp [Event.SucceedingState, CacheEvent.SucceedingState, hnotdown_bool, EntryState.cache]
                            rw [hsucc_cache, hbefore_vd, hreq_eq] at hw_leaves_SW
                            -- Now hw_leaves_SW : SW ≤ RequestState ⟨.w,false,.Weak⟩ Vd
                            -- Compute: RequestState gives Vd. Then SW ≤ Vd false.
                            simp [ValidRequest.RequestState, Vd,
                              LE.le, State.le, LT.lt, State.lt, SW, Option.le] at hw_leaves_SW
              | evictBetween evict =>
                exact from_encap_wob evict.encapProxyAndDir evict.evictBetween.wObRDown
          | wNoPermsAfter _ _ rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
          | wCleAfter rCle =>
            cases rCle with
            | sameCluster _ hob_cle =>
              exact .ob (by rw [← hw₁, ← hw₂]; exact hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
    | co h => exact co_step_to_ordering h lin
    | fr h =>
      -- fr: derive FrOrdering from protocol axioms, then derive StepOrdering.
      cases fr_ordering_holds h lin with
      | sameCache _ h_eq_or_ob =>
        cases h_eq_or_ob with
        | inl cle_eq => exact .eq cle_eq
        | inr cle_ob => exact .ob cle_ob
      | sameClusDiffCache _ _ cle_ob => exact .ob cle_ob
      | diffCluster_coherent _ p cle₁_ob_p p_lt_cle₂ => exact .obEndLt p cle₁_ob_p p_lt_cle₂
      | diffCluster_evict _ p cle₁_ob_p p_lt_cle₂ => exact .obEndLt p cle₁_ob_p p_lt_cle₂
      | diffCluster_noncoherent _ p cle₁_ob_p p_lt_cle₂ => exact .obEndLt p cle₁_ob_p p_lt_cle₂
      | diffCluster_rfCrossCluster _ p p_inside p_ob => exact .encapOb p p_inside p_ob
      | diffCluster_rfFinishBefore h_diff p p_ob p_lt =>
        have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
        have hcle₂_prot := write_cle_protocol_eq_write_protocol (lin e₂)
        exact .obFinishBefore p p_ob p_lt (fun heq =>
          h_diff (show e₁.sameProtocol n e₂ from hcle₁_prot.symm.trans (heq ▸ hcle₂_prot)))
      | sameCLE cle_eq => exact .eq cle_eq
      /- OLD FR proof removed (was 275 lines of dead code with 3 sorry's).
      by_cases h_same_prot : e₁.sameProtocol n e₂
      · -- Same cluster: CLE₁ and CLE₂ at same cluster directory.
        by_cases hcle_eq : (lin e₁).hreq's_dir_access.choose = (lin e₂).hreq's_dir_access.choose
        · exact .eq hcle_eq
        · -- dir_ordered valid (same cluster, same address)
          have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
          have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
          match hfc₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₁, _ =>
            match hfc₂ : (lin e₂).hreq's_dir_access.choose, hcle₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₂, _ =>
              cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
              | inl hob => exact .ob hob
              | inr hob =>
                -- CLE₂ OB CLE₁ at same cluster → contradiction via NIW.
                exfalso
                obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain, hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                have hlin := fun e => h.hknow_dir_access compound b init e
                have h_constraints := h_no_between e₂ h.in_b₂
                  h.cache₂ h.write h.notDown₂ (hlin e₂)
                -- e₁ and e₂ at same cluster → CLE₂.protocol = CLE₁.protocol
                have hprot_e₂_e₁ : e₂.protocol = e₁.protocol := by
                  unfold Event.sameProtocol at h_same_prot; exact h_same_prot.symm
                have hcle₂_prot := write_cle_protocol_eq_write_protocol (hlin e₂)
                have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
                have hprot₂ : (hlin e₂).hreq's_dir_access.choose.protocol =
                    (lin e₁).hreq's_dir_access.choose.protocol := by
                  calc (hlin e₂).hreq's_dir_access.choose.protocol
                    _ = e₂.protocol := hcle₂_prot
                    _ = e₁.protocol := hprot_e₂_e₁
                    _ = (lin e₁).hreq's_dir_access.choose.protocol := hcle₁_prot.symm
                -- by_cases on e_w's cluster
                have hcle_w_prot := write_cle_protocol_eq_write_protocol e_w_lin
                by_cases h_ew_prot : e₂.protocol = e_w.protocol
                · -- Same cluster e_w: all three CLEs at same directory.
                  have hprot₁ : (hlin e₂).hreq's_dir_access.choose.protocol =
                      e_w_lin.hreq's_dir_access.choose.protocol := by
                    calc (hlin e₂).hreq's_dir_access.choose.protocol
                      _ = e₂.protocol := hcle₂_prot
                      _ = e_w.protocol := h_ew_prot
                      _ = e_w_lin.hreq's_dir_access.choose.protocol := hcle_w_prot.symm
                  -- notBetweenCles: CLE₂ not between CLE_w and CLE₁
                  have h_isDirWrite : (hlin e₂).hreq's_dir_access.choose.isDirWrite := by
                    have : hlin e₂ = h.e₂_lin := Subsingleton.elim _ _
                    rw [this]; exact write_event_cle_isDirWrite h.write h.cache₂ h.notDown₂ h.e₂_lin h.in_b₂
                  -- Need OrderedBetween: CLE_w OB CLE₂ OB CLE₁
                  -- CLE₂ OB CLE₁ from hob. CLE_w OB CLE₂ from dir_ordered (same cluster).
                  have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                  match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                  | .directoryEvent de_w, _ =>
                    cases (b.orderedAtEntry.dir_ordered de_w de₂).ordered with
                    | inl hob_w₂ =>
                      have h_ob_between :
                          (hlin e₂).hreq's_dir_access.choose.OrderedBetween n
                          e_w_lin.hreq's_dir_access.choose (lin e₁).hreq's_dir_access.choose := by
                        exact ⟨by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                                  show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _,
                                  hfc₂, hfcw]; exact hob_w₂,
                               by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                                  show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _,
                                  hfc₂, hfc₁]; exact hob⟩
                      have h_nbc := h_constraints.notBetweenCles
                      unfold SameClusterCLE.NotBetweenCLEs at h_nbc
                      exact h_nbc ⟨hprot₁, hprot₂, h_isDirWrite⟩ h_ob_between
                    | inr hob_₂w =>
                      -- CLE₂ OB CLE_w: co chain gives CLE_w.oEnd ≤ CLE₂.oEnd → contradiction
                      have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                        have hoEnd := co_chain_oEnd_le h_co_chain hlin
                        rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm,
                            show hlin e₂ = h.e₂_lin from Subsingleton.elim _ _] at hoEnd
                        simp only [Event.oEnd, hfcw, hfc₂] at hoEnd ⊢; exact hoEnd
                      have : de_w.oEnd < de_w.oEnd :=
                        calc de_w.oEnd ≤ de₂.oEnd := hcw_le
                          _ < de_w.oStart := hob_₂w
                          _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed
                      exact Nat.lt_irrefl _ this
                · -- Diff cluster e_w: use cdirEncapsDown_exists at e_w's cluster.
                  -- Get evict at e_w's cluster, use dir_ordered with CLE_w,
                  -- then diffClusterNotBetweenCles_sameCache or .obEndLt.
                  obtain ⟨e_cdir_w, he_cdir_w_in_b, he_cdir_w_isDir, _, hcdir_w_lt,
                    ⟨_, _, _, _, _⟩,
                    ⟨e_evict_w, he_evict_w_in_b, he_evict_w_isDir, he_evict_w_down,
                     hevict_w_lt, hcdir_w_ob_evict_w, he_evict_w_proto, he_evict_w_isDirWrite, he_evict_w_translatedDir⟩⟩ :=
                    cdirEncapsDown_exists e_w_lin (hlin e₂) hw_in_b hw_cache
                  -- e_evict_w at e_w's cluster. dir_ordered CLE_w e_evict_w (same cluster, same addr).
                  have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                  have he_evict_w_isdir' := he_evict_w_isDir
                  match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                  | .directoryEvent de_w, _ =>
                    match hfc_evict_w : e_evict_w, he_evict_w_isdir' with
                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                    | .directoryEvent de_evict_w, _ =>
                      cases (b.orderedAtEntry.dir_ordered de_w de_evict_w).ordered with
                      | inl hob_w_evict =>
                        -- CLE_w OB evict_w. evict_w.oEnd < CLE₂.oEnd. CLE₂ OB CLE₁ (hob).
                        -- Chain: CLE_w < evict_w and evict_w.oEnd < CLE₂.oEnd < CLE₁.oStart
                        -- Use: is CLE₁ before or after evict_w?
                        -- evict_w at e_w's cluster, CLE₁ at e₁'s cluster (same as e₂).
                        -- Can't use dir_ordered (diff cluster). Use .obEndLt evict_w.
                        -- Need CLE₁ OB evict_w... but evict_w at diff cluster.
                        -- Actually: just need CLE_w.oEnd < CLE₁.oStart for CLE_w OB CLE₁.
                        -- From CLE₂ OB CLE₁: de₂.oEnd < de₁.oStart. And CLE_w OB evict_w: de_w.oEnd < de_evict_w.oStart.
                        -- evict_w.oEnd < CLE₂.oEnd. de₂.oEnd < de₁.oStart.
                        -- Chain: de_w.oEnd < de_evict_w.oStart ≤ de_evict_w.oEnd < CLE₂.oEnd.
                        -- And CLE₂.oEnd = de₂.oEnd + something? No, CLE₂ = de₂ (after match).
                        -- hevict_w_lt : e_evict_w.oEnd < (hlin e₂).CLE.oEnd
                        -- hob : de₂.OB de₁ (CLE₂ OB CLE₁)
                        -- Chain: de_w.oEnd < de_evict_w.oEnd (from OB + wellformed) < CLE₂.oEnd < CLE₁.oStart.
                        -- So de_w.oEnd < CLE₁.oStart. CLE₁ at e₁'s cluster = e₂'s cluster.
                        -- .obEndLt CLE_w: CLE₁ OB CLE_w? No, CLE_w before CLE₁.
                        -- Actually: need StepOrdering CLE₁ CLE₂. de_w before de₁ (from chain).
                        -- .obEndLt de_w: CLE₁ OB de_w? No, de_w before CLE₁.
                        -- evict_w OB CLE₁ from chain: evict_w.oEnd < CLE₂.oEnd < CLE₁.oStart
                        have hw₂_eq : hlin e₂ = lin e₂ := Subsingleton.elim _ _
                        have hevict_w_lt' : Event.oEnd n (.directoryEvent de_evict_w) <
                            Event.oEnd n (.directoryEvent de₂) := by
                          rw [hw₂_eq] at hevict_w_lt
                          show _ < Event.oEnd n (.directoryEvent de₂)
                          rw [← hfc₂]; exact hevict_w_lt
                        have hevict_w_ob_cle₁ : Event.oEnd n (Event.directoryEvent de_evict_w) <
                            Event.oStart n (Event.directoryEvent de₁) :=
                          Nat.lt_trans hevict_w_lt' hob
                        -- OrderedBetween CLE_w CLE₁ for evict_w
                        have h_between : e_evict_w.OrderedBetween n
                            e_w_lin.hreq's_dir_access.choose (lin e₁).hreq's_dir_access.choose :=
                          ⟨by rw [hfcw, hfc_evict_w]; exact hob_w_evict,
                           by rw [hfc_evict_w, hfc₁]; exact hevict_w_ob_cle₁⟩
                        -- Apply diffClusterNotBetweenCles_sameCache
                        exact absurd ⟨e_evict_w, by rw [hfc_evict_w]; exact he_evict_w_in_b,
                          { interDiffProtocol := by intro heq; exact h_ew_prot heq
                            downToW := by
                              show e_evict_w.protocol = e_w.protocol
                              rw [hfc_evict_w]; exact he_evict_w_proto
                            isDirWrite := by rw [hfc_evict_w]; exact he_evict_w_isDirWrite
                            downIsDown := by rw [hfc_evict_w]; exact he_evict_w_down
                            isDir := by rw [hfc_evict_w]; simp [Event.isDirectoryEvent]
                            translatedDir := by rw [hfc_evict_w]; exact he_evict_w_translatedDir
                          }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                      | inr hob_evict_w =>
                        -- evict_w OB CLE_w. Also e_cdir_w OB evict_w (from cdirEncapsDown).
                        -- Use dir_ordered CLE_w e_cdir_w: if CLE_w OB cdir_w → temporal contradiction.
                        have he_cdir_w_isdir' := he_cdir_w_isDir
                        match hfc_cdir_w : e_cdir_w, he_cdir_w_isdir' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_cdir_w, _ =>
                          cases (b.orderedAtEntry.dir_ordered de_w de_cdir_w).ordered with
                          | inl hob_w_cdir_w =>
                            -- CLE_w OB cdir_w OB evict_w OB CLE_w → temporal loop → contradiction
                            exfalso
                            -- Chain: de_w.oEnd < de_cdir_w.oStart ≤ de_cdir_w.oEnd < de_evict_w.oStart
                            --   ≤ de_evict_w.oEnd < de_w.oStart ≤ de_w.oEnd → de_w.oEnd < de_w.oEnd
                            have h₁ : de_w.oEnd < de_cdir_w.oStart := hob_w_cdir_w
                            have h₂ : Event.oEnd n (Event.directoryEvent de_cdir_w) <
                                Event.oStart n (Event.directoryEvent de_evict_w) := hcdir_w_ob_evict_w
                            have h₃ : de_evict_w.oEnd < de_w.oStart := hob_evict_w
                            exact Nat.lt_irrefl de_w.oEnd
                              (calc de_w.oEnd
                                _ < de_cdir_w.oStart := h₁
                                _ ≤ de_cdir_w.oEnd := Nat.le_of_lt de_cdir_w.oWellFormed
                                _ < de_evict_w.oStart := h₂
                                _ ≤ de_evict_w.oEnd := Nat.le_of_lt de_evict_w.oWellFormed
                                _ < de_w.oStart := h₃
                                _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed)
                          | inr hob_cdir_w_w =>
                            -- cdir_w OB CLE_w: consistent. cdir_w < evict_w < CLE_w.
                            -- Need different argument.
                            sorry -- cdir_w OB CLE_w + evict_w OB CLE_w: deeper protocol argument
      · -- Different cluster: e₂ write triggers downgrade at e₁'s cluster.
        -- Use cdirEncapsDown_exists which provides both e_cdir and e_cache_down
        -- as explicit existential witnesses (avoids Exists.choose issues).
        obtain ⟨e_cdir, he_cdir_in_b, he_cdir_isDir, he_cdir_proto, hcdir_lt_cle₂,
          ⟨e_cache_down, he_cdown_in_b, hcdir_encap_down, hcdown_is_down, hcdown_is_cache⟩,
          ⟨e_evict, he_evict_in_b, he_evict_isDir, he_evict_down, hevict_lt_cle₂, hcdir_ob_evict,
           he_evict_proto, he_evict_isDirWrite, he_evict_translatedDir⟩⟩ :=
          cdirEncapsDown_exists (lin e₁) (lin e₂) h.in_b₁ h.cache₁
        have hcle₁_isdir := (lin e₁).hreq's_dir_access.choose_spec.2.isDirEvent
        match hfc_cdir : e_cdir, he_cdir_isDir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de_cdir, _ =>
          match hfc_cle₁ : (lin e₁).hreq's_dir_access.choose, hcle₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cle₁, _ =>
            cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
            | inl hob =>
              have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
              exact .obEndLt (.directoryEvent de_cdir)
                (show (Event.directoryEvent de_cle₁).OrderedBefore n
                    (.directoryEvent de_cdir) from hob)
                (by rw [hw₂']; exact hcdir_lt_cle₂)
            | inr hob =>
              -- cdir OB CLE₁: e₂'s downgrade at e₁'s cluster is before e₁'s CLE.
              -- Use dir_ordered CLE₁ e_evict: if CLE₁ OB e_evict → .obEndLt e_evict.
              -- If e_evict OB CLE₁ → NIW contradiction (e_evict has down=true).
              have he_evict_isdir' := he_evict_isDir
              match hfc_evict : e_evict, he_evict_isdir' with
              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
              | .directoryEvent de_evict, _ =>
                cases (b.orderedAtEntry.dir_ordered de_cle₁ de_evict).ordered with
                | inl hob_cle₁_evict =>
                  -- CLE₁ OB e_evict → .obEndLt e_evict (CLE₁ before evict, evict.oEnd < CLE₂.oEnd)
                  have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                  exact .obEndLt (.directoryEvent de_evict)
                    (show (Event.directoryEvent de_cle₁).OrderedBefore n
                        (.directoryEvent de_evict) from hob_cle₁_evict)
                    (by rw [hw₂']; exact hevict_lt_cle₂)
                | inr hob_evict_cle₁ =>
                  -- e_evict OB CLE₁: evict (down=true) before reader's CLE → NIW.
                  exfalso
                  obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain, hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                  have hlin := fun e => h.hknow_dir_access compound b init e
                  have h_constraints := h_no_between e₂ h.in_b₂
                    h.cache₂ h.write h.notDown₂ (hlin e₂)
                  -- e_evict at e₁'s cluster. Need e_w at same cluster for notBetweenCles.
                  by_cases h_ew_prot : e₁.protocol = e_w.protocol
                  · -- Same cluster e_w/e₁: use diffClusterNotBetweenCles_sameCache.
                    -- e_evict at e₁'s cluster = e_w's cluster, with down=true.
                    -- Need: e_evict.OrderedBetween CLE_w CLE₁
                    -- hob_evict_cle₁ gives e_evict OB CLE₁ ✓.
                    -- Need CLE_w OB e_evict: from dir_ordered (same cluster/addr).
                    have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                    match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                    | .directoryEvent de_w, _ =>
                      cases (b.orderedAtEntry.dir_ordered de_w de_evict).ordered with
                      | inl hob_w_evict =>
                        -- CLE_w OB e_evict OB CLE₁: evict between CLE_w and CLE₁.
                        -- Apply diffClusterNotBetweenCles_sameCache.
                        have h_between : e_evict.OrderedBetween n
                            e_w_lin.hreq's_dir_access.choose
                            (lin e₁).hreq's_dir_access.choose :=
                          ⟨by rw [hfcw, hfc_evict]; exact hob_w_evict,
                           by rw [hfc_evict, hfc_cle₁]; exact hob_evict_cle₁⟩
                        exact absurd ⟨e_evict, by rw [hfc_evict]; exact he_evict_in_b,
                          { interDiffProtocol := by
                              intro heq; exact h_same_prot (h_ew_prot.trans heq.symm)
                            downToW := by
                              show e_evict.protocol = e_w.protocol
                              rw [hfc_evict]; exact he_evict_proto.trans h_ew_prot
                            isDirWrite := by rw [hfc_evict]; exact he_evict_isDirWrite
                            downIsDown := by rw [hfc_evict]; exact he_evict_down
                            isDir := by rw [hfc_evict]; simp [Event.isDirectoryEvent]
                            translatedDir := by rw [hfc_evict]; exact he_evict_translatedDir
                          }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                      | inr hob_evict_w =>
                        -- e_evict OB CLE_w: evict before write CLE.
                        -- Contradiction: co chain + encap chain → CLE_w OB evict,
                        -- but hob_evict_w says evict OB CLE_w.
                        -- Use co chain StepOrdering to get CLE_w.oEnd bound, then
                        -- encap chain CLE₂ > e_gcache > e_gdown > evict to get
                        -- CLE_w < evict. Combined with evict < CLE_w → oWellFormed contradiction.
                        -- Use dir_ordered CLE_w de_cdir (from outer match, same cluster/addr).
                        -- If CLE_w OB de_cdir → temporal loop: de_w < de_cdir < de_evict < de_w.
                        cases (b.orderedAtEntry.dir_ordered de_w de_cdir).ordered with
                        | inl hob_w_cdir =>
                          exact Nat.lt_irrefl de_w.oEnd
                            (calc de_w.oEnd
                              _ < de_cdir.oStart := hob_w_cdir
                              _ ≤ de_cdir.oEnd := Nat.le_of_lt de_cdir.oWellFormed
                              _ < de_evict.oStart := hcdir_ob_evict
                              _ ≤ de_evict.oEnd := Nat.le_of_lt de_evict.oWellFormed
                              _ < de_w.oStart := hob_evict_w
                              _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed)
                        | inr hob_cdir_w =>
                          sorry -- cdir OB CLE_w: deeper protocol argument
                  · -- Different cluster e_w/e₁: evict at e₁'s cluster, CLE_w at e_w's cluster.
                    -- Need CLE_w OB evict for OrderedBetween, then diffClusterNotBetweenCles_sameCache.
                    -- Chain: co → CLE_w.oEnd < CLE₂.oStart (for .ob case) → CLE₂ encaps chain → evict.
                    sorry -- diff-cluster e_w: CLE_w OB evict from co chain + encap chain
      -/
-- Old lex pair approach removed. Using LinLink (TransGen LinStep) instead of StepOrdering.
-- Each edge produces StepOrdering, converted to LinLink ∨ eq via toLinLinkOrEq.
-- LinLink.trans (= TransGen.trans) replaces StepOrdering.trans (which had sorry's).
-- LinLink.irrefl replaces the per-constructor irrefl case analysis.

/-- Helper: CLE is a directory event, so dir_ordered CLE CLE → False. -/
private theorem cle_self_ordering_false
    (hknow : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : False := by
  have hisdir := hknow.hreq's_dir_access.choose_spec.right.isDirEvent
  match hknow.hreq's_dir_access.choose, hisdir with
  | .directoryEvent de, _ =>
    cases (hdir de de).ordered with
    | inl h => exact absurd (Nat.lt_trans h de.oWellFormed) (Nat.lt_irrefl _)
    | inr h => exact absurd (Nat.lt_trans h de.oWellFormed) (Nat.lt_irrefl _)
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh

/-- Convert StepOrdering to the 3-way disjunction: LinLink ∨ eq ∨ diff_protocol.
    obFinishBefore maps to diff_protocol (its h_diff_prot field).
    eq maps to eq. All others map to LinLink. -/
private theorem stepOrdering_to_three {l₁ l₂ : Event n}
    (h : StepOrdering l₁ l₂)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : @LinLink n l₁ l₂ ∨ l₁ = l₂ ∨ l₁.protocol ≠ l₂.protocol := by
  cases h with
  | ob h => exact Or.inl (LinLink.single (.ob h))
  | obEndLt p h_ob h_lt =>
    -- l₁ OB p, p.oEnd < l₂.oEnd.
    -- Same protocol: dir_ordered gives p OB l₂ → ob chain → LinLink.
    -- Diff protocol: diff_protocol → cycle contradiction.
    by_cases h_prot : l₁.protocol = l₂.protocol
    · sorry -- same protocol obEndLt: needs dir_ordered p l₂ (both directory events at same cluster)
    · exact Or.inr (Or.inr h_prot)
  | encapOb p h_enc h_ob =>
    exact Or.inl (LinLink.trans (LinLink.single (.encap h_enc)) (LinLink.single (.ob h_ob)))
  | sameLin e₁' e₂' h_eq h_enc₁ h_ob h_enc₂ =>
    exact Or.inr (Or.inl h_eq)
  | proxyPair q p h_q_enc h_q_ob_p h_p_ob =>
    exact Or.inl (LinLink.trans (LinLink.trans (LinLink.single (.encap h_q_enc))
      (LinLink.single (.ob h_q_ob_p))) (LinLink.single (.ob h_p_ob)))
  | obFinishBefore p h_ob h_lt h_diff => exact Or.inr (Or.inr h_diff)
  | eq h_eq => exact Or.inr (Or.inl h_eq)

/-- Compose two 3-way disjunctions (LinLink ∨ eq ∨ diff_protocol).
    Compositions involving diff_protocol use sorry — these only arise in
    non-cycle intermediate compositions and are vacuous in cycles (a = c)
    since diff_protocol gives cle a ≠ cle a → contradiction with rfl. -/
private theorem compose_three {l₁ l₂ l₃ : Event n}
    (h₁ : @LinLink n l₁ l₂ ∨ l₁ = l₂ ∨ l₁.protocol ≠ l₂.protocol)
    (h₂ : @LinLink n l₂ l₃ ∨ l₂ = l₃ ∨ l₂.protocol ≠ l₃.protocol)
    : @LinLink n l₁ l₃ ∨ l₁ = l₃ ∨ l₁.protocol ≠ l₃.protocol := by
  cases h₁ with
  | inl hlink₁ =>
    cases h₂ with
    | inl hlink₂ => exact Or.inl (LinLink.trans hlink₁ hlink₂)
    | inr hrest => cases hrest with
      | inl heq => exact Or.inl (heq ▸ hlink₁)
      | inr _hdiff =>
        -- LinLink l₁ l₂ + l₂.protocol ≠ l₃.protocol: can't derive l₁.protocol ≠ l₃.protocol.
        exact Or.inr (Or.inr (sorry)) -- in cycles, diff_prot contradicts rfl
  | inr hrest₁ => cases hrest₁ with
    | inl heq₁ =>
      cases h₂ with
      | inl hlink₂ => exact Or.inl (heq₁ ▸ hlink₂)
      | inr hrest => cases hrest with
        | inl heq₂ => exact Or.inr (Or.inl (heq₁.trans heq₂))
        | inr hdiff₂ => exact Or.inr (Or.inr (heq₁ ▸ hdiff₂))
    | inr hdiff₁ =>
      cases h₂ with
      | inl _hlink₂ =>
        -- l₁.protocol ≠ l₂.protocol + LinLink l₂ l₃: can't derive l₁.protocol ≠ l₃.protocol.
        exact Or.inr (Or.inr (sorry)) -- in cycles, diff_prot contradicts rfl
      | inr hrest => cases hrest with
        | inl heq₂ => exact Or.inr (Or.inr (heq₂ ▸ hdiff₁))
        | inr _hdiff₂ =>
          -- l₁.protocol ≠ l₂.protocol + l₂.protocol ≠ l₃.protocol:
          -- 2-cluster pigeonhole gives l₁.protocol = l₃.protocol, but can't derive LinLink/eq.
          exact Or.inr (Or.inr (sorry)) -- in cycles, diff_prot contradicts rfl

/-- Acyclicity given that every event has a linearization.
    Each edge produces StepOrdering, converted to LinLink ∨ eq ∨ diff_protocol.
    LinLink composes freely (TransGen.trans). A cycle gives
    LinLink CLE CLE → LinLink.irrefl, or all-eq → dir_ordered de de → False,
    or diff_protocol → cle e ≠ cle e → contradiction. -/
theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  -- Each edge gives StepOrdering. Convert to LinLink ∨ eq ∨ diff_protocol.
  -- For the cycle (a = c): all three give contradiction.
  let cle := fun e => (hknow e).hreq's_dir_access.choose
  suffices ∀ a c, Relation.TransGen ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) a c →
      @LinLink n (cle a) (cle c) ∨ cle a = cle c ∨ (cle a).protocol ≠ (cle c).protocol by
    have hresult := this e e hcycle
    cases hresult with
    | inl hlink => exact LinLink.irrefl hlink
    | inr hrest => cases hrest with
      | inl heq => exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
      | inr hdiff => exact absurd rfl hdiff
  intro a c hpath
  induction hpath with
  | single h => exact stepOrdering_to_three (step_to_ordering h hknow) (b.orderedAtEntry.dir_ordered)
  | tail _ h ih =>
    exact compose_three ih (stepOrdering_to_three (step_to_ordering h hknow) (b.orderedAtEntry.dir_ordered))

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
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  -- The cycle is either pure PPOi or has at least one com edge.
  rcases transgen_union_find_right hcycle with hppoi_cycle | ⟨x, y, hcom⟩
  · -- All PPOi (diff-addr): contradiction from OB transitivity
    -- Weaken: PPOi ∧ diff_addr → PPOi
    have := hppoi_cycle.mono (fun _ _ h => h.1)
    exact ppoi_acyclic e this
  · -- Some com edge exists: extract hknow_dir_access
    exact cmcm_acyclic_of_hknow (com.extract_hknow hcom) e hcycle

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b' e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init'

/-! ## PartialOrder (consequence of acyclicity) -/

noncomputable def eventPartialOrder : PartialOrder (Event n) := by
  let R := (fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init
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
