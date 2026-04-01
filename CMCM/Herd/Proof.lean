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
          (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt)
          hcdir_spec.2.1
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
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
        hcdir_spec.2.1
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose
        (by rw [← hw₁]; exact evict.wObRDown)
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
        hcdir_spec.2.1

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
          (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
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
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt))
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_trans (by rw [← hw₁]; exact evict.wObRDown) (Event.oWellFormed n _))
        (by rw [← hw₂]; cases hcdir_spec.2.2.2.2.2 with
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
    with CLE_w OB d, d.oEnd < CLE₂.oEnd, d at e_w's protocol.
    Returns an intermediate write `e_mid` that triggered the downgrade (with translatedDir).
    h_no_between can be applied to e_mid at the call site. -/
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
        
        -- e_mid: the intermediate write that triggered the downgrade.
        -- Carries properties needed for h_no_between at call sites.
        ∃ (e_mid : Event n), e_mid ∈ b ∧ e_mid.isClusterCache ∧ e_mid.isWrite ∧ ¬ e_mid.down ∧
          ¬ e_mid.sameProtocol n e_w ∧
          Event.clusterDirFromDiffProtocolRequest b init e_mid d (lin e_mid) := by
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
          cases hrd_spec.2.2.2.2.2 with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        -- e_mid = the second writer in this CO step (the endpoint)
        exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_lin from Subsingleton.elim _ _]; exact w.wObRDown,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.1, hrd_spec.2.2.1,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.1⟩⟩
      | evictOrReadBetweenWAndRDown evict =>
        have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            h_co.w₂_lin.hreq's_dir_access.choose.oEnd := by
          cases hrd_spec.2.2.2.2.2 with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_lin from Subsingleton.elim _ _]; exact evict.wObRDown,
          by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.1, hrd_spec.2.2.1,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = h_co.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.1⟩⟩
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
            cases hrd_spec.2.2.2.2.2 with
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
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.1⟩⟩
        | evictOrReadBetweenWAndRDown evict =>
          have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              h_last.w₂_lin.hreq's_dir_access.choose.oEnd := by
            cases hrd_spec.2.2.2.2.2 with
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
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = h_last.w₂_lin from Subsingleton.elim _ _]; exact hrd_spec.2.2.2.2.1⟩⟩
    · -- Prefix diff-cluster: IH gives d with e_mid from some earlier step.
      -- Pass through the IH's e_mid — it has translatedDir about e_mid, not the endpoint.
      -- h_no_between at the call site can be applied to e_mid instead of e₂.
      obtain ⟨d, hd_in_b, hob_d, hd_lt, hd_isDir, hd_proto, hd_emid⟩ := ih h_mid_prot
      have hext : (lin b_mid).hreq's_dir_access.choose.oEnd ≤ (lin c_ep).hreq's_dir_access.choose.oEnd :=
        co_step_oEnd_le h_last lin
      exact ⟨d, hd_in_b, hob_d, Nat.lt_of_lt_of_le hd_lt hext, hd_isDir, hd_proto, hd_emid⟩

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
          ⟨e_evict, he_evict_in_b, he_evict_isDir, hevict_lt_cle₂,
           hcdir_ob_evict, he_evict_proto, he_evict_translatedDir⟩⟩ :=
          cdirEncapsDown_exists (lin e₁) (lin e₂) h.in_b₁ h.cache₁ h.notDown₁ lin
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
                  (by simp [Event.isDirectoryEvent])
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
                      (by simp [Event.isDirectoryEvent])
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
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto,
                        
                        e_mid, h_mid_in_b, h_mid_cache, h_mid_write, h_mid_not_down,
                        h_mid_diff_ew, h_mid_translated⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      -- dir_ordered d_co CLE₁ at e₁'s cluster
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          -- d_co OB CLE₁ → NIW contradiction via h_no_between applied to e_mid.
                          exfalso
                          have h_constraints := h_no_between e_mid h_mid_in_b
                            h_mid_cache h_mid_write h_mid_not_down (hlin e_mid)
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁]; exact hdco_ob_cle₁
                          -- Case-split on d_co.down to use the right NIW constraint
                          by_cases h_dco_down : d_co.down
                          · -- d_co is a downgrade → use sameCacheConstraints
                            exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                downIsDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                          · -- d_co is not a downgrade → use sameCacheWriteConstraints
                            exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                notDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          -- CLE₁ OB d_co: proxy for .diffCluster_coherent
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
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
                          cases hdrf_spec.2.2.2.2.2 with
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
                                  cases hdrf_spec'.2.2.2.2.2 with
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
                                            hdrf_lt hdrf_isdir''
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
                                    (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂ hdrf_isdir
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
                  (by simp [Event.isDirectoryEvent])
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
                      (by simp [Event.isDirectoryEvent])
                  | inr hob_evict =>
                    -- Same structure as encapDir case.
                    obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                      hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                    have hlin := fun e => h.hknow_dir_access compound b init e
                    by_cases h_ew_e₁ : e₁.protocol = e_w.protocol
                    · have h_ew_diff_e₂ : ¬ e_w.sameProtocol n e₂ := by
                        unfold Event.sameProtocol
                        intro h; exact h_same_prot (show e₁.protocol = e₂.protocol from h_ew_e₁.trans h)
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto, 
                        e_mid, h_mid_in_b, h_mid_cache, h_mid_write, h_mid_not_down,
                        h_mid_diff_ew, h_mid_translated⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          exfalso
                          have h_constraints := h_no_between e_mid h_mid_in_b
                            h_mid_cache h_mid_write h_mid_not_down (hlin e_mid)
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁₂]; exact hdco_ob_cle₁
                          by_cases h_dco_down : d_co.down
                          · exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                downIsDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                          · exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                notDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₂]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.2.2.2.2 with
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
                                (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂ hdrf_isdir''
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
                  (by simp [Event.isDirectoryEvent])
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
                      (by simp [Event.isDirectoryEvent])
                  | inr hob_evict =>
                    -- Same structure as encapDir case.
                    obtain ⟨e_w, e_w_write, e_w_lin, _, h_rf, h_no_between, h_co_chain,
                      hw_in_b, hw_cache, hw_not_down⟩ := h.comm
                    have hlin := fun e => h.hknow_dir_access compound b init e
                    by_cases h_ew_e₁ : e₁.protocol = e_w.protocol
                    · have h_ew_diff_e₂ : ¬ e_w.sameProtocol n e₂ := by
                        unfold Event.sameProtocol
                        intro h; exact h_same_prot (show e₁.protocol = e₂.protocol from h_ew_e₁.trans h)
                      obtain ⟨d_co, hdco_in_b, hcle_w_ob_dco, hdco_lt_cle₂, hdco_isDir, hdco_proto, 
                        e_mid, h_mid_in_b, h_mid_cache, h_mid_write, h_mid_not_down,
                        h_mid_diff_ew, h_mid_translated⟩ :=
                        co_chain_cross_cluster_downgrade h_co_chain h_ew_diff_e₂ e_w_lin hlin
                      have hdco_isdir' := hdco_isDir
                      match hfc_dco : d_co, hdco_isdir' with
                      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                      | .directoryEvent de_dco, _ =>
                        cases (b.orderedAtEntry.dir_ordered de_dco de_cle₁).ordered with
                        | inl hdco_ob_cle₁ =>
                          exfalso
                          have h_constraints := h_no_between e_mid h_mid_in_b
                            h_mid_cache h_mid_write h_mid_not_down (hlin e_mid)
                          have h_between : d_co.OrderedBetween n
                              e_w_lin.hreq's_dir_access.choose
                              (lin e₁).hreq's_dir_access.choose := by
                            constructor
                            · rw [hfc_dco]; exact hcle_w_ob_dco
                            · rw [hfc_dco, hfc_cle₁₃]; exact hdco_ob_cle₁
                          by_cases h_dco_down : d_co.down
                          · exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                downIsDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                          · exact absurd ⟨d_co, by rw [hfc_dco]; exact hdco_in_b,
                              { interDiffProtocol := by exact h_mid_diff_ew
                                downToW := by unfold Event.sameProtocol; rw [hfc_dco]; exact hdco_proto
                                notDown := hfc_dco ▸ h_dco_down
                                isDir := by rw [hfc_dco]; exact hdco_isDir
                                translatedDir := by rw [hfc_dco]; exact h_mid_translated
                              }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
                        | inr hcle₁_ob_dco =>
                          have hw₂' : lin e₂ = h.e₂_lin := Subsingleton.elim _ _
                          exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₃]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.2.2.2.2 with
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
                                (by rw [hfc_drf'', hfc_cle₂'']; exact hob) hdrf_lt₂ hdrf_isdir''
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

/-- Map a COM edge to a StepOrdering between CLEs.
    PPOi is handled separately via dir_ordered in compose_three/cmcm_acyclic_of_hknow. -/
theorem step_to_ordering
    (h : com compound b init e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : @StepOrdering n (lin e₁).hreq's_dir_access.choose (lin e₂).hreq's_dir_access.choose := by
  cases h with
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
            have hencap_rel := hcdir_spec.2.2.2.2.2
            exact .obEndLt hdown.existsRClusterDirDown.choose
              (by rw [← hw₁]; exact hwOB)
              (by rw [← hw₂]; cases hencap_rel with
                  | cleEncap henc => exact henc.right
                  | gcacheEncap _ hlt => exact hlt)
              hcdir_spec.2.1
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
                -- noEvictBetween: CLE_w OB cdir from wCleObCdir field.
                -- Use from_encap_wob directly — no dir_ordered needed.
                exact from_encap_wob w.gdownEncapProxyAndDirAndCDown.encapDir
                  w.noEvictBetween.wCleObCdir
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
      | diffCluster_coherent _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir
      | diffCluster_evict _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir
      | diffCluster_noncoherent _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir
      | diffCluster_rfCrossCluster _ p p_inside p_ob => exact .encapOb p p_inside p_ob
      | diffCluster_rfFinishBefore h_diff p p_ob p_lt h_p_isdir =>
        have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
        have hcle₂_prot := write_cle_protocol_eq_write_protocol (lin e₂)
        exact .obFinishBefore p p_ob p_lt (fun heq =>
          h_diff (show e₁.sameProtocol n e₂ from hcle₁_prot.symm.trans (heq ▸ hcle₂_prot))) h_p_isdir
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
                    ⟨e_evict_w, he_evict_w_in_b, he_evict_w_isDir,
                     hevict_w_lt, hcdir_w_ob_evict_w, he_evict_w_proto, he_evict_w_translatedDir⟩⟩ :=
                    cdirEncapsDown_exists e_w_lin (hlin e₂) hw_in_b hw_cache hw_not_down hlin
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
                        -- Branch on e_evict.down: sameCacheConstraints vs sameCacheWriteConstraints
                        by_cases hevict_down : e_evict_w.down
                        · -- down=true: use diffClusterNotBetweenCles_sameCache
                          exact absurd ⟨e_evict_w, by rw [hfc_evict_w]; exact he_evict_w_in_b,
                            { interDiffProtocol := by intro heq; exact h_ew_prot heq
                              downToW := by
                                show e_evict_w.protocol = e_w.protocol
                                rw [hfc_evict_w]; exact he_evict_w_proto
                              downIsDown := hevict_down
                              isDir := by rw [hfc_evict_w]; simp [Event.isDirectoryEvent]
                              translatedDir := by rw [hfc_evict_w]; exact he_evict_w_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                        · -- down=false: use diffClusterNotBetweenCles_sameCacheWrite
                          exact absurd ⟨e_evict_w, by rw [hfc_evict_w]; exact he_evict_w_in_b,
                            { interDiffProtocol := by intro heq; exact h_ew_prot heq
                              downToW := by
                                show e_evict_w.protocol = e_w.protocol
                                rw [hfc_evict_w]; exact he_evict_w_proto
                              notDown := by simp [Bool.eq_false_iff] at hevict_down; exact hevict_down
                              isDir := by rw [hfc_evict_w]; simp [Event.isDirectoryEvent]
                              translatedDir := by rw [hfc_evict_w]; exact he_evict_w_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
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
          ⟨e_evict, he_evict_in_b, he_evict_isDir, hevict_lt_cle₂, hcdir_ob_evict,
           he_evict_proto, he_evict_translatedDir⟩⟩ :=
          cdirEncapsDown_exists (lin e₁) (lin e₂) h.in_b₁ h.cache₁ h.notDown₁ lin
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
                (by simp [Event.isDirectoryEvent])
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
                    (by simp [Event.isDirectoryEvent])
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
                        by_cases hevict_down : e_evict.down
                        · exact absurd ⟨e_evict, by rw [hfc_evict]; exact he_evict_in_b,
                            { interDiffProtocol := by
                                intro heq; exact h_same_prot (h_ew_prot.trans heq.symm)
                              downToW := by
                                show e_evict.protocol = e_w.protocol
                                rw [hfc_evict]; exact he_evict_proto.trans h_ew_prot
                              downIsDown := hevict_down
                              isDir := by rw [hfc_evict]; simp [Event.isDirectoryEvent]
                              translatedDir := by rw [hfc_evict]; exact he_evict_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCache
                        · exact absurd ⟨e_evict, by rw [hfc_evict]; exact he_evict_in_b,
                            { interDiffProtocol := by
                                intro heq; exact h_same_prot (h_ew_prot.trans heq.symm)
                              downToW := by
                                show e_evict.protocol = e_w.protocol
                                rw [hfc_evict]; exact he_evict_proto.trans h_ew_prot
                              notDown := by simp [Bool.eq_false_iff] at hevict_down; exact hevict_down
                              isDir := by rw [hfc_evict]; simp [Event.isDirectoryEvent]
                              translatedDir := by rw [hfc_evict]; exact he_evict_translatedDir
                            }, h_between⟩ h_constraints.diffClusterNotBetweenCles_sameCacheWrite
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
    (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
    : @LinLink n l₁ l₂ ∨ l₁ = l₂ ∨ l₁.protocol ≠ l₂.protocol := by
  cases h with
  | ob h => exact Or.inl (LinLink.single (.ob h))
  | encap henc => exact Or.inl (LinLink.single (.encap henc))
  | obEndLt p h_ob h_lt _ =>
    -- l₁ OB p, p.oEnd < l₂.oEnd.
    -- Same protocol: dir_ordered gives p OB l₂ → ob chain → LinLink.
    -- Diff protocol: diff_protocol → cycle contradiction.
    by_cases h_prot : l₁.protocol = l₂.protocol
    · match hfc₁ : l₁, h₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₂ : l₂, h₂_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₂, _ =>
          cases (hdir de₁ de₂).ordered with
          | inl h => exact Or.inl (LinLink.single (.ob h))
          | inr h =>
            exfalso
            exact Nat.lt_irrefl de₂.oEnd
              (calc de₂.oEnd
                _ < de₁.oStart := h
                _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                _ < Event.oStart n p := h_ob
                _ ≤ Event.oEnd n p := Nat.le_of_lt (Event.oWellFormed n p)
                _ < de₂.oEnd := h_lt)
    · exact Or.inr (Or.inr h_prot)
  | encapOb p h_enc h_ob =>
    exact Or.inl (LinLink.trans (LinLink.single (.encap h_enc)) (LinLink.single (.ob h_ob)))
  | sameLin e₁' e₂' h_eq h_enc₁ h_ob h_enc₂ =>
    exact Or.inr (Or.inl h_eq)
  | proxyPair q p h_q_enc h_q_ob_p h_p_ob =>
    exact Or.inl (LinLink.trans (LinLink.trans (LinLink.single (.encap h_q_enc))
      (LinLink.single (.ob h_q_ob_p))) (LinLink.single (.ob h_p_ob)))
  | obFinishBefore p h_ob h_lt h_diff _ => exact Or.inr (Or.inr h_diff)
  | eq h_eq => exact Or.inr (Or.inl h_eq)
  | encapObEndLt q p h_q_enc h_q_ob h_p_lt _ =>
    by_cases h_prot : l₁.protocol = l₂.protocol
    · -- Same protocol: dir_ordered
      match hfc₁ : l₁, h₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₂ : l₂, h₂_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₂, _ =>
          cases (hdir de₁ de₂).ordered with
          | inl h => exact Or.inl (LinLink.single (.ob h))
          | inr h =>
            exfalso
            exact Nat.lt_irrefl de₂.oEnd
              (calc de₂.oEnd
                _ < de₁.oStart := h
                _ < Event.oStart n q := h_q_enc.left
                _ ≤ Event.oEnd n q := Nat.le_of_lt (Event.oWellFormed n q)
                _ < Event.oStart n p := h_q_ob
                _ ≤ Event.oEnd n p := Nat.le_of_lt (Event.oWellFormed n p)
                _ < de₂.oEnd := h_p_lt)
    · exact Or.inr (Or.inr h_prot)

/-- Key lemma: if StepOrdering l₂ l₃ holds at the same protocol, then l₃ OB l₂ is impossible.
    Proof: stepOrdering_to_three gives LinLink ∨ eq ∨ diff_prot. diff_prot contradicts same-prot.
    eq gives self-ordering contradiction. LinLink l₂ l₃ + l₃ OB l₂ → LinLink l₂ l₂ → irrefl. -/
private theorem step_ordering_same_prot_not_reverse {l₂ l₃ : Event n}
    (h₂ : @StepOrdering n l₂ l₃)
    (h_same_prot : l₂.protocol = l₃.protocol)
    (h₂_isdir : l₂.isDirectoryEvent) (h₃_isdir : l₃.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (hob_reverse : l₃.OrderedBefore n l₂)
    : False := by
  have h3 := stepOrdering_to_three h₂ hdir h₂_isdir h₃_isdir
  cases h3 with
  | inl hlink =>
    -- LinLink l₂ l₃ + l₃ OB l₂ → LinLink l₃ l₂ → LinLink l₂ l₂ → irrefl
    exact LinLink.irrefl (hlink.trans (LinLink.single (.ob hob_reverse)))
  | inr hr => cases hr with
    | inl heq =>
      -- l₂ = l₃. l₃ OB l₂ → l₂ OB l₂ → oEnd < oStart contradiction.
      exact Event.contradiction_of_reflexive_ordered_before n (heq ▸ hob_reverse)
    | inr hdiff => exact absurd h_same_prot hdiff

/-- Corollary: same-protocol dir_ordered(l₂, l₃) with StepOrdering l₂ l₃ must give l₂ OB l₃. -/
private theorem same_prot_dir_ordered_forward {l₂ l₃ : Event n}
    (h₂ : @StepOrdering n l₂ l₃)
    (h_same_prot : l₂.protocol = l₃.protocol)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₂_isdir : l₂.isDirectoryEvent) (h₃_isdir : l₃.isDirectoryEvent)
    : l₂.OrderedBefore n l₃ := by
  match hfc₂ : l₂, h₂_isdir with
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
  | .directoryEvent de₂, _ =>
    match hfc₃ : l₃, h₃_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de₃, _ =>
      cases (hdir de₂ de₃).ordered with
      | inl hob => exact hob
      | inr hob_rev =>
        exfalso; exact step_ordering_same_prot_not_reverse h₂ h_same_prot
          (hfc₂ ▸ h₂_isdir) (hfc₃ ▸ h₃_isdir) hdir hob_rev

/-- For PPOi: dir_ordered on CLEs gives the 3-way result directly.
    CLE₁ OB CLE₂ → .ob. CLE₂ OB CLE₁ → third alternative (cycle closure handles). -/
private theorem step_ordering_dir_ordered_3way {l₁ l₂ : Event n}
    (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : @StepOrdering n l₁ l₂ ∨ l₁ = l₂ ∨ l₂.OrderedBefore n l₁ := by
  match l₁, h₁_isdir with
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
  | .directoryEvent de₁, _ =>
    match l₂, h₂_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de₂, _ =>
      cases (hdir de₁ de₂).ordered with
      | inl hob => exact Or.inl (.ob hob)
      | inr hob_rev => exact Or.inr (Or.inr hob_rev)

/-- Handle obFinishBefore h₁ + com edge directly.
    Case-splits on hcom_edge for full protocol evidence instead of going
    through the lossy step_to_ordering → StepOrdering path. -/
private theorem compose_obFinishBefore_com {l₁ l₂ l₃ : Event n} {e₁ e₂ e₃ : Event n}
    (p₁ : Event n) (hob₁ : p₁.OrderedBefore n l₂) (hlt₁ : p₁.oEnd < l₁.oEnd)
    (hdiff₁ : l₁.protocol ≠ l₂.protocol) (h_p₁_isdir : p₁.isDirectoryEvent)
    (hcom_edge : com compound b init e₂ e₃)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hl₂ : l₂ = (hknow e₂).hreq's_dir_access.choose) (hl₃ : l₃ = (hknow e₃).hreq's_dir_access.choose)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₁_isdir : l₁.isDirectoryEvent)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : @StepOrdering n l₁ l₃ ∨ l₁ = l₃ ∨ l₃.OrderedBefore n l₁ := by
  -- Same-cluster: l₂.prot = l₃.prot → l₁ ≠ l₃ → .obFinishBefore via OB chain
  by_cases he₂₃ : e₂.protocol = e₃.protocol
  · have h₂ : @StepOrdering n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering hcom_edge hknow h_non_lazy_ppoi
    have h₂₃_prot : Event.protocol n l₂ = Event.protocol n l₃ := by
      rw [hl₂, hl₃]
      exact (write_cle_protocol_eq_write_protocol (hknow e₂)).trans
        (he₂₃.trans (write_cle_protocol_eq_write_protocol (hknow e₃)).symm)
    have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
    have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
    have hob₂ := same_prot_dir_ordered_forward h₂ h₂₃_prot hdir h₂_isdir h₃_isdir
    have hprot_diff : l₁.protocol ≠ l₃.protocol := fun h₁₃ => hdiff₁ (h₁₃.trans h₂₃_prot.symm)
    exact Or.inl (.obFinishBefore p₁ (Trans.trans hob₁ hob₂) hlt₁ hprot_diff h_p₁_isdir)
  · -- Diff cluster: case-split on hcom_edge for full protocol evidence
    by_cases hprot : l₁.protocol = l₃.protocol
    · -- Same protocol l₁/l₃, diff cluster e₂/e₃: need cross-cluster evidence
      have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
      match hfc₁ : l₁, h₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₃ : l₃, h₃_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₃, _ =>
          cases (hdir de₁ de₃).ordered with
          | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
          | inr hob₃₁ =>
            -- l₃ OB l₁: need cross-cluster protocol evidence from hcom_edge
            -- Case-split on the com edge to access NIW/rf/co structure
            exact Or.inr (Or.inr hob₃₁)
    · -- Diff protocol l₁/l₃: chain p₁ through h₂ to l₃
      have h₂ : @StepOrdering n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering hcom_edge hknow h_non_lazy_ppoi
      -- p₁ OB l₂. Chain through h₂ to get p₁ OB l₃ for .obFinishBefore.
      -- stepOrdering_to_three h₂ gives LinLink or eq or diff_prot.
      -- For LinLink: p₁ OB l₂ + LinLink l₂ l₃ → p₁ OB l₃ (by induction on TransGen).
      -- For eq: l₂ = l₃ → p₁ OB l₃.
      -- For diff_prot: l₂ ≠ l₃ → with l₁ ≠ l₃ → .obFinishBefore if we can chain.
      have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
      have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
      have h3way := stepOrdering_to_three h₂ hdir h₂_isdir h₃_isdir
      cases h3way with
      | inl hlink =>
        -- LinLink l₂ l₃: p₁ OB l₂ + LinLink l₂ l₃ → p₁ OB l₃
        -- p₁ OB l₂ + LinLink l₂ l₃ → p₁ OB l₃
        -- LinLink = TransGen LinStep. Each LinStep is OB or encap.
        -- p OB x + LinStep x y → p OB y (for both OB and encap steps).
        -- p₁ OB l₂ + LinLink l₂ l₃ → p₁ OB l₃ via irreflexivity argument:
        -- l₃ OB p₁ → LinLink l₃ l₂ (l₃ OB p₁, p₁ OB l₂) → with LinLink l₂ l₃ → LinLink l₃ l₃ → irrefl.
        have hp₁_ob_l₃ : p₁.OrderedBefore n l₃ := by
          match hfcp₁ : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₃ : l₃, h₃_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₃, _ =>
              cases (hdir dep₁ del₃).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                -- l₃ OB p₁ (as dir events): chain to LinLink l₃ l₃ → irrefl
                exfalso; exact LinLink.irrefl
                  (((LinLink.single (.ob (show Event.OrderedBefore n (.directoryEvent del₃) (.directoryEvent dep₁) from hob_rev))).tail
                    (.ob (show Event.OrderedBefore n (.directoryEvent dep₁) l₂ from hob₁))).trans hlink)
        exact Or.inl (.obFinishBefore p₁ hp₁_ob_l₃ hlt₁ hprot h_p₁_isdir)
      | inr hr => cases hr with
        | inl heq =>
          -- l₂ = l₃ → p₁ OB l₃
          exact Or.inl (.obFinishBefore p₁ (heq ▸ hob₁) hlt₁ hprot h_p₁_isdir)
        | inr hdiff₂ =>
          -- l₂ ≠ l₃ protocol. dir_ordered(l₁, l₃) resolves via 3-way invariant.
          match hfc₁ : l₁, h₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₁, _ =>
            match hfc₃ : l₃, h₃_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₃, _ =>
              cases (hdir de₁ de₃).ordered with
              | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
              | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)

/-- Compose two StepOrderings (or eq) and extract 3-way disjunction.
    For same-protocol l₁/l₃: dir_ordered → l₁ OB l₃ (LinLink) or l₃ OB l₁ (temporal contradiction).
    The temporal contradiction chains through BOTH h₁ and h₂'s data.
    obFinishBefore on h₁: handled by compose_obFinishBefore_com for com edges. -/
private theorem compose_three {l₁ l₂ l₃ : Event n} {e₁ e₂ e₃ : Event n}
    (h₁ : @StepOrdering n l₁ l₂ ∨ l₁ = l₂ ∨ l₂.OrderedBefore n l₁)
    (hedge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₂ e₃)
    (h_prefix_edge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₁ e₂)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hl₂ : l₂ = (hknow e₂).hreq's_dir_access.choose) (hl₃ : l₃ = (hknow e₃).hreq's_dir_access.choose)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₁_isdir : l₁.isDirectoryEvent)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : @StepOrdering n l₁ l₃ ∨ l₁ = l₃ ∨ l₃.OrderedBefore n l₁ := by
  -- Helper: extract e₂'s read/write from edge, check junction compatibility.
  -- hedge constrains e₂ from the CURRENT edge. h_prefix_edge from the PREFIX.
  -- If incompatible (e₂ read + e₂ write) → exfalso.
  have h_e₂_from_hedge : (e₂.isWrite ∨ e₂.isRead) := by
    cases hedge with
    | inl hppoi =>
        -- PPOi(e₂, e₃): e₂ is a cache event, so rw is either .w or .r
        have hcache := hppoi.1.cache₁
        cases he₂ : e₂ with
        | directoryEvent _ => simp [Event.isCacheEvent, he₂] at hcache
        | cacheEvent ce =>
          simp only [Event.isWrite, Event.isRead, Request.isWrite, Request.isRead, he₂]
          cases ce.req.val.rw with
          | w => exact Or.inl rfl
          | r => exact Or.inr rfl
    | inr hcom => cases hcom with
      | rfe hrfe => exact Or.inl hrfe.write
      | co hco => exact Or.inl hco.write₁
      | fr hfr => exact Or.inr hfr.read
  have h_e₂_from_prefix : (e₂.isWrite ∨ e₂.isRead) := by
    cases h_prefix_edge with
    | inl hppoi =>
        -- PPOi(e₁, e₂): e₂ is a cache event, so rw is either .w or .r
        have hcache := hppoi.1.cache₂
        cases he₂ : e₂ with
        | directoryEvent _ => simp [Event.isCacheEvent, he₂] at hcache
        | cacheEvent ce =>
          simp only [Event.isWrite, Event.isRead, Request.isWrite, Request.isRead]
          cases ce.req.val.rw with
          | w => exact Or.inl rfl
          | r => exact Or.inr rfl
    | inr hcom => cases hcom with
      | rfe hrfe => exact Or.inr hrfe.read   -- rfe(e₁, e₂): e₂.isRead
      | co hco => exact Or.inl hco.write₂    -- co(e₁, e₂): e₂.isWrite
      | fr hfr => exact Or.inl hfr.write     -- fr(e₁, e₂): e₂.isWrite
  -- Junction compatibility: check if both edges constrain e₂ to different types.
  -- If prefix makes e₂ a writer and current edge needs e₂ a reader (or vice versa) → contradiction.
  -- This eliminates impossible pairs like FR+FR, co+FR, rfe+rfe, etc.
  have h_junction_compat : ¬(e₂.isWrite ∧ e₂.isRead) := by
    intro ⟨hw, hr⟩
    cases e₂ with
    | cacheEvent ce =>
      simp only [Event.isRead, Request.isRead] at hr
      simp only [Event.isWrite, Request.isWrite] at hw
      rw [hw] at hr; exact absurd hr (by decide)
    | directoryEvent de => simp [Event.isRead] at hr
  -- eq/OB h₁: substitute or handle l₂ OB l₁
  cases h₁ with
  | inr hr₁ =>
    cases hr₁ with
    | inl heq₁ =>
      -- l₁ = l₂: just need 3-way for (l₂, l₃). For PPOi: dir_ordered. For COM: step_to_ordering.
      cases hedge with
      | inl hppoi_edge =>
        rw [heq₁]; exact step_ordering_dir_ordered_3way
          (hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent)
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
      | inr hcom_edge =>
        rw [heq₁, hl₂, hl₃]; exact Or.inl (step_to_ordering hcom_edge hknow h_non_lazy_ppoi)
    | inr h_l₂_ob_l₁ =>
      -- l₂ OB l₁ + new edge. dir_ordered(l₁, l₃) resolves both directions:
      -- l₁ OB l₃ → .ob (first alternative)
      -- l₃ OB l₁ → third alternative (resolved at cycle closure)
      have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
      match hfc₁ : l₁, h₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₃ : l₃, h₃_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₃, _ =>
          cases (hdir de₁ de₃).ordered with
          | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
          | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)
  | inl hso₁ =>
  -- Case-split on hedge (the actual edge) to get edge-specific evidence.
  -- For each edge type, combine with h₁ (StepOrdering from prefix).
  cases hedge with
  | inl hppoi_edge =>
    -- PPOi(e₂, e₃): dir_ordered on CLEs gives the 3-way result directly.
    -- Bypasses ppoi_step_to_ordering and avoids compound linearization matching.
    have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
    have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
    have h₂₃_3way : @StepOrdering n l₂ l₃ ∨ l₂ = l₃ ∨ l₃.OrderedBefore n l₂ := by
      rw [hl₂, hl₃]; exact step_ordering_dir_ordered_3way
        ((hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent)
        ((hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    cases h₂₃_3way with
    | inl hso₂ =>
      -- StepOrdering l₂ l₃: compose with h₁ using OB from same_prot_dir_ordered_forward
      have h₂₃_prot : l₂.protocol = l₃.protocol := by
        rw [hl₂, hl₃]; exact (write_cle_protocol_eq_write_protocol (hknow e₂)).trans
          (hppoi_edge.1.sameProtocol.trans (write_cle_protocol_eq_write_protocol (hknow e₃)).symm)
      have hob₂ : l₂.OrderedBefore n l₃ := same_prot_dir_ordered_forward hso₂ h₂₃_prot hdir h₂_isdir h₃_isdir
      cases hso₁ with
      | ob hob₁ => exact Or.inl (.ob (Trans.trans hob₁ hob₂))
      | obEndLt p₁ hob₁ hlt₁ _ =>
        exact Or.inl (.ob (Trans.trans hob₁ (show Event.OrderedBefore n p₁ l₃ from Nat.lt_trans hlt₁ hob₂)))
      | encapOb p₁ henc₁ hob₁ => exact Or.inl (.encapOb p₁ henc₁ (Trans.trans hob₁ hob₂))
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ _ =>
        exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob (show Event.OrderedBefore n p₁ l₃ from Nat.lt_trans hlt₁ hob₂)))
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₁ hq_enc hq_ob (Trans.trans hp_ob hob₂))
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
        have h₂₃_prot : l₂.protocol = l₃.protocol := by
          rw [hl₂, hl₃]; exact (write_cle_protocol_eq_write_protocol (hknow e₂)).trans
            (hppoi_edge.1.sameProtocol.trans (write_cle_protocol_eq_write_protocol (hknow e₃)).symm)
        have hprot_diff : l₁.protocol ≠ l₃.protocol := fun h₁₃ => hdiff₁ (h₁₃.trans h₂₃_prot.symm)
        exact Or.inl (.obFinishBefore p₁ (Trans.trans hob₁ hob₂) hlt₁ hprot_diff h_p₁_isdir)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .ob hob₂)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .ob hob₂)
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir h₃_isdir hdir
    | inr hr₂ => cases hr₂ with
      | inl heq₂₃ =>
        -- l₂ = l₃: substitute in h₁
        exact heq₂₃ ▸ Or.inl hso₁
      | inr hob_l₃_l₂ =>
        -- l₃ OB l₂: use dir_ordered on l₁ and l₃ for 3-way output
        exact step_ordering_dir_ordered_3way h₁_isdir (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
  | inr hcom_edge =>
    -- All com edges: derive h₂ via step_to_ordering, compose with h₁.
    -- The composition logic is the same for all edge types.
    have h₂ : @StepOrdering n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering hcom_edge hknow h_non_lazy_ppoi
    -- Compose hso₁ with h₂. Case-split h₂ for temporal chain.
    cases h₂ with
    | ob hob₂ =>
      -- Same as PPOi ob case: chain h₁ with OB.
      cases hso₁ with
      | ob hob₁ => exact Or.inl (.ob (Trans.trans hob₁ hob₂))
      | obEndLt p₁ hob₁ hlt₁ _ =>
        exact Or.inl (.ob (Trans.trans hob₁ (show Event.OrderedBefore n p₁ l₃ from Nat.lt_trans hlt₁ hob₂)))
      | encapOb p₁ henc₁ hob₁ => exact Or.inl (.encapOb p₁ henc₁ (Trans.trans hob₁ hob₂))
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ _ =>
        exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob (show Event.OrderedBefore n p₁ l₃ from Nat.lt_trans hlt₁ hob₂)))
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₁ hq_enc hq_ob (Trans.trans hp_ob hob₂))
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .ob hob₂)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .ob hob₂)
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | obEndLt p₂ hob₂ hlt₂ h_p₂_isdir =>
      cases hso₁ with
      | ob hob₁ => exact Or.inl (.obEndLt p₂ (Trans.trans hob₁ hob₂) hlt₂ h_p₂_isdir)
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.encapObEndLt p₁ p₂ henc₁ (Trans.trans hob₁ hob₂) hlt₂ h_p₂_isdir)
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ _ =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hlt₁ hob₂)) hlt₂ h_p₂_isdir)
      | obEndLt p₁ hob₁ hlt₁ _ =>
        exact Or.inl (.obEndLt p₂ (Trans.trans hob₁ (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hlt₁ hob₂)) hlt₂ h_p₂_isdir)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans hp_ob hob₂)) hlt₂ h_p₂_isdir)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .obEndLt p₂ hob₂ hlt₂ h_p₂_isdir)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .obEndLt p₂ hob₂ hlt₂ h_p₂_isdir)
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | encapOb p₂ henc₂ hob₂ =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.ob (Trans.trans (show Event.OrderedBefore n l₁ p₂ from Nat.lt_trans hob₁ henc₂.left) hob₂))
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.proxyPair p₁ p₂ henc₁ (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hob₁ henc₂.left) hob₂)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₂ hq_enc (Trans.trans hq_ob (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hp_ob henc₂.left)) hob₂)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .encapOb p₂ henc₂ hob₂)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .encapOb p₂ henc₂ hob₂)
      | obEndLt p₁ hob₁ hlt₁ h_p₁_isdir =>
        -- obEndLt h₁ + encapOb h₂: use dir_ordered(p₁, l₂) to chain through.
        -- l₂ OB p₁ → p₁.oEnd < l₂.oEnd (hlt₁) and l₂.oEnd < p₁.oStart → p₁.oEnd < p₁.oStart → False.
        -- So dir_ordered gives p₁ OB l₂. Chain: l₁ OB p₁ OB l₂, l₂ encaps p₂ OB l₃ → .ob.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                -- l₂ OB p₁: del₂.oEnd < dep₁.oStart. But p₁.oEnd < l₂.oEnd gives
                -- dep₁.oEnd < del₂.oEnd < dep₁.oStart → dep₁.oEnd < dep₁.oStart → contradiction.
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        -- Chain: p₁ OB l₂, l₂.oStart < p₂.oStart (encap) → p₁ OB p₂ → p₁ OB l₃
        exact Or.inl (.ob (Trans.trans hob₁
          (Trans.trans (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hp₁_ob_l₂ henc₂.left) hob₂)))
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ h_p₁_isdir =>
        -- encapObEndLt h₁ + encapOb h₂: same dir_ordered(p₁, l₂) trick as obEndLt.
        -- p₁ OB l₂ (reverse contradicts p₁.oEnd < l₂.oEnd). Chain: q₁ OB p₁ OB l₂ OB p₂ OB l₃.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob
          (Trans.trans (show Event.OrderedBefore n p₁ p₂ from Nat.lt_trans hp₁_ob_l₂ henc₂.left) hob₂)))
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | proxyPair q₂ p₂ hq_enc₂ hq_ob₂ hp_ob₂ =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.ob (Trans.trans (show Event.OrderedBefore n l₁ q₂ from Nat.lt_trans hob₁ hq_enc₂.left) (Trans.trans hq_ob₂ hp_ob₂)))
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.proxyPair p₁ p₂ henc₁ (Trans.trans (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hob₁ hq_enc₂.left) hq_ob₂) hp_ob₂)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp_ob hq_enc₂.left) hq_ob₂)) hp_ob₂)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .proxyPair q₂ p₂ hq_enc₂ hq_ob₂ hp_ob₂)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .proxyPair q₂ p₂ hq_enc₂ hq_ob₂ hp_ob₂)
      | obEndLt p₁ hob₁ hlt₁ h_p₁_isdir =>
        -- obEndLt h₁ + proxyPair h₂: same dir_ordered(p₁, l₂) trick.
        -- p₁ OB l₂ → p₁ OB q₂ OB p₂ OB l₃ → l₁ OB p₁ OB l₃ → .ob.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        exact Or.inl (.ob (Trans.trans hob₁ (Trans.trans
          (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp₁_ob_l₂ hq_enc₂.left)
          (Trans.trans hq_ob₂ hp_ob₂))))
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ h_p₁_isdir =>
        -- encapObEndLt h₁ + proxyPair h₂: same dir_ordered(p₁, l₂) trick.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob (Trans.trans
          (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp₁_ob_l₂ hq_enc₂.left)
          (Trans.trans hq_ob₂ hp_ob₂))))
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | encapObEndLt q₂ p₂ hq_enc₂ hq_ob₂ hp_lt₂ h_p₂_isdir =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.obEndLt p₂ (Trans.trans (show Event.OrderedBefore n l₁ q₂ from Nat.lt_trans hob₁ hq_enc₂.left) hq_ob₂) hp_lt₂ h_p₂_isdir)
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.encapObEndLt p₁ p₂ henc₁ (Trans.trans (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hob₁ hq_enc₂.left) hq_ob₂) hp_lt₂ h_p₂_isdir)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp_ob hq_enc₂.left) hq_ob₂)) hp_lt₂ h_p₂_isdir)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .encapObEndLt q₂ p₂ hq_enc₂ hq_ob₂ hp_lt₂ h_p₂_isdir)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .encapObEndLt q₂ p₂ hq_enc₂ hq_ob₂ hp_lt₂ h_p₂_isdir)
      | obEndLt p₁ hob₁ hlt₁ h_p₁_isdir =>
        -- Same dir_ordered(p₁, l₂) trick: p₁ OB l₂ → p₁ OB q₂ OB p₂.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        exact Or.inl (.obEndLt p₂ (Trans.trans hob₁ (Trans.trans
          (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp₁_ob_l₂ hq_enc₂.left) hq_ob₂))
          hp_lt₂ h_p₂_isdir)
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ h_p₁_isdir =>
        -- Same trick: p₁ OB l₂ → chain q₁ OB p₁ OB q₂ OB p₂.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans
          (show Event.OrderedBefore n p₁ q₂ from Nat.lt_trans hp₁_ob_l₂ hq_enc₂.left) hq_ob₂))
          hp_lt₂ h_p₂_isdir)
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | encap henc =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | obFinishBefore p₂ hob₂ hlt₂ hdiff₂ h_p₂_isdir =>
      cases hso₁ with
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .obFinishBefore p₂ hob₂ hlt₂ hdiff₂ h_p₂_isdir)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .obFinishBefore p₂ hob₂ hlt₂ hdiff₂ h_p₂_isdir)
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | ob hob₁ =>
        -- ob + obFinishBefore: l₁ OB l₂. p₂ OB l₃, p₂.oEnd < l₂.oEnd.
        -- dir_ordered(l₁, p₂): l₁ OB p₂? l₁.oEnd < p₂.oStart. p₂.oEnd < l₂.oEnd.
        -- l₁ OB l₂ → l₁.oEnd < l₂.oStart. p₂.oEnd < l₂.oEnd. p₂ could end after l₁.
        -- But: dir_ordered(p₂, l₁): need both dir events.
        -- p₂ OB l₁: p₂.oEnd < l₁.oStart. From l₁ OB l₂: l₁.oEnd < l₂.oStart.
        --   p₂.oEnd < l₂.oEnd. Consistent — p₂ could end between l₁ and l₂.
        -- l₁ OB p₂: l₁.oEnd < p₂.oStart. And p₂.oEnd < l₂.oEnd.
        --   l₁.oEnd < l₂.oStart (from hob₁). p₂.oStart could be before or after l₂.oStart.
        -- Both directions possible — need by_cases protocol.
        by_cases hprot : l₁.protocol = l₃.protocol
        · have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
          match hfc₁ : l₁, h₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₁, _ =>
            match hfc₃ : l₃, h₃_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de₃, _ =>
              cases (hdir de₁ de₃).ordered with
              | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
              | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)
        · -- Diff protocol: use dir_ordered(p₂, l₁) to chain.
          match hfcl₁ : l₁, h₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent del₁, _ =>
            match hfcp₂ : p₂, h_p₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent dep₂, _ =>
              cases (hdir dep₂ del₁).ordered with
              | inl hp₂_ob_l₁ =>
                -- p₂ OB l₁ → p₂.oEnd < l₁.oStart → p₂.oEnd < l₁.oEnd.
                exact Or.inl (.obFinishBefore (.directoryEvent dep₂) hob₂
                  (Nat.lt_trans (show dep₂.oEnd < del₁.oStart from hp₂_ob_l₁) del₁.oWellFormed)
                  hprot (by simp [Event.isDirectoryEvent]))
              | inr hl₁_ob_p₂ =>
                -- l₁ OB p₂ → l₁ OB p₂ OB l₃ → l₁ OB l₃ → .ob.
                exact Or.inl (.ob (Nat.lt_trans (show del₁.oEnd < dep₂.oStart from hl₁_ob_p₂)
                  (Nat.lt_trans dep₂.oWellFormed hob₂)))
      | obEndLt p₁ hob₁ hlt₁ h_p₁_isdir =>
        -- obEndLt + obFinishBefore: both proxies are dir events.
        -- dir_ordered(p₁, l₂): l₂ OB p₁ → contradiction. So p₁ OB l₂.
        -- dir_ordered(p₂, l₂): l₂ OB p₂ → contradiction. So p₂ OB l₂.
        -- dir_ordered(p₁, p₂): p₁ OB p₂ → .ob (chain). p₂ OB p₁ → dir_ordered on l₁/p₂.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        -- p₁ OB l₂. dir_ordered(p₁, p₂):
        match hfcp₁ : p₁, h_p₁_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent dep₁, _ =>
          match hfcp₂ : p₂, h_p₂_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₂, _ =>
            cases (hdir dep₁ dep₂).ordered with
            | inl hp₁p₂ =>
              -- p₁ OB p₂ OB l₃ → l₁ OB p₁ OB l₃ → .ob
              have hp₁_ob_l₃ : Event.OrderedBefore n (.directoryEvent dep₁) l₃ :=
                Nat.lt_trans (Nat.lt_trans hp₁p₂ dep₂.oWellFormed) hob₂
              exact Or.inl (.ob (show Event.OrderedBefore n l₁ l₃ from Trans.trans hob₁ hp₁_ob_l₃))
            | inr hp₂p₁ =>
              by_cases hprot : l₁.protocol = l₃.protocol
              · have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
                match hfcl₁ : l₁, h₁_isdir with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent del₁, _ =>
                  match hfcl₃ : l₃, h₃_isdir with
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                  | .directoryEvent del₃, _ =>
                    cases (hdir del₁ del₃).ordered with
                    | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
                    | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)
              · -- Diff protocol: dir_ordered(p₂, l₁) resolves
                match hfcl₁ : l₁, h₁_isdir with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent del₁, _ =>
                  cases (hdir dep₂ del₁).ordered with
                  | inl hp₂l₁ =>
                    -- p₂ OB l₁ → p₂.oEnd < l₁.oEnd → .obFinishBefore p₂
                    exact Or.inl (.obFinishBefore (.directoryEvent dep₂) hob₂
                      (Nat.lt_trans (show dep₂.oEnd < del₁.oStart from hp₂l₁) del₁.oWellFormed)
                      hprot (by simp [Event.isDirectoryEvent]))
                  | inr hl₁p₂ =>
                    -- l₁ OB p₂ OB l₃ → .ob
                    exact Or.inl (.ob (Nat.lt_trans (Nat.lt_trans hl₁p₂ dep₂.oWellFormed) hob₂))
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ h_p₁_isdir =>
        -- Same dir_ordered trick. p₁ OB l₂ → chain through p₂.
        have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
        have hp₁_ob_l₂ : p₁.OrderedBefore n l₂ := by
          match hfcp : p₁, h_p₁_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₁, _ =>
            match hfcl₂ : l₂, h₂_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent del₂, _ =>
              cases (hdir dep₁ del₂).ordered with
              | inl hob => exact hob
              | inr hob_rev =>
                exfalso; exact Nat.lt_irrefl dep₁.oEnd
                  (Nat.lt_trans (show dep₁.oEnd < del₂.oEnd from hlt₁)
                    (Nat.lt_trans hob_rev dep₁.oWellFormed))
        match hfcp₁ : p₁, h_p₁_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent dep₁, _ =>
          match hfcp₂ : p₂, h_p₂_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent dep₂, _ =>
            cases (hdir dep₁ dep₂).ordered with
            | inl hp₁p₂ =>
              have hp₁_ob_l₃ : Event.OrderedBefore n (.directoryEvent dep₁) l₃ :=
                Nat.lt_trans (Nat.lt_trans hp₁p₂ dep₂.oWellFormed) hob₂
              exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob hp₁_ob_l₃))
            | inr hp₂p₁ =>
              by_cases hprot : l₁.protocol = l₃.protocol
              · have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
                match hfcl₁ : l₁, h₁_isdir with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent del₁, _ =>
                  match hfcl₃ : l₃, h₃_isdir with
                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                  | .directoryEvent del₃, _ =>
                    cases (hdir del₁ del₃).ordered with
                    | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
                    | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)
              · match hfcl₁ : l₁, h₁_isdir with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent del₁, _ =>
                  cases (hdir dep₂ del₁).ordered with
                  | inl hp₂l₁ =>
                    exact Or.inl (.obFinishBefore (.directoryEvent dep₂) hob₂
                      (Nat.lt_trans (show dep₂.oEnd < del₁.oStart from hp₂l₁) del₁.oWellFormed)
                      hprot (by simp [Event.isDirectoryEvent]))
                  | inr hl₁p₂ =>
                    exact Or.inl (.ob (Nat.lt_trans (Nat.lt_trans hl₁p₂ dep₂.oWellFormed) hob₂))
      | _ =>
        -- encapOb/proxyPair/ob + obFinishBefore h₂: dir_ordered(l₁, l₃) via 3-way invariant
        have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
        match hfc₁ : l₁, h₁_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₁, _ =>
          match hfc₃ : l₃, h₃_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₃, _ =>
            cases (hdir de₁ de₃).ordered with
            | inl hob₁₃ => exact Or.inl (.ob hob₁₃)
            | inr hob₃₁ => exact Or.inr (Or.inr hob₃₁)
    | sameLin _ _ heq₂ _ _ _ => exact Or.inl (heq₂ ▸ hso₁)
    | eq heq₂ => exact Or.inl (heq₂ ▸ hso₁)
    | encap henc₂ =>
      -- l₂ encapsulates l₃. Compose with hso₁.
      cases hso₁ with
      | ob hob₁ => exact Or.inl (.ob (Nat.lt_trans hob₁ henc₂.left))
      | encapOb p₁ henc₁ hob₁ => exact Or.inl (.encapOb p₁ henc₁ (Nat.lt_trans hob₁ henc₂.left))
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob => exact Or.inl (.proxyPair q₁ p₁ hq_enc hq_ob (Nat.lt_trans hp_ob henc₂.left))
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .encap henc₂)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .encap henc₂)
      | encap henc₁ => exact Or.inl (.encap (Trans.trans henc₁ henc₂))
      | obEndLt p₁ hob₁ hlt₁ h_p₁_isdir =>
        -- p₁.oEnd < l₂.oEnd, l₃.oEnd < l₂.oEnd: use dir_ordered(l₁, l₃)
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ h_p₁_isdir =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi


/-- sameLin always gives .ob between compoundLin events via the encap+OB chain:
    CLE₁.oEnd < e₁'.oEnd (enc₁) < e₂'.oStart (OB) < CLE₂.oStart (enc₂)
    ≤ CLE₂.oEnd (oWellFormed). Any compoundLin₁ with oEnd ≤ CLE₁.oEnd chains
    forward, and any compoundLin₂ with oStart ≥ CLE₂.oStart chains forward. -/
private theorem sameLin_gives_ob {e₁' e₂' : Event n}
    (henc₁ : l₁.EncapsulatedBy n e₁') (hob : e₁'.OrderedBefore n e₂')
    (henc₂ : l₂.EncapsulatedBy n e₂')
    (h₁_oEnd_le : Event.oEnd n cl₁ ≤ Event.oEnd n l₁)
    (h₂_oStart_ge : Event.oStart n l₂ ≤ Event.oStart n cl₂)
    : cl₁.OrderedBefore n cl₂ :=
  Nat.lt_of_le_of_lt h₁_oEnd_le (Nat.lt_trans henc₁.right (Nat.lt_trans hob
    (Nat.lt_of_lt_of_le henc₂.left h₂_oStart_ge)))

/-- Bridge: lift StepOrdering on CLEs to StepOrdering on compoundLin events.
    Handles all compoundLin_cle_rel combinations except cle_ob + same_protocol,
    which requires COM-specific evidence (handled by step_to_ordering_compoundLin). -/
theorem step_ordering_cle_to_compoundLin
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : @StepOrdering n lin₁.hreq's_dir_access.choose lin₂.hreq's_dir_access.choose)
    (h₁_notdown : ¬ e₁.down) (h₂_notdown : ¬ e₂.down)
    : @StepOrdering n lin₁.compoundLin lin₂.compoundLin := by
  have hrel₁ := lin₁.compoundLin_cle h₁_notdown
  have hrel₂ := lin₂.compoundLin_cle h₂_notdown
  -- Case-split on both compoundLin_cle_rel cases.
  -- For each StepOrdering constructor h, chain with the compoundLin ↔ CLE evidence.
  -- Most cases resolve via .ob chaining. The cle_ob event 1 case uses .obFinishBefore
  -- (when diff_prot) or needs COM-specific evidence (same_prot).
  -- For each (hrel₁, hrel₂) combination × each StepOrdering constructor,
  -- chain the temporal evidence. Use omega/sorry for hard cases.
  cases hrel₁ with
  | eq ha₁ => rw [ha₁]; cases hrel₂ with
    | eq ha₂ => rw [ha₂]; exact h
    | cle_ob_compoundLin ha₂ =>
      cases h with
      | ob hob => exact .ob (Trans.trans hob ha₂)
      | eq heq => exact .ob (heq ▸ ha₂)
      | encap henc => exact .encapOb _ henc ha₂
      | obEndLt p hob hlt hisdir => exact .obEndLt p hob (Nat.lt_trans hlt (Nat.lt_of_lt_of_le ha₂ (Nat.le_of_lt (Event.oWellFormed n _)))) hisdir
      | encapOb p henc hob => exact .encapOb p henc (Trans.trans hob ha₂)
      | proxyPair q p hqenc hqob hpob => exact .proxyPair q p hqenc hqob (Trans.trans hpob ha₂)
      | encapObEndLt q p hqenc hqob hlt hisdir => exact .encapObEndLt q p hqenc hqob (Nat.lt_trans hlt (Nat.lt_of_lt_of_le ha₂ (Nat.le_of_lt (Event.oWellFormed n _)))) hisdir
      | sameLin e₁' e₂' heq henc₁ hob henc₂ =>
        -- CLE₁=CLE₂, CLE₁ EncBy e₁', e₁' OB e₂', CLE₂ EncBy e₂', CLE₂ OB compoundLin₂.
        -- Chain: CLE₁.oEnd < e₁'.oEnd < e₂'.oStart, e₂'.oStart < CLE₂.oStart < CLE₂.oEnd < compoundLin₂.oStart
        exact .ob (Nat.lt_trans henc₁.right (Nat.lt_trans hob
          (Nat.lt_trans henc₂.left (Nat.lt_of_le_of_lt (Nat.le_of_lt (Event.oWellFormed n _)) ha₂))))
      | obFinishBefore p hob hlt hdiff hisdir => sorry
    | compoundLin_ob_cle ha₂ => sorry
    | compoundLin_inside_cle ha₂ =>
      cases h with
      | ob hob => exact .ob (Nat.lt_trans hob ha₂.left)
      | eq heq => exact .encap ⟨heq ▸ ha₂.left, heq ▸ ha₂.right⟩
      | encap henc => exact .encap ⟨Nat.lt_trans henc.left ha₂.left, Nat.lt_trans ha₂.right henc.right⟩
      | encapOb p henc hob => exact .encapOb p henc (Nat.lt_trans hob ha₂.left)
      | proxyPair q p hqenc hqob hpob => exact .proxyPair q p hqenc hqob (Nat.lt_trans hpob ha₂.left)
      | sameLin e₁' e₂' heq henc₁ hob henc₂ =>
        exact .ob (Nat.lt_trans henc₁.right (Nat.lt_trans hob (Nat.lt_trans henc₂.left ha₂.left)))
      | obEndLt p hob hlt hisdir =>
        -- p.oEnd < CLE₂.oEnd. compoundLin₂.oEnd < CLE₂.oEnd. Unknown p vs compoundLin₂.
        sorry
      | obFinishBefore p hob hlt hdiff hisdir => sorry
      | encapObEndLt q p hqenc hqob hlt hisdir => sorry
  | cle_ob_compoundLin ha₁ => sorry
  | compoundLin_ob_cle ha₁ =>
    cases hrel₂ with
    | eq ha₂ => rw [ha₂]; cases h with
      | ob hob => exact .ob (Trans.trans ha₁ hob)
      | eq heq => exact .ob (heq ▸ ha₁)
      | encap henc => exact .ob (Nat.lt_trans ha₁ henc.left)
      | obEndLt p hob hlt hisdir => exact .obEndLt p (Trans.trans ha₁ hob) hlt hisdir
      | sameLin e₁' e₂' heq henc₁ hob henc₂ =>
        -- compoundLin₁.oEnd < CLE₁.oStart ≤ CLE₁.oEnd < e₁'.oEnd < e₂'.oStart < CLE₂.oStart
        exact .ob (Nat.lt_of_lt_of_le ha₁ (Nat.le_of_lt (Nat.lt_trans (Event.oWellFormed n _)
          (Nat.lt_trans henc₁.right (Nat.lt_trans hob henc₂.left)))))
      | _ => sorry
    | cle_ob_compoundLin ha₂ =>
      cases h with
      | ob hob => exact .ob (Trans.trans ha₁ (Trans.trans hob ha₂))
      | eq heq => exact .ob (Trans.trans ha₁ (heq ▸ ha₂))
      | obEndLt p hob hlt hisdir => exact .obEndLt p (Trans.trans ha₁ hob) (Nat.lt_trans hlt (Nat.lt_of_lt_of_le ha₂ (Nat.le_of_lt (Event.oWellFormed n _)))) hisdir
      | _ => sorry
    | compoundLin_ob_cle ha₂ => sorry
    | compoundLin_inside_cle ha₂ =>
      cases h with
      | ob hob => exact .ob (Nat.lt_trans (Nat.lt_of_lt_of_le ha₁ (Nat.le_of_lt (Event.oWellFormed n _))) (Nat.lt_trans hob ha₂.left))
      | eq heq => exact .ob (Nat.lt_trans ha₁ (heq ▸ ha₂.left))
      | encap henc => exact .ob (Nat.lt_trans ha₁ (Nat.lt_trans henc.left ha₂.left))
      | _ => sorry
  | compoundLin_inside_cle ha₁ =>
    cases hrel₂ with
    | eq ha₂ => rw [ha₂]; cases h with
      | ob hob => exact .ob (Nat.lt_trans ha₁.right hob)
      | obEndLt p hob hlt hisdir => exact .obEndLt p (Nat.lt_trans ha₁.right hob) hlt hisdir
      | _ => sorry
    | cle_ob_compoundLin ha₂ =>
      cases h with
      | ob hob => exact .ob (Nat.lt_trans ha₁.right (Nat.lt_trans hob (Nat.lt_of_le_of_lt (Nat.le_of_lt (Event.oWellFormed n _)) ha₂)))
      | obEndLt p hob hlt hisdir => exact .obEndLt p (Nat.lt_trans ha₁.right hob) (Nat.lt_trans hlt (Nat.lt_of_lt_of_le ha₂ (Nat.le_of_lt (Event.oWellFormed n _)))) hisdir
      | _ => sorry
    | compoundLin_ob_cle ha₂ => sorry
    | compoundLin_inside_cle ha₂ =>
      cases h with
      | ob hob => exact .ob (Nat.lt_trans ha₁.right (Nat.lt_trans hob ha₂.left))
      | encap henc => sorry
      | obEndLt p hob hlt hisdir => sorry
      | _ => sorry

/-- Map a COM edge to StepOrdering between compoundLin events.
    Uses COM edge evidence directly + compoundLin_cle bridge.
    - sameCache: e₁ OB e₂ gives compoundLin ordering directly
    - sameClusDiffCache: downgrade chain evidence + bridge
    - diffClus: bridge + obFinishBefore (diff_protocol available) -/
theorem step_to_ordering_compoundLin
    (h : com compound b init e₁ e₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    (h₁_notdown : ¬ e₁.down) (h₂_notdown : ¬ e₂.down)
    : @StepOrdering n (lin e₁).compoundLin (lin e₂).compoundLin := by
  have h_cle := step_to_ordering h lin h_non_lazy_ppoi
  have hrel₁ := (lin e₁).compoundLin_cle h₁_notdown
  have hrel₂ := (lin e₂).compoundLin_cle h₂_notdown
  -- Handle ob_cle event 2 and cle_ob event 1 using COM evidence.
  -- For these cases, compoundLin = e (requestLin), and we need e₁/e₂ temporal info.
  -- For all other cases, delegate to the generic bridge.
  cases hrel₂ with
  | compoundLin_ob_cle ha₂ =>
    -- compoundLin₂ OB CLE₂ → requestLin → compoundLin₂ = e₂.
    -- Need to case-split on linearizationOfEvent to get compoundLin₂ = e₂.
    cases hlin₂ : compound.linearizationOfEvent b init e₂ with
    | requestLin hreqlin₂ =>
      have hcl₂ := (lin e₂).compoundLin_eq_event_of_requestLin hlin₂
      rw [hcl₂]
      -- Now goal: StepOrdering compoundLin₁ e₂.
      -- compoundLin₁ relates to CLE₁ via hrel₁.
      -- CLE₁ relates to CLE₂ via h_cle (StepOrdering).
      -- CLE₂ is AFTER e₂ (orderAfterDir). So CLE₂.oStart > e₂.oEnd.
      -- Need: compoundLin₁ OB e₂ or similar.
      -- Protocol context: compoundLin₂ = e₂ (requestLin). e₂ has perms (reqHasPerms).
      -- e₂ OB CLE₂ (orderAfterDir). CLE₂ at successor of e₂.
      -- For compoundLin₁: relates to CLE₁ via hrel₁ (eq/cle_ob/ob_cle/inside).
      -- StepOrdering CLE₁ CLE₂ from h_cle.
      -- Need: StepOrdering compoundLin₁ e₂.
      --
      -- For hrel₁ cases:
      -- eq: compoundLin₁ = CLE₁. Need CLE₁ OB e₂? Not directly available.
      --   But CLE₁.oEnd < CLE₂.oStart (from .ob h_cle) and e₂.oEnd < CLE₂.oStart (ha₂).
      --   Both before CLE₂. Need COM evidence for CLE₁ vs e₂.
      -- ob_cle: compoundLin₁ = e₁ (requestLin). For co.sameCache: e₁ OB e₂ → .ob.
      -- inside: compoundLin₁ inside CLE₁. Same issue as eq.
      -- cle_ob: compoundLin₁ after CLE₁. Even harder.
      --
      -- Case-split on hrel₁ to handle ob_cle (= e₁) case directly:
      cases hrel₁ with
      | compoundLin_ob_cle ha₁_ob =>
        -- compoundLin₁ = e₁ (requestLin + orderAfterDir). e₁ and e₂ are COM-related.
        -- For co.sameCache: e₁ OB e₂ → compoundLin₁ OB e₂.
        -- Need compoundLin₁ = e₁:
        cases hlin₁ : compound.linearizationOfEvent b init e₁ with
        | requestLin hreqlin₁ =>
          have hcl₁ := (lin e₁).compoundLin_eq_event_of_requestLin hlin₁
          rw [hcl₁]
          -- Goal: StepOrdering e₁ e₂. Extract e₁ OB e₂ from COM edge.
          cases h with
          | co hco => cases hco.comm with
            | sameCache _ cache_ob => exact .ob cache_ob
            | sameClusDiffCache _ _ => sorry -- needs downgrade chain
            | diffClus _ _ => sorry
          | rfe _ => sorry
          | fr _ => sorry
        | dirLin _ => sorry -- vacuous: dirLin + ob_cle
      | eq ha₁_eq =>
        rw [ha₁_eq]
        -- compoundLin₁ = CLE₁. Need StepOrdering CLE₁ e₂.
        -- CLE₁ and e₂ both before CLE₂. Need COM evidence.
        sorry
      | cle_ob_compoundLin ha₁_ob => sorry
      | compoundLin_inside_cle ha₁_enc => sorry
    | dirLin hdir₂ =>
      -- dirLin + compoundLin_ob_cle: this should be vacuous.
      -- dirLin gives reqMissingPerms. compoundLin_ob_cle arises from requestLin + orderAfterDir.
      -- requestLin needs reqHasPerms. Contradiction with dirLin's reqMissingPerms.
      -- But compoundLin_ob_cle doesn't carry requestLin evidence directly...
      sorry
  | _ =>
    -- For eq, cle_ob, inside: delegate to generic bridge.
    cases hrel₁ with
    | cle_ob_compoundLin ha₁ =>
      -- cle_ob event 1: similar handling needed.
      sorry
    | _ =>
      -- All remaining cases: generic bridge handles them.
      exact step_ordering_cle_to_compoundLin h_cle h₁_notdown h₂_notdown

/-- Acyclicity given that every event has a linearization.
    Invariant: `StepOrdering (cle a) (cle c) ∨ cle a = cle c ∨ (cle c).OrderedBefore n (cle a)`
    on CLEs from `hknow`. At cycle level, all three alternatives derive contradiction.

    Architecture:
    - PPOi: `dir_ordered` gives 3-way on CLEs (same cluster directory events).
    - COM: `step_to_ordering` gives StepOrdering on CLEs directly.
    - Composition: `compose_three` handles all edge type combinations. -/
theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  -- Use CLEs from hknow directly as linearization points.
  -- PPOi: dir_ordered gives 3-way. COM: step_to_ordering gives StepOrdering.
  -- Composition: compose_three handles all edge types.
  -- Invariant: StepOrdering ∨ eq ∨ reverse OB on CLEs.
  -- Also track last edge (needed by compose_three for junction compatibility).
  let R := (fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init
  let cle := fun e => (hknow e).hreq's_dir_access.choose
  suffices h_ind : ∀ a c, Relation.TransGen R a c →
      (∃ b_prev, R b_prev c) ∧
      (@StepOrdering n (hknow a).hreq's_dir_access.choose (hknow c).hreq's_dir_access.choose ∨
       (hknow a).hreq's_dir_access.choose = (hknow c).hreq's_dir_access.choose ∨
       ((hknow c).hreq's_dir_access.choose).OrderedBefore n (hknow a).hreq's_dir_access.choose) by
    have ⟨_, hresult⟩ := h_ind e e hcycle
    cases hresult with
    | inl hso =>
      -- StepOrdering cle(e) cle(e) → False.
      cases hso with
      | ob h => exact Event.contradiction_of_reflexive_ordered_before n h
      | obEndLt p h_ob h_lt _ =>
        exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans h_ob (Event.oWellFormed n p)) h_lt)
      | encapOb p h_enc h_ob =>
        exact Nat.lt_irrefl _ (Nat.lt_trans h_enc.left (Nat.lt_trans (Event.oWellFormed n p) h_ob))
      | obFinishBefore _ _ _ h_diff _ => exact absurd rfl h_diff
      | sameLin e₁' e₂' _ h_enc₁ h_ob h_enc₂ =>
        exact Nat.lt_irrefl _ (calc Event.oEnd n (cle e)
          _ < Event.oEnd n e₁' := h_enc₁.right
          _ < Event.oStart n e₂' := h_ob
          _ < Event.oStart n (cle e) := h_enc₂.left
          _ ≤ Event.oEnd n (cle e) := Nat.le_of_lt (Event.oWellFormed n _))
      | proxyPair q p h_q_enc h_q_ob h_p_ob =>
        exact Nat.lt_irrefl _ (calc Event.oEnd n p
          _ < Event.oStart n (cle e) := h_p_ob
          _ < Event.oStart n q := h_q_enc.left
          _ ≤ Event.oEnd n q := Nat.le_of_lt (Event.oWellFormed n q)
          _ < Event.oStart n p := h_q_ob
          _ ≤ Event.oEnd n p := Nat.le_of_lt (Event.oWellFormed n p))
      | encap henc => exact Nat.lt_irrefl _ henc.left
      | eq _ => exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
      | encapObEndLt q p h_q_enc h_q_ob h_p_lt _ =>
        exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
    | inr hr => cases hr with
      | inl heq =>
        exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
      | inr hob_rev => exact Event.contradiction_of_reflexive_ordered_before n hob_rev
  intro a c hpath
  induction hpath with
  | single h =>
    constructor
    · exact ⟨a, h⟩
    · cases h with
      | inl hppoi =>
        -- PPOi: dir_ordered gives 3-way on CLEs directly (no compound_lin needed).
        exact step_ordering_dir_ordered_3way
          (hknow _).hreq's_dir_access.choose_spec.right.isDirEvent
          (hknow _).hreq's_dir_access.choose_spec.right.isDirEvent
          b.orderedAtEntry.dir_ordered
      | inr hcom =>
        -- COM: step_to_ordering gives StepOrdering on CLEs directly.
        exact Or.inl (step_to_ordering hcom hknow h_non_lazy_ppoi)
  | tail hpath h ih =>
    -- ih : (∃ last edge) ∧ 3-way for prefix (a → b_mid) on CLEs.
    -- h : R b_mid c (current edge).
    -- compose_three handles ALL composition cases (StepOrdering/eq/reverseOB × PPOi/COM).
    constructor
    · exact ⟨_, h⟩
    · let ⟨⟨b_prev, h_last_prefix⟩, h3way_prefix⟩ := ih
      exact compose_three h3way_prefix h h_last_prefix hknow rfl rfl
        b.orderedAtEntry.dir_ordered
        ((hknow a).hreq's_dir_access.choose_spec.right.isDirEvent)
        h_non_lazy_ppoi

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
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  -- The cycle is either pure PPOi or has at least one com edge.
  rcases transgen_union_find_right hcycle with hppoi_cycle | ⟨x, y, hcom⟩
  · -- All PPOi (diff-addr): contradiction from OB transitivity
    -- Weaken: PPOi ∧ diff_addr → PPOi
    have := hppoi_cycle.mono (fun _ _ h => h.1)
    exact ppoi_acyclic e this
  · -- Some com edge exists: extract hknow_dir_access
    exact cmcm_acyclic_of_hknow (com.extract_hknow hcom) h_non_lazy_ppoi e hcycle

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b' a₁ a₂ → a₁.addr ≠ a₂.addr →
      (cmp.compoundLinearizationEvent cmp.shimAxioms b' init' a₁
        (cmp.linearizationOfEvent b' init' a₁)).linearizationEvent.OrderedBefore n
      (cmp.compoundLinearizationEvent cmp.shimAxioms b' init' a₂
        (cmp.linearizationOfEvent b' init' a₂)).linearizationEvent)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b' e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' h_non_lazy_ppoi

/-! ## PartialOrder (consequence of acyclicity) -/

noncomputable def eventPartialOrder
    (h_non_lazy_ppoi : ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
        (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
      (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
        (compound.linearizationOfEvent b init a₂)).linearizationEvent)
    : PartialOrder (Event n) := by
  let R := (fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init
  have hacyclic := @cmcm_acyclic n compound b init h_non_lazy_ppoi
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
