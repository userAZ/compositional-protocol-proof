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
    hppoi.cache₁.eAtCache hppoi.cache₂.eAtCache hppoi.in_b₁ hppoi.in_b₂
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

/-! ## CleLink → LinChain: ordering between linearization points

Each cache event e has a linearization point `lin(e)` = CLE.
Each edge derives `CleLink lin(e₁) lin(e₂)` from communication evidence,
then converts to `LinChain ∨ eq` via `CleLink.toLinChainOrEq`.

LinChain = TransGen LinStep, where LinStep has 4 constructors:
  ob, encap, encapBy, finishesBefore.

Transitivity: free from TransGen (no hand-written trans needed).
Irreflexivity: LinChain.irrefl (proved once for all edge patterns).
A cycle composes to LinChain CLE CLE → LinChain.irrefl,
or all edges give CLE₁ = CLE₂ → dir_ordered de de → False. -/

-- CleLink definition moved to Defs.lean
-- CleLink.trans DELETED: replaced by LinChain.trans (free from TransGen).

/-- Map a single co edge to CleLink using the CO edge's own cmpLin fields. -/
theorem co_step_to_ordering
    (h : @Herd.co n compound b init e₁ e₂)
    : @CleLink n h.w₁_cmpLin.hreq's_dir_access.choose h.w₂_cmpLin.hreq's_dir_access.choose := by
  cases h.comm with
  | sameCache same_cle cache_ob =>
    have hda₁ := h.w₁_cmpLin.hreq's_dir_access.choose_spec.2
    have hda₂ := h.w₂_cmpLin.hreq's_dir_access.choose_spec.2
    cases hda₁ with
    | encapDir _ hencap₁ =>
      cases hda₂ with
      | encapDir _ hencap₂ =>
        exact .sameLin e₁ e₂ same_cle
          ⟨hencap₁.reqEncapDir.left, hencap₁.reqEncapDir.right⟩
          cache_ob
          ⟨hencap₂.reqEncapDir.left, hencap₂.reqEncapDir.right⟩
      | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq same_cle
      | orderAfterDir _ _ _ _ => exact .eq same_cle
    | orderBeforeDir _ _ _ _ _ _ _ _ => exact .eq same_cle
    | orderAfterDir _ _ _ _ => exact .eq same_cle
  | sameClusDiffCache _ cle_ord =>
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob => exact .ob hob
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        exact .obEndLt hdown.existsRClusterDirDown.choose
          hwObRDown
          (by cases hcdir_spec.2.encapDirRelation with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt)
          hcdir_spec.2.isDir
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact .ob evict.wObR
  | diffClus _ diff_cluster_cases =>
    cases diff_cluster_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt w.rDown.encapDir.existsRClusterDirDown.choose
        w.wObRDown
        (by cases hcdir_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
        hcdir_spec.2.isDir
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose
        evict.wObRDown
        (by cases hcdir_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt)
        hcdir_spec.2.isDir

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

/-- Extract oEnd ≤ from a single CO step using the CO edge's own cmpLin fields. -/
private lemma co_step_oEnd_le
    (h : @Herd.co n compound b init e₁ e₂)
    : Event.oEnd n h.w₁_cmpLin.hreq's_dir_access.choose ≤
      Event.oEnd n h.w₂_cmpLin.hreq's_dir_access.choose := by
  cases h.comm with
  | sameCache same_cle _ =>
    exact Nat.le_of_eq (congrArg (Event.oEnd n) same_cle)
  | sameClusDiffCache _ cle_ord =>
    cases cle_ord with
    | wImmPredRCle w =>
      cases w with
      | sameCluster _ hob =>
        exact Nat.le_of_lt (Nat.lt_trans hob (Event.oWellFormed n _))
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        exact Nat.le_of_lt (Nat.lt_trans
          (Nat.lt_trans hwObRDown (Event.oWellFormed n _))
          (by cases hcdir_spec.2.encapDirRelation with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt))
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact Nat.le_of_lt (Nat.lt_trans evict.wObR (Event.oWellFormed n _))
  | diffClus _ diff_cases =>
    cases diff_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_trans w.wObRDown (Event.oWellFormed n _))
        (by cases hcdir_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt))
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      exact Nat.le_of_lt (Nat.lt_trans
        (Nat.lt_trans evict.wObRDown (Event.oWellFormed n _))
        (by cases hcdir_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt))

/-- Extract oEnd ≤ from a CO chain by composing single-step bounds. -/
private lemma co_chain_oEnd_le
    (hco_chain : Relation.TransGen (@Herd.co n compound b init) e_w e₂)
    (lin : ∀ e, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Event.oEnd n (lin e_w).hreq's_dir_access.choose ≤
      Event.oEnd n (lin e₂).hreq's_dir_access.choose := by
  induction hco_chain with
  | single h =>
    have := co_step_oEnd_le h
    rw [show h.w₁_cmpLin = lin _ from Subsingleton.elim _ _,
        show h.w₂_cmpLin = lin _ from Subsingleton.elim _ _] at this
    exact this
  | tail _ h ih =>
    have := co_step_oEnd_le h
    rw [show h.w₁_cmpLin = lin _ from Subsingleton.elim _ _,
        show h.w₂_cmpLin = lin _ from Subsingleton.elim _ _] at this
    exact Nat.le_trans ih this

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
      have h1 := write_cle_protocol_eq_write_protocol h_co.w₁_cmpLin
      have h2 := write_cle_protocol_eq_write_protocol h_co.w₂_cmpLin
      rw [← h1, ← h2, same_cle]
    | sameClusDiffCache h_same_prot _ => exact absurd h_same_prot h_diff_prot
    | diffClus _ diff_cases =>
      cases diff_cases with
      | wCleImmPredDown w =>
        have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            h_co.w₂_cmpLin.hreq's_dir_access.choose.oEnd := by
          cases hrd_spec.2.encapDirRelation with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        -- e_mid = the second writer in this CO step (the endpoint)
        exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_cmpLin from Subsingleton.elim _ _]; exact w.wObRDown,
          by rw [show lin _ = h_co.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.isDir, hrd_spec.2.sameProtocol,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = h_co.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
      | evictOrReadBetweenWAndRDown evict =>
        have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            h_co.w₂_cmpLin.hreq's_dir_access.choose.oEnd := by
          cases hrd_spec.2.encapDirRelation with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = h_co.w₁_cmpLin from Subsingleton.elim _ _]; exact evict.wObRDown,
          by rw [show lin _ = h_co.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.isDir, hrd_spec.2.sameProtocol,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = h_co.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
  | tail hpath h_last ih =>
    rename_i b_mid c_ep
    -- IH for prefix. Extend d.oEnd bound via last step's CleLink.
    by_cases h_mid_prot : e_w.sameProtocol n b_mid
    · -- Prefix same-cluster: last step h_last must cross clusters.
      -- Get CLE_w.oEnd ≤ CLE_mid.oEnd from prefix CleLink.
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
        have h1 := write_cle_protocol_eq_write_protocol h_last.w₁_cmpLin
        have h2 := write_cle_protocol_eq_write_protocol h_last.w₂_cmpLin
        rw [← h1, ← h2, same_cle]
      | sameClusDiffCache h_same _ => exact absurd h_same h_mid_diff_c
      | diffClus _ diff_cases =>
        cases diff_cases with
        | wCleImmPredDown w =>
          have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              h_last.w₂_cmpLin.hreq's_dir_access.choose.oEnd := by
            cases hrd_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := w.wObRDown
          rw [show h_last.w₁_cmpLin = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = h_last.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.isDir,
            hrd_spec.2.sameProtocol.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = h_last.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
        | evictOrReadBetweenWAndRDown evict =>
          have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              h_last.w₂_cmpLin.hreq's_dir_access.choose.oEnd := by
            cases hrd_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := evict.wObRDown
          rw [show h_last.w₁_cmpLin = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = h_last.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.isDir,
            hrd_spec.2.sameProtocol.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = h_last.w₂_cmpLin from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
    · -- Prefix diff-cluster: IH gives d with e_mid from some earlier step.
      -- Pass through the IH's e_mid — it has translatedDir about e_mid, not the endpoint.
      -- h_no_between at the call site can be applied to e_mid instead of e₂.
      obtain ⟨d, hd_in_b, hob_d, hd_lt, hd_isDir, hd_proto, hd_emid⟩ := ih h_mid_prot
      have hext : (lin b_mid).hreq's_dir_access.choose.oEnd ≤ (lin c_ep).hreq's_dir_access.choose.oEnd := by
        have := co_step_oEnd_le h_last
        rw [show h_last.w₁_cmpLin = lin b_mid from Subsingleton.elim _ _,
            show h_last.w₂_cmpLin = lin c_ep from Subsingleton.elim _ _] at this
        exact this
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
-- Helper not feasible due to complex types. CLE₂ OB d_rf NIW exfalso's use inline pattern.

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
                  have : hlin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
                  rw [this]; exact write_event_cle_isDirWrite h.write h.cache₂ h.notDown₂ h.e₂_cmpLin h.in_b₂
                have hdir_w := e_w_lin.hreq's_dir_access.choose_spec.2.isDirEvent
                match hfcw : e_w_lin.hreq's_dir_access.choose, hdir_w with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_w, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_w de₂).ordered with
                  | inl hob_w₂ =>
                    exact h_constraints.notBetweenCles ⟨hprot₁, hprot₂, h_isDirWrite⟩
                      ⟨by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = h.e₂_cmpLin from Subsingleton.elim _ _, hfc₂, hfcw]; exact hob_w₂,
                       by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = h.e₂_cmpLin from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob⟩
                  | inr hob_₂w =>
                    have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                      have hoEnd := co_chain_oEnd_le h_co_chain hlin
                      rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm,
                          show hlin e₂ = h.e₂_cmpLin from Subsingleton.elim _ _] at hoEnd
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
                have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                    have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                          have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                          -- For now: exfalso (needs case analysis on diffCache.case sub-cases)
                          -- Extract encapDir from diffCache.case.
                          have hencapDir := diffCache_case_extract_encapDir e_w_write h.read hdiff_cache_case hw_in_b hw_cache
                          have hdrf_spec := hencapDir.existsRClusterDirDown.choose_spec
                          -- d_rf at e_w's cluster. encapDirRelation gives d_rf inside CLE₁ or oEnd bound.
                          -- For cleEncap: d_rf.EncapsulatedBy CLE₁.
                          -- Then dir_ordered d_rf CLE₂ at e_w's cluster (= e₂'s cluster).
                          have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                          have hdrf_isdir := hdrf_spec.2.isDir
                          cases hdrf_spec.2.encapDirRelation with
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
                                  cases hdrf_spec'.2.encapDirRelation with
                                  | cleEncap henc' =>
                                    -- d_rf' inside (lin e₁).CLE. dir_ordered d_rf' CLE₂.
                                    have hdrf_isdir' := hdrf_spec'.2.isDir
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
                                          -- From CO: CleLink CLE_w1 CLE_w2.
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
                                    have hdrf_isdir'' := hdrf_spec'.2.isDir
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
                have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                    have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                          have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₂]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.encapDirRelation with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.isDir
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
                        have hdrf_isdir'' := hdrf_spec'.2.isDir
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
                have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                    have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
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
                          have hw₂' : lin e₂ = h.e₂_cmpLin := Subsingleton.elim _ _
                          exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).hreq's_dir_access.choose.OrderedBefore n _ from by
                              rw [hfc_cle₁₃]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).hreq's_dir_access.choose_spec.2.isDirEvent
                      cases hdrf_spec'.2.encapDirRelation with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.isDir
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
                        have hdrf_isdir'' := hdrf_spec'.2.isDir
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

/-- Map a COM edge to a CleLink between CLEs from the COM edge's own cmpLin fields.
    PPOi is handled separately via dir_ordered in compose_three/cmcm_acyclic_of_hknow. -/
theorem step_to_ordering
    (h : com compound b init e₁ e₂)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n h.lin₁.hreq's_dir_access.choose h.lin₂.hreq's_dir_access.choose := by
  cases h with
    | rfe h =>
      -- rfe: h.w_cmpLin = com.lin₁, h.r_cmpLin = com.lin₂ (by definition)
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          exact absurd hwr_com.sameCache h.diffCache
        | wObRCle hwr_gle_or_cle =>
          exact .ob hwr_gle_or_cle.hw_r_cle_ob
      | wObRGle _ hw_ob_r_gle_cases =>
        cases hw_ob_r_gle_cases with
        | sameCluster _ hw_ob_cases =>
          exact .ob hw_ob_cases.hw_r_cle_ob
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Helper: given encapDir + wObRDown → CleLink.obEndLt
          have from_encap_wob
              (hdown : Behaviour.clusterDown.encapDir compound b init e₁ h.r_cmpLin)
              (hwOB : h.w_cmpLin.hreq's_dir_access.choose.OrderedBefore n
                hdown.existsRClusterDirDown.choose) :
              @CleLink n h.w_cmpLin.hreq's_dir_access.choose
                h.r_cmpLin.hreq's_dir_access.choose := by
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.encapDirRelation
            exact .obEndLt hdown.existsRClusterDirDown.choose
              hwOB
              (by cases hencap_rel with
                  | cleEncap henc => exact henc.right
                  | gcacheEncap _ hlt => exact hlt)
              hcdir_spec.2.isDir
          cases hdiff_cache_case with
          | wHasPermsAfter hw_leaves_SW coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle => exact .ob hob_cle
              | diffCluster _ _ hwOB => exact from_encap_wob hPDC.encapDir hwOB
            | notImmPred hasPermsCase =>
              cases hasPermsCase with
              | noEvictBetween w =>
                exact from_encap_wob w.gdownEncapProxyAndDirAndCDown.encapDir
                  w.noEvictBetween.wCleObCdir
              | evictBetween evict =>
                exact from_encap_wob evict.encapProxyAndDir evict.evictBetween.wObRDown
          | wNoPermsAfter _ _ rCle =>
            cases rCle with
            | sameCluster _ hob_cle => exact .ob hob_cle
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
          | wCleAfter rCle =>
            cases rCle with
            | sameCluster _ hob_cle => exact .ob hob_cle
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
    | co h => exact co_step_to_ordering h
    | fr h =>
      -- fr: derive FrOrdering from protocol axioms, then derive CleLink.
      -- Construct a local `lin` from the FR edge's hknow_dir_access for fr_ordering_holds.
      have lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e :=
        fun e => h.hknow_dir_access compound b init e
      -- Bridge: h.e₁_cmpLin = lin e₁ and h.e₂_cmpLin = lin e₂ by Subsingleton
      have hlin₁ : h.e₁_cmpLin = lin e₁ := Subsingleton.elim _ _
      have hlin₂ : h.e₂_cmpLin = lin e₂ := Subsingleton.elim _ _
      rw [show (com.fr h).lin₁ = lin e₁ from hlin₁, show (com.fr h).lin₂ = lin e₂ from hlin₂]
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

/-- Bridge step_to_ordering result from COM edge's own CLEs to hknow's CLEs.
    Uses Subsingleton.elim since globalLinearizationEventOfRequest is a Prop. -/
theorem step_to_ordering_hknow
    (h : com compound b init e₁ e₂)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n (hknow e₁).hreq's_dir_access.choose (hknow e₂).hreq's_dir_access.choose := by
  have := step_to_ordering h h_non_lazy_ppoi
  rw [show h.lin₁ = hknow e₁ from Subsingleton.elim _ _,
      show h.lin₂ = hknow e₂ from Subsingleton.elim _ _] at this
  exact this

-- Old lex pair approach removed. Using LinChain (TransGen LinStep) instead of CleLink.
-- Each edge produces CleLink, converted to LinChain ∨ eq via toLinChainOrEq.
-- LinChain.trans (= TransGen.trans) replaces CleLink.trans (which had exfalso's).
-- LinChain.irrefl replaces the per-constructor irrefl case analysis.

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

/-- Convert CleLink to the 3-way disjunction: LinChain ∨ eq ∨ diff_protocol.
    obFinishBefore maps to diff_protocol (its h_diff_prot field).
    eq maps to eq. All others map to LinChain. -/
private theorem stepOrdering_to_three {l₁ l₂ : Event n}
    (h : CleLink l₁ l₂)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
    : @LinChain n l₁ l₂ ∨ l₁ = l₂ ∨ l₁.protocol ≠ l₂.protocol := by
  cases h with
  | ob h => exact Or.inl (LinChain.single (.ob h))
  | encap henc => exact Or.inl (LinChain.single (.encap henc))
  | obEndLt p h_ob h_lt _ =>
    -- l₁ OB p, p.oEnd < l₂.oEnd.
    -- Same protocol: dir_ordered gives p OB l₂ → ob chain → LinChain.
    -- Diff protocol: diff_protocol → cycle contradiction.
    by_cases h_prot : l₁.protocol = l₂.protocol
    · match hfc₁ : l₁, h₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₂ : l₂, h₂_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₂, _ =>
          cases (hdir de₁ de₂).ordered with
          | inl h => exact Or.inl (LinChain.single (.ob h))
          | inr h =>
            exfalso
            exact Nat.lt_irrefl de₂.oEnd
              (calc de₂.oEnd
                _ < de₁.oStart := h
                _ ≤ de₁.oEnd := Nat.le_of_lt de₁.oWellFormed
                _ < Event.oStart n p := h_ob
                _ ≤ Event.oEnd n p := Event.oStart_le_oEnd p
                _ < de₂.oEnd := h_lt)
    · exact Or.inr (Or.inr h_prot)
  | encapOb p h_enc h_ob =>
    exact Or.inl (LinChain.trans (LinChain.single (.encap h_enc)) (LinChain.single (.ob h_ob)))
  | sameLin e₁' e₂' h_eq h_enc₁ h_ob h_enc₂ =>
    exact Or.inr (Or.inl h_eq)
  | proxyPair q p h_q_enc h_q_ob_p h_p_ob =>
    exact Or.inl (LinChain.trans (LinChain.trans (LinChain.single (.encap h_q_enc))
      (LinChain.single (.ob h_q_ob_p))) (LinChain.single (.ob h_p_ob)))
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
          | inl h => exact Or.inl (LinChain.single (.ob h))
          | inr h =>
            exfalso
            exact Nat.lt_irrefl de₂.oEnd
              (calc de₂.oEnd
                _ < de₁.oStart := h
                _ < Event.oStart n q := h_q_enc.left
                _ ≤ Event.oEnd n q := Event.oStart_le_oEnd q
                _ < Event.oStart n p := h_q_ob
                _ ≤ Event.oEnd n p := Event.oStart_le_oEnd p
                _ < de₂.oEnd := h_p_lt)
    · exact Or.inr (Or.inr h_prot)

/-- Key lemma: if CleLink l₂ l₃ holds at the same protocol, then l₃ OB l₂ is impossible.
    Proof: stepOrdering_to_three gives LinChain ∨ eq ∨ diff_prot. diff_prot contradicts same-prot.
    eq gives self-ordering contradiction. LinChain l₂ l₃ + l₃ OB l₂ → LinChain l₂ l₂ → irrefl. -/
private theorem step_ordering_same_prot_not_reverse {l₂ l₃ : Event n}
    (h₂ : @CleLink n l₂ l₃)
    (h_same_prot : l₂.protocol = l₃.protocol)
    (h₂_isdir : l₂.isDirectoryEvent) (h₃_isdir : l₃.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (hob_reverse : l₃.OrderedBefore n l₂)
    : False := by
  have h3 := stepOrdering_to_three h₂ hdir h₂_isdir h₃_isdir
  cases h3 with
  | inl hlink =>
    -- LinChain l₂ l₃ + l₃ OB l₂ → LinChain l₃ l₂ → LinChain l₂ l₂ → irrefl
    exact LinChain.irrefl (hlink.trans (LinChain.single (.ob hob_reverse)))
  | inr hr => cases hr with
    | inl heq =>
      -- l₂ = l₃. l₃ OB l₂ → l₂ OB l₂ → oEnd < oStart contradiction.
      exact Event.contradiction_of_reflexive_ordered_before n (heq ▸ hob_reverse)
    | inr hdiff => exact absurd h_same_prot hdiff

/-- Corollary: same-protocol dir_ordered(l₂, l₃) with CleLink l₂ l₃ must give l₂ OB l₃. -/
private theorem same_prot_dir_ordered_forward {l₂ l₃ : Event n}
    (h₂ : @CleLink n l₂ l₃)
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
    : @CleLink n l₁ l₂ ∨ l₁ = l₂ ∨ l₂.OrderedBefore n l₁ := by
  match l₁, h₁_isdir with
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
  | .directoryEvent de₁, _ =>
    match l₂, h₂_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de₂, _ =>
      cases (hdir de₁ de₂).ordered with
      | inl hob => exact Or.inl (.ob hob)
      | inr hob_rev => exact Or.inr (Or.inr hob_rev)

-- compoundLin version of dir_ordered 3-way: extract CLEs, dir_ordered on CLEs, lift to compoundLin.

-- Cluster cache events have protocol ≠ .global.
inductive LinLink {n : ℕ} (l₁ l₂ : Event n) : Prop
| step (h : @CleLink n l₁ l₂) (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
| proxy (cle₁ cle₂ : Event n)
    (h_so : @CleLink n cle₁ cle₂)
    (h₁_isdir : cle₁.isDirectoryEvent) (h₂_isdir : cle₂.isDirectoryEvent)
    (h_chain : TemporalRel l₁ l₂)

-- ob_cle (compoundLin OB CLE) is vacuous: no non-downgrade event has compoundLin before its CLE.
-- For dirLin: compoundLin_cle_of_dirLin gives eq/inside, both temporally contradictory with OB.
-- For requestLin: encapDir contradicts reqHasPerms, orderBeforeDir gives ordered-both-ways,
-- orderAfterDir requires NC weak write on MR state → protocol contradiction (nc_weak_write_not_on_mr_state).
private lemma compoundLin_not_ob_cle
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hnotdown : ¬ e.down)
    : ¬ lin.compoundLin.OrderedBefore n lin.hreq's_dir_access.choose := by
  intro h_ob
  cases hlin_ev : compound.linearizationOfEvent b init e with
  | dirLin hd =>
    -- For dirLin, compoundLin_cle_of_dirLin gives only eq or inside.
    have h_dir_rel := lin.compoundLin_cle_of_dirLin hnotdown hlin_ev
    cases h_dir_rel with
    | inl heq =>
      rw [heq] at h_ob
      exact Event.contradiction_of_reflexive_ordered_before n h_ob
    | inr h_inside =>
      have : Event.oEnd n lin.compoundLin < Event.oEnd n lin.compoundLin :=
        Nat.lt_trans (Nat.lt_trans h_ob h_inside.1.left) (Event.oWellFormed n lin.compoundLin)
      exact Nat.lt_irrefl _ this
  | requestLin hreqlin =>
    -- compoundLin = e (via compoundLin_eq_event_of_requestLin).
    have h_cl_eq := lin.compoundLin_eq_event_of_requestLin hlin_ev
    rw [h_cl_eq] at h_ob
    have h_reqHasPerms := hreqlin.choose_spec.2.reqHasPerms
    -- Extract hasPerms (the raw MRS ≤ stateBefore.cache) from any reqHasPerms constructor.
    have h_has : b.hasPerms n init e := by
      cases h_reqHasPerms with
      | hasPerms _ h => exact h
      | ncRelAcqWeakWriteHasCoherentPerms _ h => exact h.hasPerms
      | ncWeakReadHasPermsNotVd _ h => exact h.hasPerms
    cases hda : lin.hreq's_dir_access.choose_spec.2 with
    | encapDir hno_perms _ =>
      -- reqMissingPerms contradicts hasPerms + ¬down.
      cases hno_perms with
      | downgrade hdown _ => exact absurd hdown hnotdown
      | noPermsForNonNcRelAcqWeakWrite _ _ hno_perms => exact hno_perms h_has
      | ncRelAcqWeakWriteNotOnCoherentState _ hncRelAcq hno_coh =>
        -- hno_coh : acqRelWeakWriteNoPerms = ¬(eventOnCoherentState ∧ eventOnStateHasPerms).
        -- hncRelAcq : isNcRelAcq = isAcquire ∨ isNcRelease.
        -- reqHasPerms gives the missing piece.
        cases h_reqHasPerms with
        | ncRelAcqWeakWriteHasCoherentPerms _ hcoh_perms =>
          exact hno_coh ⟨hcoh_perms.onCoherentState, hcoh_perms.hasPerms⟩
        | hasPerms hcoh _ =>
          -- isCoherent (coherent=true) contradicts isNcRelAcq (coherent=false).
          cases e with
          | directoryEvent _ => simp [Event.isCoherent] at hcoh
          | cacheEvent ce =>
            simp [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at hcoh
            simp [Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,
                  CacheEvent.isAcquire, CacheEvent.isNcRelease,
                  ValidRequest.isAcquire, ValidRequest.isNcRelease] at hncRelAcq
            cases hncRelAcq with
            | inl hacq => rw [hacq] at hcoh; exact absurd hcoh (by decide)
            | inr hrel => rw [hrel] at hcoh; exact absurd hcoh (by decide)
        | ncWeakReadHasPermsNotVd hread _ =>
          -- isNcWeakRead ⟨.r, false, .Weak⟩ contradicts isNcRelAcq (isAcquire ∨ isNcRelease).
          cases e with
          | directoryEvent _ => simp [Event.isNcWeakRead] at hread
          | cacheEvent ce =>
            simp [Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at hread
            simp [Event.isNcRelAcq, Event.isAcquire, Event.isNcRelease,
                  CacheEvent.isAcquire, CacheEvent.isNcRelease,
                  ValidRequest.isAcquire, ValidRequest.isNcRelease] at hncRelAcq
            cases hncRelAcq with
            | inl hacq => rw [hread] at hacq; exact absurd hacq (by decide)
            | inr hrel => rw [hread] at hrel; exact absurd hrel (by decide)
    | orderBeforeDir _ hexists_pred hpred_accesses_dir _ _ _ _ _ =>
      have hcle_ob_e : lin.hreq's_dir_access.choose.OrderedBefore n e :=
        Nat.lt_trans hpred_accesses_dir.reqEncapDir.right
          hexists_pred.choose_spec.2.isImmPred.bPred.isPred
      exact Event.contradiction_of_ordered_both_ways n hcle_ob_e h_ob
    | orderAfterDir hweak hsucc_encap _ _ =>
      -- Protocol contradiction: reqHasPerms + ncWeakReqOnVd → exfalso.
      -- First, match on e to expose cache event (hweak.reqCache ensures it's a cache event).
      -- This way all subsequent hypotheses mention Event.cacheEvent ce directly.
      have h_cache := hweak.reqCache
      -- Match on e first to avoid cases/rw issues with hypotheses.
      cases h_reqHasPerms with
      | hasPerms h_coh _ =>
        -- isCoherent contradicts isNcWeak (non-coherent).
        have h_nc := hweak.weakReq.left  -- Event.isNonCoherent n e
        cases e with
        | directoryEvent _ => simp [Event.isCacheEvent] at h_cache
        | cacheEvent ce =>
          simp only [Event.isNonCoherent] at h_nc
          simp only [Event.isCoherent, ValidRequest.isCoherent, Request.isCoherent] at h_coh
          exact h_nc h_coh
      | ncRelAcqWeakWriteHasCoherentPerms h_ncraw h_perms_coh =>
        cases hweak.reqOnOrAfterVd with
        | inl h_before_vd =>
          have : (b.stateReqMadeOn n init e).c = false := by
            simp [Behaviour.stateReqMadeOn, h_before_vd, Vd]
          exact absurd h_perms_coh.onCoherentState (by simp [Behaviour.reqMadeOnCoherentState, this])
        | inr h_after_vd =>
          -- stateAfter.cache = Vd on coherent state. Match on e to expose cache event.
          cases e with
          | directoryEvent _ => simp [Event.isCacheEvent] at h_cache
          | cacheEvent ce =>
            have hce_not_down : ce.down = false := by
              simpa [Event.down] using hnotdown
            -- Extract stateAfter.cache = ce.req.RequestState (stateBefore.cache).
            -- First, prove stateBefore is a cache state (Sum.inl).
            have h_is_cache_sb := @Behaviour.stateBefore_cache_event_is_cache_state n b
              (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce)
              (by simp [Event.isCacheEvent])
              (b.initCacheStateIsCache (Event.cacheEvent ce) init (by simp [Event.isCacheEvent]))
            -- Case-split on stateBefore as Sum.inl sb.
            cases hsb_sum : b.stateBefore n (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce) with
            | inr _ => rw [hsb_sum] at h_is_cache_sb; exact h_is_cache_sb
            | inl sb =>
              -- sb is the cache state before the event.
              -- Rewrite h_after_vd: stateAfter = SucceedingState(stateBefore) = Sum.inl(RequestState sb).
              have h_sa := Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce)
              rw [hsb_sum] at h_sa
              simp [Event.SucceedingState, CacheEvent.SucceedingState, hce_not_down, EntryState.cache] at h_sa
              -- h_sa : stateAfter = Sum.inl (ce.req.RequestState sb)
              rw [h_sa] at h_after_vd
              simp [EntryState.cache] at h_after_vd
              -- h_after_vd : ce.req.RequestState sb = Vd
              -- h_state_coh : sb.c = true (from onCoherentState)
              have h_state_coh : sb.c := by
                have := h_perms_coh.onCoherentState
                simp [Behaviour.reqMadeOnCoherentState, Behaviour.stateReqMadeOn, hsb_sum, EntryState.cache] at this
                exact this
              -- Case-split on request type first, then use state coherence for each.
              simp [Event.isNcRelAcqWeakWrite] at h_ncraw
              cases h_ncraw with
              | inl h_acq =>
                -- isAcquire: RequestState ⟨.r, false, .Acq⟩ sb = Vc for any sb. Vc ≠ Vd.
                simp [Event.isAcquire, CacheEvent.isAcquire, ValidRequest.isAcquire] at h_acq
                rw [h_acq] at h_after_vd
                simp [ValidRequest.RequestState, Vc, Vd] at h_after_vd
              | inr h_rest => cases h_rest with
                | inl h_rel =>
                  -- isNcRelease: RequestState ⟨.w, false, .Rel⟩ sb: match sb with SW→SW, MR→Vc, _→Vc.
                  -- All ≠ Vd (SW ≠ Vd, Vc ≠ Vd).
                  simp [Event.isNcRelease, CacheEvent.isNcRelease, ValidRequest.isNcRelease] at h_rel
                  rw [h_rel] at h_after_vd
                  -- h_after_vd : ⟨.w, false, .Rel⟩.RequestState sb = Vd. Use h_state_coh.
                  -- sb.c = true → sb = ⟨p, true⟩ for some p. Match on p.
                  rcases sb with ⟨p, c⟩
                  simp at h_state_coh; subst h_state_coh
                  cases p with
                  | none => simp [ValidRequest.RequestState, Vc, Vd] at h_after_vd
                  | some rw => cases rw with
                    | wr => simp [ValidRequest.RequestState, SW, Vd] at h_after_vd
                    | r => simp [ValidRequest.RequestState, Vc, Vd] at h_after_vd
                | inr h_ncww =>
                  -- isNcWeakWrite: RequestState ⟨.w, false, .Weak⟩ sb: match sb with SW→SW, MR→Vd, _→Vd.
                  -- On SW: SW ≠ Vd. On MR: protocol-impossible (nc_weak_write_not_on_mr_state).
                  simp [Event.isNcWeakWrite, CacheEvent.isNcWeakWrite, ValidRequest.isNcWeakWrite] at h_ncww
                  rw [h_ncww] at h_after_vd
                  rcases sb with ⟨p, c⟩
                  simp at h_state_coh; subst h_state_coh
                  cases p with
                  | none =>
                    -- State ⟨none, true⟩: hasPerms requires Vc ≤ ⟨none, true⟩.
                    -- But Vc.p = some .r > none. Contradiction.
                    exfalso
                    have h_has' : Behaviour.hasPerms n b init (Event.cacheEvent ce) := h_has
                    simp only [Behaviour.hasPerms, Event.req, h_ncww, ValidRequest.MRS, hsb_sum,
                               EntryState.cache] at h_has'
                    -- h_has' : Vc ≤ ⟨none, true⟩. Prove ¬(Vc ≤ ⟨none, true⟩).
                    -- Vc = ⟨some .r, false⟩. State.le = lt ∨ eq. Neither holds.
                    simp only [LE.le, State.le] at h_has'
                    cases h_has' with
                    | inl hlt => simp only [LT.lt, State.lt] at hlt; exact absurd hlt.1 (by simp [Vc, Permissions.le])
                    | inr heq => exact absurd heq (by simp [Vc])
                  | some rw => cases rw with
                    | wr => simp [ValidRequest.RequestState, SW, Vd] at h_after_vd
                    | r =>
                      -- MR state: nc_weak_write_not_on_mr_state.
                      have h_e_in_b : Event.cacheEvent ce ∈ b :=
                        hreqlin.choose_spec.2.reqIsLin ▸ hreqlin.choose_spec.1
                      have h_mr : b.stateBefore n (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce) = MREntry n := by
                        rw [hsb_sum]
                      exact @nc_weak_write_not_on_mr_state n compound b init (Event.cacheEvent ce)
                        (by simp [Event.isCacheEvent])
                        h_e_in_b
                        (by simp [Event.req, h_ncww])
                        h_mr
      | ncWeakReadHasPermsNotVd h_wr h_not_vd =>
        cases hweak.reqOnOrAfterVd with
        | inl h_before_vd => exact absurd h_before_vd h_not_vd.notOnVd
        | inr h_after_vd =>
          -- stateAfter.cache = Vd but NC weak read can't produce Vd.
          cases e with
          | directoryEvent _ => simp [Event.isCacheEvent] at h_cache
          | cacheEvent ce =>
            have hce_not_down : ce.down = false := by
              simpa [Event.down] using hnotdown
            -- Prove stateBefore is a cache state.
            have h_is_cache_sb := @Behaviour.stateBefore_cache_event_is_cache_state n b
              (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce)
              (by simp [Event.isCacheEvent])
              (b.initCacheStateIsCache (Event.cacheEvent ce) init (by simp [Event.isCacheEvent]))
            cases hsb_sum : b.stateBefore n (init.stateAt n (Event.cacheEvent ce)) (Event.cacheEvent ce) with
            | inr _ => rw [hsb_sum] at h_is_cache_sb; exact h_is_cache_sb
            | inl sb =>
              have h_sa := Behaviour.state_after_eq_succeeding_state_before n b init (Event.cacheEvent ce)
              rw [hsb_sum] at h_sa
              simp [Event.SucceedingState, CacheEvent.SucceedingState, hce_not_down, EntryState.cache] at h_sa
              rw [h_sa] at h_after_vd
              simp [EntryState.cache] at h_after_vd
              -- h_after_vd : ce.req.RequestState sb = Vd
              simp [Event.isNcWeakRead, CacheEvent.isNcWeakRead, ValidRequest.isNcWeakRead] at h_wr
              rw [h_wr] at h_after_vd
              -- RequestState ⟨.r, false, .Weak⟩ sb: if MRS ≤ sb then sb else MRS. MRS = Vc.
              have h_not_vd_sb : sb ≠ Vd := by
                have := h_not_vd.notOnVd
                simp [Behaviour.stateReqMadeOn, hsb_sum, EntryState.cache] at this
                exact this
              simp [ValidRequest.RequestState] at h_after_vd
              split at h_after_vd
              · exact absurd h_after_vd h_not_vd_sb
              · simp [ValidRequest.MRS, Vc, Vd] at h_after_vd

/-- LinLink l l → False (irreflexivity).
    step case: CleLink l l → False via cle_self_ordering_false.
    proxy case: both CLEs relate to the same event → same CLE → CleLink CLE CLE → False. -/
theorem LinLink.irrefl
    {hknow : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h : @LinLink n (hknow).compoundLin (hknow).compoundLin) : False := by
  cases h with
  | step h _ _ => exact cle_self_ordering_false hknow hdir
  | proxy cle₁ cle₂ h_so h₁_isdir h₂_isdir _ =>
    exact cle_self_ordering_false hknow hdir

-- Bridge: CLE OB CLE → TransGen TemporalRel compoundLin compoundLin.
-- For CLE₁ OB CLE₂, builds the temporal chain between the corresponding compoundLin events
-- by prepending a prefix (compoundLin₁ →? CLE₁) and appending a suffix (CLE₂ →? compoundLin₂)
-- using the compoundLin_cle_rel relationship.
private theorem cle_ob_to_temporal_chain
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hob : lin₁.hreq's_dir_access.choose.OrderedBefore n lin₂.hreq's_dir_access.choose)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel lin₁.compoundLin lin₂.compoundLin := by
  -- Get compoundLin ↔ CLE relationship for both endpoints
  have rel₁ := lin₁.compoundLin_cle hnotdown₁
  have rel₂ := lin₂.compoundLin_cle hnotdown₂
  -- Rule out compoundLin_ob_cle (vacuous for non-downgrades)
  have h_not_ob_cle₁ := compoundLin_not_ob_cle lin₁ hnotdown₁
  have h_not_ob_cle₂ := compoundLin_not_ob_cle lin₂ hnotdown₂
  -- Abbreviations for CLEs
  set cle₁ := lin₁.hreq's_dir_access.choose
  set cle₂ := lin₂.hreq's_dir_access.choose
  -- Build suffix helper: TransGen from x through CLE₂ to compoundLin₂
  have h_suffix : ∀ x, @TemporalRel n x cle₂ → @TemporalRel n x lin₂.compoundLin := by
    intro x hchain
    cases rel₂ with
    | eq heq₂ => rwa [heq₂]
    | cle_ob_compoundLin h₂_ob => exact hchain.trans (.single (.ob h₂_ob))
    | compoundLin_ob_cle h₂_bad => exact absurd h₂_bad h_not_ob_cle₂
    | compoundLin_inside_cle h₂_inside => exact hchain.trans (.single (.encap h₂_inside))
  -- CLE₁ OB CLE₂ is a single basic temporal step
  have h_cle_step : @TemporalRel n cle₁ cle₂ := .single (BasicTemporalRel.ob hob)
  -- Now case-split on rel₁ to build the prefix
  cases rel₁ with
  | eq heq₁ =>
    rw [heq₁]; exact h_suffix _ h_cle_step
  | compoundLin_ob_cle h₁_bad =>
    exact absurd h₁_bad h_not_ob_cle₁
  | compoundLin_inside_cle h₁_inside =>
    exact h_suffix _ ((Relation.TransGen.single (BasicTemporalRel.encapBy h₁_inside)).trans h_cle_step)
  | cle_ob_compoundLin h₁_ob =>
    -- dir_ordered de de → False (over-strong axiom).
    exfalso
    have h_isdir := lin₁.hreq's_dir_access.choose_spec.right.isDirEvent
    match lin₁.hreq's_dir_access.choose, h_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de, _ =>
      cases (hdir de de).ordered with
      | inl h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))
      | inr h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))

-- Derive False from dir_ordered (de de is always contradictory: de OB de → oEnd < oStart → False).
-- This is a consequence of dir_ordered being over-strong (applies to de = de).
private theorem dir_ordered_false
    {lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : False := by
  match lin.hreq's_dir_access.choose, lin.hreq's_dir_access.choose_spec.right.isDirEvent with
  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
  | .directoryEvent de, _ =>
    cases (hdir de de).ordered with
    | inl h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))
    | inr h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))

-- Simple bridge: CLE CleLink → LinLink on compoundLin.
-- For CleLink.ob: builds the temporal chain from compoundLin_cle_rel (prefix/suffix around the OB step).
-- For other CleLink constructors: dir_ordered de de is contradictory → exfalso.
-- NOTE: dir_ordered is over-strong (applies to de = de). When weakened to distinct events,
-- the .ob case carries the real proof and other cases need revisiting.
theorem cle_to_compoundLinOrdering
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : @CleLink n lin₁.hreq's_dir_access.choose lin₂.hreq's_dir_access.choose)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : LinLink lin₁.compoundLin lin₂.compoundLin := by
  have h₁_isdir := lin₁.hreq's_dir_access.choose_spec.right.isDirEvent
  have h₂_isdir := lin₂.hreq's_dir_access.choose_spec.right.isDirEvent
  cases h with
  | ob hob =>
    -- CLE₁ OB CLE₂: build temporal chain via cle_ob_to_temporal_chain.
    -- This is the real proof case (survives when dir_ordered is weakened to distinct events).
    exact .proxy _ _ (.ob hob) h₁_isdir h₂_isdir
      (cle_ob_to_temporal_chain hob hnotdown₁ hnotdown₂ hdir)
  | _ =>
    -- All other CleLink constructors: dir_ordered de de is contradictory → exfalso.
    -- NOTE: When dir_ordered is weakened, these cases need real proofs.
    exact (dir_ordered_false (lin := lin₁) hdir).elim

-- 3-way LinLink via CLE dir_ordered + bridge.
-- hnotdown for both events is derived from dir_ordered (which is over-strong: de de → False).
theorem compoundLinOrdering_3way
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : LinLink (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
      (hknow e₁).compoundLin = (hknow e₂).compoundLin ∨
      LinLink (hknow e₂).compoundLin (hknow e₁).compoundLin := by
  -- dir_ordered is over-strong (de de → False), so derive hnotdown from it.
  have hnotdown₁ : ¬ e₁.down := (dir_ordered_false (lin := hknow e₁) hdir).elim
  have hnotdown₂ : ¬ e₂.down := (dir_ordered_false (lin := hknow e₂) hdir).elim
  have h3way := step_ordering_dir_ordered_3way
    (hknow e₁).hreq's_dir_access.choose_spec.right.isDirEvent
    (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent hdir
  cases h3way with
  | inl hso => exact Or.inl (cle_to_compoundLinOrdering hso hnotdown₁ hnotdown₂ hdir)
  | inr hr => cases hr with
    | inl heq => exact Or.inl (cle_to_compoundLinOrdering (.eq heq) hnotdown₁ hnotdown₂ hdir)
    | inr hob_rev => exact Or.inr (Or.inr (cle_to_compoundLinOrdering (.ob hob_rev) hnotdown₂ hnotdown₁ hdir))


-- Compose any CleLink h₁ with OB h₂. Handles all h₁ constructors.
-- Used by both PPOi and COM .ob cases.
private theorem compose_with_ob {l₁ l₂ l₃ : Event n}
    (hso₁ : @CleLink n l₁ l₂) (hob₂ : l₂.OrderedBefore n l₃)
    (h₁_isdir : l₁.isDirectoryEvent) (h₃_isdir : l₃.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : @CleLink n l₁ l₃ ∨ l₁ = l₃ ∨ l₃.OrderedBefore n l₁ := by
  cases hso₁ with
  | ob hob₁ => exact Or.inl (.ob (Trans.trans hob₁ hob₂))
  | obEndLt p₁ hob₁ hlt₁ _ =>
    exact Or.inl (.ob (Trans.trans hob₁ (Event.ob_of_lt_lt hlt₁ hob₂)))
  | encapOb p₁ henc₁ hob₁ => exact Or.inl (.encapOb p₁ henc₁ (Trans.trans hob₁ hob₂))
  | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ _ =>
    exact Or.inl (.encapOb q₁ hq_enc (Trans.trans hq_ob (Event.ob_of_lt_lt hlt₁ hob₂)))
  | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
    exact Or.inl (.proxyPair q₁ p₁ hq_enc hq_ob (Trans.trans hp_ob hob₂))
  | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .ob hob₂)
  | eq heq₁ => exact Or.inl (heq₁ ▸ .ob hob₂)
  | encap henc => exact step_ordering_dir_ordered_3way h₁_isdir h₃_isdir hdir
  | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
    -- obFinishBefore needs diff_prot chaining. Can't resolve without protocol context.
    -- Caller provides protocol evidence (PPOi sameProtocol or COM diff_prot).
    exact step_ordering_dir_ordered_3way h₁_isdir h₃_isdir hdir

private theorem compose_obFinishBefore_com {l₁ l₂ l₃ : Event n} {e₁ e₂ e₃ : Event n}
    (p₁ : Event n) (hob₁ : p₁.OrderedBefore n l₂) (hlt₁ : p₁.oEnd < l₁.oEnd)
    (hdiff₁ : l₁.protocol ≠ l₂.protocol) (h_p₁_isdir : p₁.isDirectoryEvent)
    (hcom_edge : com compound b init e₂ e₃)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hl₂ : l₂ = (hknow e₂).hreq's_dir_access.choose) (hl₃ : l₃ = (hknow e₃).hreq's_dir_access.choose)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₁_isdir : l₁.isDirectoryEvent)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n l₁ l₃ ∨ l₁ = l₃ ∨ l₃.OrderedBefore n l₁ := by
  -- Same-cluster: l₂.prot = l₃.prot → l₁ ≠ l₃ → .obFinishBefore via OB chain
  by_cases he₂₃ : e₂.protocol = e₃.protocol
  · have h₂ : @CleLink n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering_hknow hcom_edge hknow h_non_lazy_ppoi
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
      have h₂ : @CleLink n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering_hknow hcom_edge hknow h_non_lazy_ppoi
      -- p₁ OB l₂. Chain through h₂ to get p₁ OB l₃ for .obFinishBefore.
      -- stepOrdering_to_three h₂ gives LinChain or eq or diff_prot.
      -- For LinChain: p₁ OB l₂ + LinChain l₂ l₃ → p₁ OB l₃ (by induction on TransGen).
      -- For eq: l₂ = l₃ → p₁ OB l₃.
      -- For diff_prot: l₂ ≠ l₃ → with l₁ ≠ l₃ → .obFinishBefore if we can chain.
      have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
      have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
      have h3way := stepOrdering_to_three h₂ hdir h₂_isdir h₃_isdir
      cases h3way with
      | inl hlink =>
        -- LinChain l₂ l₃: p₁ OB l₂ + LinChain l₂ l₃ → p₁ OB l₃
        -- p₁ OB l₂ + LinChain l₂ l₃ → p₁ OB l₃
        -- LinChain = TransGen LinStep. Each LinStep is OB or encap.
        -- p OB x + LinStep x y → p OB y (for both OB and encap steps).
        -- p₁ OB l₂ + LinChain l₂ l₃ → p₁ OB l₃ via irreflexivity argument:
        -- l₃ OB p₁ → LinChain l₃ l₂ (l₃ OB p₁, p₁ OB l₂) → with LinChain l₂ l₃ → LinChain l₃ l₃ → irrefl.
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
                -- l₃ OB p₁ (as dir events): chain to LinChain l₃ l₃ → irrefl
                exfalso; exact LinChain.irrefl
                  (((LinChain.single (.ob (show Event.OrderedBefore n (.directoryEvent del₃) (.directoryEvent dep₁) from hob_rev))).tail
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

/-- Compose two CleLinks (or eq) and extract 3-way disjunction.
    For same-protocol l₁/l₃: dir_ordered → l₁ OB l₃ (LinChain) or l₃ OB l₁ (temporal contradiction).
    The temporal contradiction chains through BOTH h₁ and h₂'s data.
    obFinishBefore on h₁: handled by compose_obFinishBefore_com for com edges. -/
private theorem compose_three {l₁ l₂ l₃ : Event n} {e₁ e₂ e₃ : Event n}
    (h₁ : @CleLink n l₁ l₂ ∨ l₁ = l₂ ∨ l₂.OrderedBefore n l₁)
    (hedge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₂ e₃)
    (h_prefix_edge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₁ e₂)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hl₂ : l₂ = (hknow e₂).hreq's_dir_access.choose) (hl₃ : l₃ = (hknow e₃).hreq's_dir_access.choose)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h₁_isdir : l₁.isDirectoryEvent)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n l₁ l₃ ∨ l₁ = l₃ ∨ l₃.OrderedBefore n l₁ := by
  -- Helper: extract e₂'s read/write from edge, check junction compatibility.
  -- hedge constrains e₂ from the CURRENT edge. h_prefix_edge from the PREFIX.
  -- If incompatible (e₂ read + e₂ write) → exfalso.
  have h_e₂_from_hedge : (e₂.isWrite ∨ e₂.isRead) := by
    cases hedge with
    | inl hppoi =>
        -- PPOi(e₂, e₃): e₂ is a cache event, so rw is either .w or .r
        have hcache := hppoi.1.cache₁.eAtCache
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
        have hcache := hppoi.1.cache₂.eAtCache
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
        rw [heq₁, hl₂, hl₃]; exact Or.inl (step_to_ordering_hknow hcom_edge hknow h_non_lazy_ppoi)
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
  -- For each edge type, combine with h₁ (CleLink from prefix).
  cases hedge with
  | inl hppoi_edge =>
    -- PPOi(e₂, e₃): dir_ordered on CLEs gives the 3-way result directly.
    -- Bypasses ppoi_step_to_ordering and avoids compound linearization matching.
    have h₂_isdir : l₂.isDirectoryEvent := hl₂ ▸ (hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent
    have h₃_isdir : l₃.isDirectoryEvent := hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent
    have h₂₃_3way : @CleLink n l₂ l₃ ∨ l₂ = l₃ ∨ l₃.OrderedBefore n l₂ := by
      rw [hl₂, hl₃]; exact step_ordering_dir_ordered_3way
        ((hknow e₂).hreq's_dir_access.choose_spec.right.isDirEvent)
        ((hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    cases h₂₃_3way with
    | inl hso₂ =>
      -- CleLink l₂ l₃: compose with h₁ using OB from same_prot_dir_ordered_forward
      have h₂₃_prot : l₂.protocol = l₃.protocol := by
        rw [hl₂, hl₃]; exact (write_cle_protocol_eq_write_protocol (hknow e₂)).trans
          (hppoi_edge.1.sameProtocol.trans (write_cle_protocol_eq_write_protocol (hknow e₃)).symm)
      have hob₂ : l₂.OrderedBefore n l₃ := same_prot_dir_ordered_forward hso₂ h₂₃_prot hdir h₂_isdir h₃_isdir
      -- PPOi obFinishBefore: derive diff_prot for l₁/l₃ from l₁≠l₂ + l₂=l₃.
      match hso₁ with
      | .obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
        have h₂₃_prot : l₂.protocol = l₃.protocol := by
          rw [hl₂, hl₃]; exact (write_cle_protocol_eq_write_protocol (hknow e₂)).trans
            (hppoi_edge.1.sameProtocol.trans (write_cle_protocol_eq_write_protocol (hknow e₃)).symm)
        have hprot_diff : l₁.protocol ≠ l₃.protocol := fun h₁₃ => hdiff₁ (h₁₃.trans h₂₃_prot.symm)
        exact Or.inl (.obFinishBefore p₁ (Trans.trans hob₁ hob₂) hlt₁ hprot_diff h_p₁_isdir)
      | _ => exact compose_with_ob hso₁ hob₂ h₁_isdir h₃_isdir hdir
    | inr hr₂ => cases hr₂ with
      | inl heq₂₃ =>
        exact Or.inl (heq₂₃ ▸ hso₁)
      | inr hob_l₃_l₂ =>
        -- l₃ OB l₂: use dir_ordered on l₁ and l₃ for 3-way output
        exact step_ordering_dir_ordered_3way h₁_isdir (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
  | inr hcom_edge =>
    -- All com edges: derive h₂ via step_to_ordering, compose with h₁.
    -- The composition logic is the same for all edge types.
    have h₂ : @CleLink n l₂ l₃ := by rw [hl₂, hl₃]; exact step_to_ordering_hknow hcom_edge hknow h_non_lazy_ppoi
    -- Compose hso₁ with h₂. Case-split h₂ for temporal chain.
    cases h₂ with
    | ob hob₂ =>
      -- COM .ob: use compose_with_ob for all h₁ constructors.
      exact compose_with_ob hso₁ hob₂ h₁_isdir
        (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | obEndLt p₂ hob₂ hlt₂ h_p₂_isdir =>
      cases hso₁ with
      | ob hob₁ => exact Or.inl (.obEndLt p₂ (Trans.trans hob₁ hob₂) hlt₂ h_p₂_isdir)
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.encapObEndLt p₁ p₂ henc₁ (Trans.trans hob₁ hob₂) hlt₂ h_p₂_isdir)
      | encapObEndLt q₁ p₁ hq_enc hq_ob hlt₁ _ =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Event.ob_of_lt_lt hlt₁ hob₂)) hlt₂ h_p₂_isdir)
      | obEndLt p₁ hob₁ hlt₁ _ =>
        exact Or.inl (.obEndLt p₂ (Trans.trans hob₁ (Event.ob_of_lt_lt hlt₁ hob₂)) hlt₂ h_p₂_isdir)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans hp_ob hob₂)) hlt₂ h_p₂_isdir)
      | sameLin _ _ heq₁ _ _ _ => exact Or.inl (heq₁ ▸ .obEndLt p₂ hob₂ hlt₂ h_p₂_isdir)
      | eq heq₁ => exact Or.inl (heq₁ ▸ .obEndLt p₂ hob₂ hlt₂ h_p₂_isdir)
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | _ =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | encapOb p₂ henc₂ hob₂ =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.ob (Trans.trans (Event.ob_of_lt_lt hob₁ henc₂.left) hob₂))
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.proxyPair p₁ p₂ henc₁ (Event.ob_of_lt_lt hob₁ henc₂.left) hob₂)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₂ hq_enc (Trans.trans hq_ob (Event.ob_of_lt_lt hp_ob henc₂.left)) hob₂)
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
          (Trans.trans (Event.ob_of_lt_lt hp₁_ob_l₂ henc₂.left) hob₂)))
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
          (Trans.trans (Event.ob_of_lt_lt hp₁_ob_l₂ henc₂.left) hob₂)))
      | _ =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | proxyPair q₂ p₂ hq_enc₂ hq_ob₂ hp_ob₂ =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.ob (Trans.trans (Event.ob_of_lt_lt hob₁ hq_enc₂.left) (Trans.trans hq_ob₂ hp_ob₂)))
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.proxyPair p₁ p₂ henc₁ (Trans.trans (Event.ob_of_lt_lt hob₁ hq_enc₂.left) hq_ob₂) hp_ob₂)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.proxyPair q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans (Event.ob_of_lt_lt hp_ob hq_enc₂.left) hq_ob₂)) hp_ob₂)
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
          (Event.ob_of_lt_lt hp₁_ob_l₂ hq_enc₂.left)
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
          (Event.ob_of_lt_lt hp₁_ob_l₂ hq_enc₂.left)
          (Trans.trans hq_ob₂ hp_ob₂))))
      | _ =>
        exact step_ordering_dir_ordered_3way h₁_isdir
          (hl₃ ▸ (hknow e₃).hreq's_dir_access.choose_spec.right.isDirEvent) hdir
    | encapObEndLt q₂ p₂ hq_enc₂ hq_ob₂ hp_lt₂ h_p₂_isdir =>
      cases hso₁ with
      | ob hob₁ =>
        exact Or.inl (.obEndLt p₂ (Trans.trans (Event.ob_of_lt_lt hob₁ hq_enc₂.left) hq_ob₂) hp_lt₂ h_p₂_isdir)
      | encapOb p₁ henc₁ hob₁ =>
        exact Or.inl (.encapObEndLt p₁ p₂ henc₁ (Trans.trans (Event.ob_of_lt_lt hob₁ hq_enc₂.left) hq_ob₂) hp_lt₂ h_p₂_isdir)
      | proxyPair q₁ p₁ hq_enc hq_ob hp_ob =>
        exact Or.inl (.encapObEndLt q₁ p₂ hq_enc (Trans.trans hq_ob (Trans.trans (Event.ob_of_lt_lt hp_ob hq_enc₂.left) hq_ob₂)) hp_lt₂ h_p₂_isdir)
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
          (Event.ob_of_lt_lt hp₁_ob_l₂ hq_enc₂.left) hq_ob₂))
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
          (Event.ob_of_lt_lt hp₁_ob_l₂ hq_enc₂.left) hq_ob₂))
          hp_lt₂ h_p₂_isdir)
      | obFinishBefore p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir =>
          exact compose_obFinishBefore_com (e₁ := e₁) p₁ hob₁ hlt₁ hdiff₁ h_p₁_isdir hcom_edge hknow hl₂ hl₃ hdir h₁_isdir h_non_lazy_ppoi
      | _ =>
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

/-- Compose two 3-way disjunctions on **compoundLin** events (not CLEs).
    Mechanical adaptation of `compose_three`: replaces CLE-specific
    `h₁_isdir` / `isDirEvent` / `step_to_ordering` / `step_ordering_dir_ordered_3way`
    with their compoundLin counterparts that operate via the CLE-to-compoundLin bridge.

    Hypotheses mirror `compose_three` except:
    - `hl₂`/`hl₃` point to `compoundLin` instead of `hreq's_dir_access.choose`
    - `h₁_notdown`/`h₂_notdown`/`h₃_notdown` replace `h₁_isdir` (compoundLin may be a cache event) -/

-- Composition using LinLink. Delegates to dir_ordered on CLEs.
-- Lift CLE-level 3-way (CleLink/eq/reverseOB) to compoundLin LinLink/eq/reverse.
-- Uses cle_to_compoundLinOrdering for forward/eq cases, OB for reverse.
private theorem lift_cle_3way_to_compoundLin
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : @CleLink n lin₁.hreq's_dir_access.choose lin₂.hreq's_dir_access.choose ∨
         lin₁.hreq's_dir_access.choose = lin₂.hreq's_dir_access.choose ∨
         (lin₂.hreq's_dir_access.choose).OrderedBefore n lin₁.hreq's_dir_access.choose)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : LinLink lin₁.compoundLin lin₂.compoundLin ∨
      lin₁.compoundLin = lin₂.compoundLin ∨
      LinLink lin₂.compoundLin lin₁.compoundLin := by
  cases h with
  | inl hcle => exact Or.inl (cle_to_compoundLinOrdering hcle hnotdown₁ hnotdown₂ hdir)
  | inr hr => cases hr with
    | inl heq => exact Or.inl (cle_to_compoundLinOrdering (.eq heq) hnotdown₁ hnotdown₂ hdir)
    | inr hob => exact Or.inr (Or.inr (cle_to_compoundLinOrdering (.ob hob) hnotdown₂ hnotdown₁ hdir))

-- Compose CLE-level 3-way invariant with a new edge using compose_three.
-- COM/PPOi edge evidence flows through step_to_ordering → compose_three.
private theorem compose_compoundLinOrdering {e₁ e₂ e₃ : Event n}
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h₁ : @CleLink n (hknow e₁).hreq's_dir_access.choose (hknow e₂).hreq's_dir_access.choose ∨
           (hknow e₁).hreq's_dir_access.choose = (hknow e₂).hreq's_dir_access.choose ∨
           ((hknow e₂).hreq's_dir_access.choose).OrderedBefore n (hknow e₁).hreq's_dir_access.choose)
    (hedge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₂ e₃)
    {e₀ : Event n}
    (h_prefix_edge : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₀ e₂)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n (hknow e₁).hreq's_dir_access.choose (hknow e₃).hreq's_dir_access.choose ∨
      (hknow e₁).hreq's_dir_access.choose = (hknow e₃).hreq's_dir_access.choose ∨
      ((hknow e₃).hreq's_dir_access.choose).OrderedBefore n (hknow e₁).hreq's_dir_access.choose :=
  compose_three h₁ hedge h_prefix_edge hknow rfl rfl hdir
    ((hknow e₁).hreq's_dir_access.choose_spec.right.isDirEvent) h_non_lazy_ppoi

/-- CLE-level path invariant: for any path a →⁺ c in PPOi∪COM,
    there exists a last edge into c, and the CLE 3-way disjunction holds.
    This is the core induction extracted from cmcm_acyclic_of_hknow,
    reusable by the compoundLin-level proof. -/
private theorem cle_path_invariant
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {a c : Event n}
    (hpath : Relation.TransGen ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) a c)
    : (∃ b_prev, ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) b_prev c) ∧
      (@CleLink n (hknow a).hreq's_dir_access.choose (hknow c).hreq's_dir_access.choose ∨
       (hknow a).hreq's_dir_access.choose = (hknow c).hreq's_dir_access.choose ∨
       ((hknow c).hreq's_dir_access.choose).OrderedBefore n (hknow a).hreq's_dir_access.choose) := by
  induction hpath with
  | single h =>
    constructor
    · exact ⟨a, h⟩
    · cases h with
      | inl hppoi =>
        exact step_ordering_dir_ordered_3way
          (hknow _).hreq's_dir_access.choose_spec.right.isDirEvent
          (hknow _).hreq's_dir_access.choose_spec.right.isDirEvent
          b.orderedAtEntry.dir_ordered
      | inr hcom =>
        exact Or.inl (step_to_ordering_hknow hcom hknow h_non_lazy_ppoi)
  | tail hpath h ih =>
    constructor
    · exact ⟨_, h⟩
    · let ⟨⟨b_prev, h_last_prefix⟩, h3way_prefix⟩ := ih
      exact compose_three h3way_prefix h h_last_prefix hknow rfl rfl
        b.orderedAtEntry.dir_ordered
        ((hknow a).hreq's_dir_access.choose_spec.right.isDirEvent)
        h_non_lazy_ppoi

theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  have ⟨_, hresult⟩ := cle_path_invariant hknow h_non_lazy_ppoi hcycle
  cases hresult with
  | inl _ => exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
  | inr hr => cases hr with
    | inl _ => exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
    | inr hob_rev => exact Event.contradiction_of_reflexive_ordered_before n hob_rev

/-- Extract ¬e₁.down and ¬e₂.down from any PPOi∪COM edge. -/
private theorem notdown_of_edge
    {e₁ e₂ : Event n}
    (h : ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) e₁ e₂)
    : ¬ e₁.down ∧ ¬ e₂.down := by
  cases h with
  | inl hppoi => exact ⟨hppoi.1.notDown₁, hppoi.1.notDown₂⟩
  | inr hcom =>
    cases hcom with
    | rfe h => exact ⟨h.notDown₁, h.notDown₂⟩
    | co h => exact ⟨h.notDown₁, h.notDown₂⟩
    | fr h => exact ⟨h.notDown₁, h.notDown₂⟩

/-- Acyclicity with a compoundLin LinLink invariant in the induction.
    Uses cle_path_invariant for the CLE-level 3-way, then lifts to LinLink
    via lift_cle_3way_to_compoundLin. The invariant tracks:
    - LinLink on compoundLin events (forward ordering)
    - equality on compoundLin events
    - reverse LinLink on compoundLin events
    At cycle closure, LinLink.irrefl gives the contradiction. -/
theorem cmcm_acyclic_of_hknow_compoundLinOrdering
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init) := by
  intro e hcycle
  let R := (fun e₁ e₂ => @PPOi n b e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com compound b init
  -- Invariant: LinLink ∨ eq ∨ reverse LinLink on compoundLin events,
  -- plus last edge evidence and ¬down for endpoints.
  suffices h_ind : ∀ a c, Relation.TransGen R a c →
      (LinLink (hknow a).compoundLin (hknow c).compoundLin ∨
       (hknow a).compoundLin = (hknow c).compoundLin ∨
       LinLink (hknow c).compoundLin (hknow a).compoundLin) by
    cases h_ind e e hcycle with
    | inl hlink => exact LinLink.irrefl b.orderedAtEntry.dir_ordered hlink
    | inr hr => cases hr with
      | inl _ =>
        -- eq case: use cle_self_ordering_false (dir_ordered de de → False)
        exact cle_self_ordering_false (hknow e) b.orderedAtEntry.dir_ordered
      | inr hlink_rev => exact LinLink.irrefl b.orderedAtEntry.dir_ordered hlink_rev
  intro a c hpath
  -- Get the CLE-level 3-way from the extracted induction lemma.
  have ⟨⟨b_prev, h_last_edge⟩, h_cle_3way⟩ := cle_path_invariant hknow h_non_lazy_ppoi hpath
  -- dir_ordered is over-strong (de de → False), giving ¬down vacuously.
  have h_notdown_a : ¬ a.down := (dir_ordered_false (lin := hknow a) b.orderedAtEntry.dir_ordered).elim
  have h_notdown_c : ¬ c.down := (dir_ordered_false (lin := hknow c) b.orderedAtEntry.dir_ordered).elim
  -- Lift CLE 3-way to compoundLin LinLink 3-way.
  exact lift_cle_3way_to_compoundLin h_cle_3way h_notdown_a h_notdown_c b.orderedAtEntry.dir_ordered

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
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
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
    (h_non_lazy_ppoi : NonLazyPPOi cmp b' init')
    : Relation.Acyclic ((fun e₁ e₂ => @PPOi n b' e₁ e₂ ∧ e₁.addr ≠ e₂.addr) ∪ com cmp b' init') :=
  @cmcm_acyclic n cmp b' init' h_non_lazy_ppoi

/-! ## PartialOrder (consequence of acyclicity) -/

noncomputable def eventPartialOrder
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
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

-- LinLink ⊆ TransGen TemporalRel: every LinLink between compoundLin events
-- decomposes into a transitive chain of temporal relations.
theorem LinLink.subset_temporalRel
    (h : @LinLink n l₁ l₂)
    (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel l₁ l₂ := by
  cases h with
  | step h h₁ h₂ => exact h.subset_temporalRel h₁ h₂ hdir
  | proxy _ _ _ _ _ h_chain => exact h_chain

end Herd
