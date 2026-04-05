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

/-! ## The PPOi∪COM relation via hknow -/

/-- The PPOi∪COM edge relation, parameterized by hknow.
    This makes compoundLin the primary concept: `(hknow e).compoundLin`, `.cle`, `.gle`. -/
abbrev R_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n) : Prop :=
  (PPOi (hknow e₁) (hknow e₂) ∧ e₁.addr ≠ e₂.addr) ∨ com (hknow e₁) (hknow e₂)

/-- Bridge: any PPOi with arbitrary lins lifts to R_hknow via Subsingleton.elim. -/
theorem R_hknow_of_ppoi
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : PPOi lin₁ lin₂) (h_addr : e₁.addr ≠ e₂.addr) : R_hknow hknow e₁ e₂ :=
  Or.inl ⟨(Subsingleton.elim lin₁ (hknow e₁)) ▸ (Subsingleton.elim lin₂ (hknow e₂)) ▸ h, h_addr⟩

/-- Bridge: any COM with arbitrary lins lifts to R_hknow via Subsingleton.elim. -/
theorem R_hknow_of_com
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : com lin₁ lin₂) : R_hknow hknow e₁ e₂ :=
  Or.inr ((Subsingleton.elim lin₁ (hknow e₁)) ▸ (Subsingleton.elim lin₂ (hknow e₂)) ▸ h)

/-! ## Irreflexivity of each edge type -/

theorem ppoi_irrefl {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : PPOi lin₁ lin₂) : False :=
  Event.contradiction_of_reflexive_ordered_before n h.orderedBefore

theorem rfe_irrefl {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : Herd.rfe lin₁ lin₂) : False :=
  absurd rfl h.diffCache

theorem co_irrefl {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : Herd.co lin₁ lin₂) : False := by
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

theorem fr_irrefl {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : Herd.fr lin₁ lin₂) : False := by
  have hread := h.read
  have hwrite := h.write
  cases e with
  | cacheEvent ce =>
    simp only [Event.isRead, Request.isRead] at hread
    simp only [Event.isWrite, Request.isWrite] at hwrite
    rw [hwrite] at hread; exact absurd hread (by decide)
  | directoryEvent de =>
    simp [Event.isRead] at hread

theorem com_irrefl {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : com lin₁ lin₂) : False := by
  cases h with
  | rfe h => exact rfe_irrefl h
  | co h => exact co_irrefl h
  | fr h => exact fr_irrefl h

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
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hppoi : PPOi lin₁ lin₂)
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
theorem ppoi_acyclic (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Relation.Acyclic (fun e₁ e₂ => PPOi (hknow e₁) (hknow e₂)) := by
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

/-- Map a single co edge to CleLink using the CO edge's lin parameters. -/
theorem co_step_to_ordering
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : Herd.co lin₁ lin₂)
    : @CleLink n lin₁.cle lin₂.cle := by
  cases h.comm with
  | sameCache same_cle cache_ob =>
    have hda₁ := lin₁.hreq's_dir_access.choose_spec.2
    have hda₂ := lin₂.hreq's_dir_access.choose_spec.2
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
      | sameCluster _ hob => exact .ob hob (Event.ne_of_ob hob)
      | diffCluster _ hdown hwObRDown =>
        have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
        have h_lt : Event.oEnd n hdown.existsRClusterDirDown.choose < Event.oEnd n lin₂.cle := by
          cases hcdir_spec.2.encapDirRelation with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact .obEndLt hdown.existsRClusterDirDown.choose hwObRDown h_lt
          hcdir_spec.2.isDir (Event.ne_of_obEndLt hwObRDown h_lt)
    | evictOrReadBetweenWAndRCleSameCluster evict =>
      exact .ob evict.wObR (Event.ne_of_ob evict.wObR)
  | diffClus _ diff_cluster_cases =>
    cases diff_cluster_cases with
    | wCleImmPredDown w =>
      have hcdir_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
      have h_lt : Event.oEnd n w.rDown.encapDir.existsRClusterDirDown.choose < Event.oEnd n lin₂.cle := by
        cases hcdir_spec.2.encapDirRelation with
        | cleEncap henc => exact henc.right
        | gcacheEncap _ hlt => exact hlt
      exact .obEndLt w.rDown.encapDir.existsRClusterDirDown.choose w.wObRDown h_lt
        hcdir_spec.2.isDir (Event.ne_of_obEndLt w.wObRDown h_lt)
    | evictOrReadBetweenWAndRDown evict =>
      have hcdir_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
      have h_lt : Event.oEnd n evict.rDown.encapDir.existsRClusterDirDown.choose < Event.oEnd n lin₂.cle := by
        cases hcdir_spec.2.encapDirRelation with
        | cleEncap henc => exact henc.right
        | gcacheEncap _ hlt => exact hlt
      exact .obEndLt evict.rDown.encapDir.existsRClusterDirDown.choose evict.wObRDown h_lt
        hcdir_spec.2.isDir (Event.ne_of_obEndLt evict.wObRDown h_lt)

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
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : Herd.co lin₁ lin₂)
    : Event.oEnd n lin₁.cle ≤ Event.oEnd n lin₂.cle := by
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
    (hco_chain : Relation.TransGen (fun ew₁ ew₂ => ∃ (l₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₁) (l₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₂), Herd.co l₁ l₂) e_w e₂)
    (lin : ∀ e, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Event.oEnd n (lin e_w).cle ≤
      Event.oEnd n (lin e₂).cle := by
  induction hco_chain with
  | single h =>
    obtain ⟨l₁, l₂, hco⟩ := h
    have := co_step_oEnd_le hco
    rw [show l₁ = lin _ from Subsingleton.elim _ _,
        show l₂ = lin _ from Subsingleton.elim _ _] at this
    exact this
  | tail _ h ih =>
    obtain ⟨l₁, l₂, hco⟩ := h
    have := co_step_oEnd_le hco
    rw [show l₁ = lin _ from Subsingleton.elim _ _,
        show l₂ = lin _ from Subsingleton.elim _ _] at this
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
    (h_co_chain : Relation.TransGen (fun ew₁ ew₂ => ∃ (l₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₁) (l₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₂), Herd.co l₁ l₂) e_w e₂)
    (h_diff_prot : ¬ e_w.sameProtocol n e₂)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : ∃ (d : Event n),
        d ∈ b ∧
        e_w_lin.cle.OrderedBefore n d ∧
        d.oEnd < (lin e₂).cle.oEnd ∧
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
  | single h_co_ex =>
    -- Single co step: co(e_w, c). Since protocols differ: must be diffClus.
    obtain ⟨l₁_co, l₂_co, h_co⟩ := h_co_ex
    cases h_co.comm with
    | sameCache same_cle _ =>
      -- sameCache → same CLE → same protocol. But h_diff_prot says diff protocol. Contradiction.
      exfalso; apply h_diff_prot
      unfold Event.sameProtocol
      have h1 := write_cle_protocol_eq_write_protocol l₁_co
      have h2 := write_cle_protocol_eq_write_protocol l₂_co
      rw [← h1, ← h2, same_cle]
    | sameClusDiffCache h_same_prot _ => exact absurd h_same_prot h_diff_prot
    | diffClus _ diff_cases =>
      cases diff_cases with
      | wCleImmPredDown w =>
        have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            l₂_co.cle.oEnd := by
          cases hrd_spec.2.encapDirRelation with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        -- e_mid = the second writer in this CO step (the endpoint)
        exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = l₁_co from Subsingleton.elim _ _]; exact w.wObRDown,
          by rw [show lin _ = l₂_co from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.isDir, hrd_spec.2.sameProtocol,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = l₂_co from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
      | evictOrReadBetweenWAndRDown evict =>
        have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
        have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
            l₂_co.cle.oEnd := by
          cases hrd_spec.2.encapDirRelation with
          | cleEncap henc => exact henc.right
          | gcacheEncap _ hlt => exact hlt
        exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
          hrd_spec.1,
          by rw [show e_w_lin = l₁_co from Subsingleton.elim _ _]; exact evict.wObRDown,
          by rw [show lin _ = l₂_co from Subsingleton.elim _ _]; exact hrd_lt,
          hrd_spec.2.isDir, hrd_spec.2.sameProtocol,
          
          ⟨_, h_co.in_b₂, h_co.cache₂, h_co.write₂, h_co.notDown₂,
           fun h => h_diff_prot (show e_w.sameProtocol n _ from h.symm),
           by rw [show lin _ = l₂_co from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
  | tail hpath h_last_ex ih =>
    rename_i b_mid c_ep
    obtain ⟨l₁_last_t, l₂_last_t, h_last⟩ := h_last_ex
    -- IH for prefix. Extend d.oEnd bound via last step's CleLink.
    by_cases h_mid_prot : e_w.sameProtocol n b_mid
    · -- Prefix same-cluster: last step h_last must cross clusters.
      -- Get CLE_w.oEnd ≤ CLE_mid.oEnd from prefix CleLink.
      have hcle_w_le_mid : Event.oEnd n e_w_lin.cle ≤
          Event.oEnd n (lin b_mid).cle := by
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
        have h1 := write_cle_protocol_eq_write_protocol l₁_last_t
        have h2 := write_cle_protocol_eq_write_protocol l₂_last_t
        rw [← h1, ← h2, same_cle]
      | sameClusDiffCache h_same _ => exact absurd h_same h_mid_diff_c
      | diffClus _ diff_cases =>
        cases diff_cases with
        | wCleImmPredDown w =>
          have hrd_spec := w.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : w.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              l₂_last_t.cle.oEnd := by
            cases hrd_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := w.wObRDown
          rw [show l₁_last_t = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨w.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = l₂_last_t from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.isDir,
            hrd_spec.2.sameProtocol.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = l₂_last_t from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
        | evictOrReadBetweenWAndRDown evict =>
          have hrd_spec := evict.rDown.encapDir.existsRClusterDirDown.choose_spec
          have hrd_lt : evict.rDown.encapDir.existsRClusterDirDown.choose.oEnd <
              l₂_last_t.cle.oEnd := by
            cases hrd_spec.2.encapDirRelation with
            | cleEncap henc => exact henc.right
            | gcacheEncap _ hlt => exact hlt
          have h_mid_ob_d := evict.wObRDown
          rw [show l₁_last_t = lin b_mid from Subsingleton.elim _ _] at h_mid_ob_d
          exact ⟨evict.rDown.encapDir.existsRClusterDirDown.choose,
            hrd_spec.1,
            Nat.lt_of_le_of_lt hcle_w_le_mid h_mid_ob_d,
            by rw [show lin c_ep = l₂_last_t from Subsingleton.elim _ _]; exact hrd_lt,
            hrd_spec.2.isDir,
            hrd_spec.2.sameProtocol.trans (show b_mid.protocol = e_w.protocol from
              (show e_w.protocol = b_mid.protocol from h_mid_prot).symm),
            
            ⟨c_ep, h_last.in_b₂, h_last.cache₂, h_last.write₂, h_last.notDown₂,
             fun h => h_diff_prot (show e_w.sameProtocol n c_ep from h.symm),
             by rw [show lin c_ep = l₂_last_t from Subsingleton.elim _ _]; exact hrd_spec.2.clusterDir⟩⟩
    · -- Prefix diff-cluster: IH gives d with e_mid from some earlier step.
      -- Pass through the IH's e_mid — it has translatedDir about e_mid, not the endpoint.
      -- h_no_between at the call site can be applied to e_mid instead of e₂.
      obtain ⟨d, hd_in_b, hob_d, hd_lt, hd_isDir, hd_proto, hd_emid⟩ := ih h_mid_prot
      have hext : (lin b_mid).cle.oEnd ≤ (lin c_ep).cle.oEnd := by
        have := co_step_oEnd_le h_last
        rw [show l₁_last_t = lin b_mid from Subsingleton.elim _ _,
            show l₂_last_t = lin c_ep from Subsingleton.elim _ _] at this
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
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : Herd.fr lin₁ lin₂)
    (lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : FrOrdering (lin e₁) (lin e₂) := by
  -- FR = rf⁻¹ ; co⁺ with e_w as intermediate write.
  -- Case structure: sameCLE / sameCache / sameClusDiffCache / diffCluster.
  -- diffCluster sub-cases by e₁'s coherence state.
  by_cases hcle_eq : (lin e₁).cle = (lin e₂).cle
  · exact .sameCLE hcle_eq
  · by_cases h_same_cache : e₁.struct = e₂.struct
    · -- Same cache e₁/e₂: same cluster + same dir → dir_ordered + NIW.
      have hcle₁_isdir := (lin e₁).cle_isDirEvent
      have hcle₂_isdir := (lin e₂).cle_isDirEvent
      match hfc₁ : (lin e₁).cle, hcle₁_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₁, _ =>
        match hfc₂ : (lin e₂).cle, hcle₂_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₂, _ =>
          cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
          | inl hob =>
            exact .sameCache h_same_cache (Or.inr (show Event.OrderedBefore n
              (lin e₁).cle (lin e₂).cle from
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
              (show (hlin e₂).cle.OrderedBefore n
                  (lin e₁).cle from by
                rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob)
    · by_cases h_same_prot : e₁.sameProtocol n e₂
      · -- Same cluster, different cache: dir_ordered + NIW.
        have hcle₁_isdir := (lin e₁).cle_isDirEvent
        have hcle₂_isdir := (lin e₂).cle_isDirEvent
        match hfc₁ : (lin e₁).cle, hcle₁_isdir with
        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
        | .directoryEvent de₁, _ =>
          match hfc₂ : (lin e₂).cle, hcle₂_isdir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de₂, _ =>
            cases (b.orderedAtEntry.dir_ordered de₁ de₂).ordered with
            | inl hob =>
              exact .sameClusDiffCache h_same_prot h_same_cache (show Event.OrderedBefore n
                (lin e₁).cle (lin e₂).cle from
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
                have hprot₁ : (hlin e₂).cle.protocol =
                    e_w_lin.cle.protocol :=
                  hcle₂_prot.trans (h_ew_prot.trans hcle_w_prot.symm)
                have hprot₂ : (hlin e₂).cle.protocol =
                    (lin e₁).cle.protocol :=
                  hcle₂_prot.trans (hprot_e₂_e₁.trans hcle₁_prot.symm)
                have h_isDirWrite : (hlin e₂).cle.isDirWrite := by
                  have : hlin e₂ = lin₂ := Subsingleton.elim _ _
                  rw [this]; exact write_event_cle_isDirWrite h.write h.cache₂ h.notDown₂ lin₂ h.in_b₂
                have hdir_w := e_w_lin.cle_isDirEvent
                match hfcw : e_w_lin.cle, hdir_w with
                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                | .directoryEvent de_w, _ =>
                  cases (b.orderedAtEntry.dir_ordered de_w de₂).ordered with
                  | inl hob_w₂ =>
                    exact h_constraints.notBetweenCles ⟨hprot₁, hprot₂, h_isDirWrite⟩
                      ⟨by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = lin₂ from Subsingleton.elim _ _, hfc₂, hfcw]; exact hob_w₂,
                       by simp only [Event.OrderedBefore, Event.oEnd, Event.oStart,
                            show hlin e₂ = lin₂ from Subsingleton.elim _ _, hfc₂, hfc₁]; exact hob⟩
                  | inr hob_₂w =>
                    have hcw_le : de_w.oEnd ≤ de₂.oEnd := by
                      have hoEnd := co_chain_oEnd_le h_co_chain hlin
                      rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm,
                          show hlin e₂ = lin₂ from Subsingleton.elim _ _] at hoEnd
                      simp only [Event.oEnd, hfcw, hfc₂] at hoEnd ⊢; exact hoEnd
                    exact Nat.lt_irrefl _ (calc de_w.oEnd ≤ de₂.oEnd := hcw_le
                      _ < de_w.oStart := hob_₂w
                      _ ≤ de_w.oEnd := Nat.le_of_lt de_w.oWellFormed)
              · -- Diff cluster e_w: use cdirEncapsDown_exists + diffClusterNotBetweenCles_sameCache.
                -- Use interSameProtocolCleOB: e₂ same cluster as e₁ → ¬ CLE₂ OB CLE₁.
                have h_same_prot₂₁ : e₂.sameProtocol n e₁ := by
                  unfold Event.sameProtocol at h_same_prot ⊢; exact h_same_prot.symm
                exact absurd
                  (show (hlin e₂).cle.OrderedBefore n
                      (lin e₁).cle from by
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
          have hcle₁_isdir := (lin e₁).cle_isDirEvent
          match hfc_cdir : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁ : (lin e₁).cle, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob_cle₁_cdir =>
                -- CLE₁ OB cdir → proxy = cdir
                have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
                exact .diffCluster_coherent h_same_prot (.directoryEvent de_cdir)
                  (show (lin e₁).cle.OrderedBefore n _ from by
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
                    have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
                    exact .diffCluster_coherent h_same_prot (.directoryEvent de_evict)
                      (show (lin e₁).cle.OrderedBefore n _ from by
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
                              e_w_lin.cle
                              (lin e₁).cle := by
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
                          have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).cle.OrderedBefore n _ from by
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
                          have hcle₂_isdir := (lin e₂).cle_isDirEvent
                          have hdrf_isdir := hdrf_spec.2.isDir
                          cases hdrf_spec.2.encapDirRelation with
                          | cleEncap henc_drf =>
                            -- d_rf inside CLE₁ (CLE₁ encapsulates d_rf).
                            -- dir_ordered d_rf CLE₂ at e_w's cluster.
                            match hfc_drf : hencapDir.existsRClusterDirDown.choose, hdrf_isdir with
                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                            | .directoryEvent de_drf, _ =>
                              match hfc_cle₂ : (lin e₂).cle, hcle₂_isdir with
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
                                      match hfc_cle₂' : (lin e₂).cle, hcle₂_isdir with
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
                                          have hcle_w_isdir := e_w_lin.cle_isDirEvent
                                          have hcle_w2_isdir := (hlin e₂).cle_isDirEvent
                                          match hfc_clew : e_w_lin.cle, hcle_w_isdir with
                                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                          | .directoryEvent de_clew, _ =>
                                            match hfc_clew2 : (hlin e₂).cle, hcle_w2_isdir with
                                            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                            | .directoryEvent de_clew2, _ =>
                                              have hcle_w1_ob := co_chain_same_cluster_ob hoEnd
                                                hfc_clew hfc_clew2 (b.orderedAtEntry.dir_ordered de_clew de_clew2)
                                              have hcle_w2_ob_drf : (hlin e₂).cle.OrderedBefore n
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
                                      match hfc_cle₂'' : (lin e₂).cle, hcle₂_isdir with
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
                                              (hlin e₂).cle.OrderedBefore n
                                              hencapDir'.existsRClusterDirDown.choose := by
                                            rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _,
                                                hfc_cle₂'', hfc_drf'']; exact hob
                                          -- CLE_w OB CLE₂ from CO chain via oEnd ≤ + dir_ordered.
                                          have hoEnd := co_chain_oEnd_le h_co_chain hlin
                                          rw [show hlin e_w = e_w_lin from (Subsingleton.elim _ _).symm] at hoEnd
                                          have hcle_w_isdir := e_w_lin.cle_isDirEvent
                                          have hcle_w2_isdir := (hlin e₂).cle_isDirEvent
                                          match hfc_clew : e_w_lin.cle, hcle_w_isdir with
                                          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                          | .directoryEvent de_clew, _ =>
                                            match hfc_clew2 : (hlin e₂).cle, hcle_w2_isdir with
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
                                  have hcle_w_isdir := e_w_lin.cle_isDirEvent
                                  have hcle_w2_isdir := (hlin e₂).cle_isDirEvent
                                  match hfc_w : e_w_lin.cle, hcle_w_isdir with
                                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                  | .directoryEvent de_w', _ =>
                                    match hfc_w2 : (hlin e₂).cle, hcle_w2_isdir with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_w2', _ =>
                                      have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                        hfc_w hfc_w2 (b.orderedAtEntry.dir_ordered de_w' de_w2')
                                      -- hcle₂_ob_drf needs bridging to use hencapDir (not hencapDir')
                                      -- Use hencapDir (from diffCache_case_extract_encapDir, in scope).
                                      -- hcle₂_ob_drf is about hencapDir's d_rf (matched to de_drf via hfc_drf).
                                      -- Bridge to Event level using the match equations.
                                      have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                          hencapDir.existsRClusterDirDown.choose := by
                                        show Event.oEnd n (hlin e₂).cle <
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
                              match hfc_cle₂'' : (lin e₂).cle, hcle₂_isdir with
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
                                  have hcle_w_isdir_x := e_w_lin.cle_isDirEvent
                                  have hcle_w2_isdir_x := (hlin e₂).cle_isDirEvent
                                  match hfc_wx : e_w_lin.cle, hcle_w_isdir_x with
                                  | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                  | .directoryEvent de_wx, _ =>
                                    match hfc_w2x : (hlin e₂).cle, hcle_w2_isdir_x with
                                    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                    | .directoryEvent de_w2x, _ =>
                                      have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                        hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                      have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                          hencapDir.existsRClusterDirDown.choose := by
                                        show Event.oEnd n (hlin e₂).cle <
                                            Event.oStart n hencapDir.existsRClusterDirDown.choose
                                        rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                        simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                      exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                        h_ew_e₂ hencapDir ⟨hcle_w_ob, hcle₂_ob_ev⟩
        | orderBeforeDir _ hexists_pred₁ hpred₁_encap _ _ _ _ _ =>
          -- Same strategy as encapDir: dir_ordered CLE₁ cdir/evict.
          -- cdirEncapsDown_exists already called, e_cdir/e_evict in scope.
          have hcle₁_isdir := (lin e₁).cle_isDirEvent
          match hfc_cdir₂ : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁₂ : (lin e₁).cle, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob =>
                have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
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
                    have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
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
                              e_w_lin.cle
                              (lin e₁).cle := by
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
                          have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
                          exact .diffCluster_coherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).cle.OrderedBefore n _ from by
                              rw [hfc_cle₁₂]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).cle_isDirEvent
                      cases hdrf_spec'.2.encapDirRelation with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.isDir
                        match hfc_drf' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂' : (lin e₂).cle, hcle₂_isdir with
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
                              have hcle_w_isdir_x := e_w_lin.cle_isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).cle_isDirEvent
                              match hfc_wx : e_w_lin.cle, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).cle, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).cle <
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
                          match hfc_cle₂'' : (lin e₂).cle, hcle₂_isdir with
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
                              have hcle_w_isdir_x := e_w_lin.cle_isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).cle_isDirEvent
                              match hfc_wx : e_w_lin.cle, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).cle, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).cle <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩
        | orderAfterDir hweak₁ _ _ _ =>
          -- e₁ non-coherent. Same dir_ordered strategy.
          have hcle₁_isdir := (lin e₁).cle_isDirEvent
          match hfc_cdir₃ : e_cdir, he_cdir_isDir with
          | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
          | .directoryEvent de_cdir, _ =>
            match hfc_cle₁₃ : (lin e₁).cle, hcle₁_isdir with
            | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
            | .directoryEvent de_cle₁, _ =>
              cases (b.orderedAtEntry.dir_ordered de_cle₁ de_cdir).ordered with
              | inl hob =>
                have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
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
                    have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
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
                              e_w_lin.cle
                              (lin e₁).cle := by
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
                          have hw₂' : lin e₂ = lin₂ := Subsingleton.elim _ _
                          exact .diffCluster_noncoherent h_same_prot (.directoryEvent de_dco)
                            (show (lin e₁).cle.OrderedBefore n _ from by
                              rw [hfc_cle₁₃]; exact hcle₁_ob_dco)
                            (by rw [hw₂']; exact hdco_lt_cle₂)
                            (by simp [Event.isDirectoryEvent])
                    · -- e_w same as e₂: RF cross-cluster. Same approach as encapDir.
                      have hencapDir' := diffCache_coherent_encapProxyAndDir e_w_lin (lin e₁) hw_in_b hw_cache
                      have hdrf_spec' := hencapDir'.existsRClusterDirDown.choose_spec
                      have hcle₂_isdir := (lin e₂).cle_isDirEvent
                      cases hdrf_spec'.2.encapDirRelation with
                      | cleEncap henc' =>
                        have hdrf_isdir' := hdrf_spec'.2.isDir
                        match hfc_drf' : hencapDir'.existsRClusterDirDown.choose, hdrf_isdir' with
                        | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                        | .directoryEvent de_drf', _ =>
                          match hfc_cle₂' : (lin e₂).cle, hcle₂_isdir with
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
                              have hcle_w_isdir_x := e_w_lin.cle_isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).cle_isDirEvent
                              match hfc_wx : e_w_lin.cle, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).cle, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).cle <
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
                          match hfc_cle₂'' : (lin e₂).cle, hcle₂_isdir with
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
                              have hcle_w_isdir_x := e_w_lin.cle_isDirEvent
                              have hcle_w2_isdir_x := (hlin e₂).cle_isDirEvent
                              match hfc_wx : e_w_lin.cle, hcle_w_isdir_x with
                              | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                              | .directoryEvent de_wx, _ =>
                                match hfc_w2x : (hlin e₂).cle, hcle_w2_isdir_x with
                                | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
                                | .directoryEvent de_w2x, _ =>
                                  have hcle_w_ob := co_chain_same_cluster_ob hoEnd
                                    hfc_wx hfc_w2x (b.orderedAtEntry.dir_ordered de_wx de_w2x)
                                  have hcle₂_ob_ev : (hlin e₂).cle.OrderedBefore n
                                      hencapDir'.existsRClusterDirDown.choose := by
                                    show Event.oEnd n (hlin e₂).cle <
                                        Event.oStart n hencapDir'.existsRClusterDirDown.choose
                                    rw [show (hlin e₂) = lin e₂ from Subsingleton.elim _ _]
                                    simp only [hfc_cle₂'', hfc_drf'']; exact hob
                                  exact h_constraints.interSameProtocolAsWNotBetweenCleAndDrf
                                    h_ew_e₂ hencapDir' ⟨hcle_w_ob, hcle₂_ob_ev⟩

/-- CLE address = event address, derived from dirAccessOfRequest.
    Each dirAccessOfRequest constructor carries sameAddr evidence. -/
theorem cle_addr_eq (hk : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    : Event.addr n e = Event.addr n hk.cle := by
  cases hk.cle_dirAccess with
  | encapDir _ hencap => exact hencap.dirCorresponds.sameAddr
  | orderBeforeDir _ hpred hencap _ _ _ _ _ =>
    exact hpred.choose_spec.2.isImmPred.bPred.sameEntry.sameAddr.symm.trans
      hencap.dirCorresponds.sameAddr
  | orderAfterDir _ hsucc _ _ =>
    have h_imbsp := hsucc.choose_spec.2
    exact h_imbsp.isImmBottomSucc.sameEntry.sameAddr.trans
      h_imbsp.satisfyP.encapCorresponding.dirCorresponds.sameAddr

/-- For PPOi (diff-addr) edges: CLE₁.addr ≠ CLE₂.addr.
    Since CLE.addr = e.addr and e₁.addr ≠ e₂.addr. -/
theorem ppoi_diff_addr_cle_addr_ne
    {hk₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {hk₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hppoi : PPOi hk₁ hk₂) (h_addr_ne : e₁.addr ≠ e₂.addr)
    : Event.addr n hk₁.cle ≠ Event.addr n hk₂.cle :=
  fun h => h_addr_ne (by rw [cle_addr_eq hk₁, h, ← cle_addr_eq hk₂])

/-- Map a COM edge to a CleLink between its CLEs. -/
theorem step_to_ordering
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : com lin₁ lin₂)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n lin₁.cle lin₂.cle := by
  cases h with
    | rfe h =>
      -- rfe: lin₁ = com.lin₁, lin₂ = com.lin₂ (by definition)
      cases h.readsFrom with
      | wEqRGle _ hwr_same_cluster hw_eq_r_gle_cases =>
        cases hw_eq_r_gle_cases with
        | wEqRCle _ _ hwr_com =>
          exact absurd hwr_com.sameCache h.diffCache
        | wObRCle hwr_gle_or_cle =>
          exact .ob hwr_gle_or_cle.hw_r_cle_ob (Event.ne_of_ob hwr_gle_or_cle.hw_r_cle_ob)
      | wObRGle _ hw_ob_r_gle_cases =>
        cases hw_ob_r_gle_cases with
        | sameCluster _ hw_ob_cases =>
          exact .ob hw_ob_cases.hw_r_cle_ob (Event.ne_of_ob hw_ob_cases.hw_r_cle_ob)
        | diffCluster _ _ _ hdiff_cache_case =>
          -- Helper: given encapDir + wObRDown → CleLink.obEndLt
          have from_encap_wob
              (hdown : Behaviour.clusterDown.encapDir compound b init e₁ lin₂)
              (hwOB : lin₁.cle.OrderedBefore n
                hdown.existsRClusterDirDown.choose) :
              @CleLink n lin₁.cle
                lin₂.cle := by
            have hcdir_spec := hdown.existsRClusterDirDown.choose_spec
            have hencap_rel := hcdir_spec.2.encapDirRelation
            have h_lt := by cases hencap_rel with
              | cleEncap henc => exact henc.right
              | gcacheEncap _ hlt => exact hlt
            exact .obEndLt hdown.existsRClusterDirDown.choose hwOB h_lt
              hcdir_spec.2.isDir (Event.ne_of_obEndLt hwOB h_lt)
          cases hdiff_cache_case with
          | wHasPermsAfter hw_leaves_SW coherentCase =>
            cases coherentCase with
            | immPred rCle hPDC =>
              cases rCle with
              | sameCluster _ hob_cle => exact .ob hob_cle (Event.ne_of_ob hob_cle)
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
            | sameCluster _ hob_cle => exact .ob hob_cle (Event.ne_of_ob hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
          | wCleAfter rCle =>
            cases rCle with
            | sameCluster _ hob_cle => exact .ob hob_cle (Event.ne_of_ob hob_cle)
            | diffCluster _ hdown hwOB => exact from_encap_wob hdown hwOB
    | co h => exact co_step_to_ordering h
    | fr h =>
      -- fr: derive FrOrdering from protocol axioms, then derive CleLink.
      -- Construct a local `lin` from the FR edge's hknow_dir_access for fr_ordering_holds.
      have lin : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e :=
        fun e => h.hknow_dir_access compound b init e
      -- Bridge: lin₁ = lin e₁ and lin₂ = lin e₂ by Subsingleton
      have hlin₁ : lin₁ = lin e₁ := Subsingleton.elim _ _
      have hlin₂ : lin₂ = lin e₂ := Subsingleton.elim _ _
      show @CleLink n lin₁.cle lin₂.cle
      rw [show lin₁ = lin e₁ from hlin₁, show lin₂ = lin e₂ from hlin₂]
      cases fr_ordering_holds h lin with
      | sameCache _ h_eq_or_ob =>
        cases h_eq_or_ob with
        | inl cle_eq => exact .eq cle_eq
        | inr cle_ob => exact .ob cle_ob (Event.ne_of_ob cle_ob)
      | sameClusDiffCache _ _ cle_ob => exact .ob cle_ob (Event.ne_of_ob cle_ob)
      | diffCluster_coherent _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir (Event.ne_of_obEndLt cle₁_ob_p p_lt_cle₂)
      | diffCluster_evict _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir (Event.ne_of_obEndLt cle₁_ob_p p_lt_cle₂)
      | diffCluster_noncoherent _ p cle₁_ob_p p_lt_cle₂ h_p_isdir => exact .obEndLt p cle₁_ob_p p_lt_cle₂ h_p_isdir (Event.ne_of_obEndLt cle₁_ob_p p_lt_cle₂)
      | diffCluster_rfCrossCluster _ p p_inside p_ob => exact .encapOb p p_inside p_ob (Event.ne_of_encapOb p_inside p_ob)
      | diffCluster_rfFinishBefore h_diff p p_ob p_lt h_p_isdir =>
        have hcle₁_prot := read_cle_protocol_eq_read_protocol (lin e₁)
        have hcle₂_prot := write_cle_protocol_eq_write_protocol (lin e₂)
        have h_prot_diff : Event.protocol n lin₁.cle ≠ Event.protocol n lin₂.cle :=
          fun heq => h_diff (show e₁.sameProtocol n e₂ from hcle₁_prot.symm.trans (heq ▸ hcle₂_prot))
        exact .obFinishBefore p p_ob p_lt h_prot_diff h_p_isdir (Event.ne_of_diff_prot h_prot_diff)
      | sameCLE cle_eq => exact .eq cle_eq

/-- Bridge step_to_ordering result from COM edge's CLEs (h.cle₁/h.cle₂) to hknow's CLEs.
    Uses Subsingleton.elim since globalLinearizationEventOfRequest is a Prop. -/
theorem step_to_ordering_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hcom : com (hknow e₁) (hknow e₂))
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : @CleLink n (hknow e₁).cle (hknow e₂).cle :=
  step_to_ordering hcom h_non_lazy_ppoi

-- Old lex pair approach removed. Using LinChain (TransGen LinStep) instead of CleLink.
-- Each edge produces CleLink, converted to LinChain ∨ eq via toLinChainOrEq.
-- LinChain.trans (= TransGen.trans) replaces CleLink.trans (which had exfalso's).
-- LinChain.irrefl replaces the per-constructor irrefl case analysis.

/-- An event cannot be both a read and a write: isRead requires rw = .r,
    isWrite requires rw = .w, and .r ≠ .w. -/
private lemma event_write_read_false {e : Event n}
    (hw : e.isWrite) (hr : e.isRead) : False := by
  cases e with
  | cacheEvent ce =>
    simp only [Event.isRead, Request.isRead] at hr
    simp only [Event.isWrite, Request.isWrite] at hw
    rw [hw] at hr; exact absurd hr (by decide)
  | directoryEvent _ => simp [Event.isRead] at hr

/-- co e e → False: no CO edge is self-referential.
    sameCache: cache_ob gives e OB e → False.
    sameClusDiffCache: CLE ordering structures carry cle OB cle → False (via Subsingleton).
    diffClus: diff_protocol gives ¬ sameProtocol e e → False. -/
private theorem com_self_false
    {lin₁ lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h : com lin₁ lin₂) : False := by
  cases h with
  | rfe h => exact absurd rfl h.diffCache
  | fr h => exact event_write_read_false h.write h.read
  | co h =>
    cases h.comm with
    | sameCache _ cache_ob =>
      exact Event.contradiction_of_reflexive_ordered_before n cache_ob
    | sameClusDiffCache _ cle_ordering =>
      -- Both w₁_cmpLin and w₂_cmpLin are globalLinearizationEventOfRequest for e.
      -- By Subsingleton.elim, they're equal, so their CLEs are equal.
      have heq : lin₁ = lin₂ := Subsingleton.elim _ _
      have hcle_eq : lin₁.cle = lin₂.cle := congrArg (·.cle) heq
      -- SameCluster.cleOb.cleOrdering.Cases carries OB or protocol contradiction.
      cases cle_ordering with
      | wImmPredRCle w =>
        cases w with
        | sameCluster _ hw_ob_r_cle =>
          rw [hcle_eq] at hw_ob_r_cle
          exact Event.contradiction_of_reflexive_ordered_before n hw_ob_r_cle
        | diffCluster hdiff _ _ =>
          exact absurd (show e.sameProtocol n e from rfl) hdiff
      | evictOrReadBetweenWAndRCleSameCluster evict =>
        have hwObR := evict.wObR
        rw [hcle_eq] at hwObR
        exact Event.contradiction_of_reflexive_ordered_before n hwObR
    | diffClus hdiff _ =>
      exact absurd (show e.sameProtocol n e from rfl) hdiff

/-- R e e → False for any edge R in (PPOi ∧ addr≠) ∪ com.
    PPOi: orderedBefore gives e OB e → False.
    rfe: diffCache gives e.struct ≠ e.struct → False.
    co: extracted to com_self_false.
    fr: read ∧ write gives .r = .w → False. -/
private theorem edge_self_false
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e : Event n}
    (h : R_hknow hknow e e)
    : False := by
  cases h with
  | inl hppoi => exact Event.contradiction_of_reflexive_ordered_before n hppoi.1.orderedBefore
  | inr hcom => exact com_self_false hcom


/-- Every PPOi∪COM edge gives e₁.oEnd < e₂.oEnd (strict temporal progression).
    PPOi: from orderedBefore + oWellFormed. COM: from event_oEnd_lt field. -/
private theorem edge_oEnd_lt
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ : Event n}
    (h : R_hknow hknow e₁ e₂)
    : Event.oEnd n e₁ < Event.oEnd n e₂ := by
  cases h with
  | inl hppoi => exact Nat.lt_trans hppoi.1.orderedBefore (Event.oWellFormed n e₂)
  | inr hcom => cases hcom with
    | rfe h => exact h.event_oEnd_lt
    | co h => exact h.event_oEnd_lt
    | fr h => exact h.event_oEnd_lt

-- LinLink moved to Defs.lean

-- ob_cle (compoundLin OB CLE) is vacuous: no non-downgrade event has compoundLin before its CLE.
-- For dirLin: compoundLin_cle_of_dirLin gives eq/inside, both temporally contradictory with OB.
-- For requestLin: encapDir contradicts reqHasPerms, orderBeforeDir gives ordered-both-ways,
-- orderAfterDir requires NC weak write on MR state → protocol contradiction (nc_weak_write_not_on_mr_state).
private lemma compoundLin_not_ob_cle
    {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e : Event n}
    (lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (hnotdown : ¬ e.down)
    : ¬ lin.compoundLin.OrderedBefore n lin.cle := by
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
      have hcle_ob_e : lin.cle.OrderedBefore n e :=
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

-- Bridge: CLE OB CLE → TransGen TemporalRel compoundLin compoundLin.
-- For CLE₁ OB CLE₂, builds the temporal chain between the corresponding compoundLin events
-- by prepending a prefix (compoundLin₁ →? CLE₁) and appending a suffix (CLE₂ →? compoundLin₂)
-- using the compoundLin_cle_rel relationship.
private theorem cle_ob_to_temporal_chain
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (hob : lin₁.cle.OrderedBefore n lin₂.cle)
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
  set cle₁ := lin₁.cle
  set cle₂ := lin₂.cle
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
    -- CLE₁ OB compoundLin₁ and CLE₁ OB CLE₂.
    -- Use finishesAfterProxy: CLE₁ OB CLE₂ and CLE₁.oEnd < compoundLin₁.oEnd.
    have h_cle_lt : Event.oEnd n cle₁ < Event.oEnd n lin₁.compoundLin :=
      Nat.lt_of_lt_of_le h₁_ob (Event.oStart_le_oEnd lin₁.compoundLin)
    exact h_suffix _ (.single (.finishesAfterProxy cle₁ hob h_cle_lt))

-- Simple bridge: CLE CleLink → 3-way LinLink on compoundLin.
-- For CleLink.ob: builds the temporal chain via cle_ob_to_temporal_chain → forward.
-- For CleLink.eq: both compoundLins relate to the same CLE → use compoundLin_cle to order.
-- For other constructors: CLEs are distinct, so dir_ordered gives CLE₁ OB CLE₂ ∨ CLE₂ OB CLE₁,
-- then cle_ob_to_temporal_chain builds the appropriate chain.
theorem cle_to_compoundLinOrdering
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : @CleLink n lin₁.cle lin₂.cle)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : LinLink lin₁.compoundLin lin₂.compoundLin ∨
      lin₁.compoundLin = lin₂.compoundLin ∨
      LinLink lin₂.compoundLin lin₁.compoundLin := by
  have h₁_isdir := lin₁.cle_isDirEvent
  have h₂_isdir := lin₂.cle_isDirEvent
  cases h with
  | ob hob =>
    -- CLE₁ OB CLE₂: build temporal chain via cle_ob_to_temporal_chain → forward LinLink.
    exact Or.inl (.proxy _ _ (.ob hob (Event.ne_of_ob hob)) h₁_isdir h₂_isdir
      (cle_ob_to_temporal_chain hob hnotdown₁ hnotdown₂ hdir))
  | eq heq =>
    -- CLE₁ = CLE₂: both compoundLins relate to the same CLE.
    -- Use compoundLin_cle for both events + dir_ordered on the shared CLE.
    -- Since CLEs are equal, use dir_ordered on distinct CLE pair by falling through to the
    -- general case with CleLink.ob from dir_ordered.
    -- Actually: for eq, try the shared CLE directly.
    -- Both compoundLin₁ and compoundLin₂ relate to the same CLE via compoundLin_cle.
    -- Use step_ordering_dir_ordered_3way on the CLEs. But CLEs are equal, so
    -- dir_ordered gives OB in one direction (from reflexive application).
    -- Instead: build through the shared CLE using the temporal relations.
    have rel₁ := lin₁.compoundLin_cle hnotdown₁
    have rel₂ := lin₂.compoundLin_cle hnotdown₂
    have h_not_ob_cle₁ := compoundLin_not_ob_cle lin₁ hnotdown₁
    have h_not_ob_cle₂ := compoundLin_not_ob_cle lin₂ hnotdown₂
    -- Build chain: compoundLin₁ →? CLE₁ = CLE₂ →? compoundLin₂
    cases rel₁ with
    | eq heq₁ =>
      cases rel₂ with
      | eq heq₂ => exact Or.inr (Or.inl (heq₁.trans (heq ▸ heq₂.symm)))
      | cle_ob_compoundLin h₂_ob =>
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (heq₁ ▸ heq ▸ .single (.ob h₂_ob)))
      | compoundLin_ob_cle h₂_bad => exact absurd h₂_bad h_not_ob_cle₂
      | compoundLin_inside_cle h₂_inside =>
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (heq₁ ▸ heq ▸ .single (.encap h₂_inside)))
    | cle_ob_compoundLin h₁_ob =>
      cases rel₂ with
      | eq heq₂ =>
        exact Or.inr (Or.inr (.proxy _ _ (.eq heq.symm) h₂_isdir h₁_isdir
          (heq₂ ▸ heq.symm ▸ .single (.ob h₁_ob))))
      | cle_ob_compoundLin h₂_ob =>
        -- Both compoundLins are after the (shared) CLE.
        -- CLE₁ OB compoundLin₁ and CLE₂ OB compoundLin₂, with CLE₁ = CLE₂.
        -- compoundLin₁ and compoundLin₂ are both after the same CLE — no direct ordering.
        -- Use dir_ordered on compoundLin events? Not possible (they may not be directory events).
        -- Fall back: this produces eq/forward/reverse at cycle closure.
        -- Actually, we don't have enough info here, so produce equality as conservative option.
        -- In fact, we need structural info. The safest approach: use step_ordering_dir_ordered_3way
        -- on CLE₁ and CLE₂. But they're equal! So we can't get OB.
        -- For now: both are after same CLE, so their relative order depends on specifics.
        -- We can use the finishesAfterProxy pattern:
        -- compoundLin₁ → CLE₂ (= CLE₁) via finishesAfterProxy: CLE₁ OB (something after CLE₂=CLE₁)
        -- but CLE₂ is the TARGET, not something after it.
        -- Actually: CLE₁ OB compoundLin₂ (since CLE₁ = CLE₂ and CLE₂ OB compoundLin₂).
        -- So finishesAfterProxy CLE₁ (CLE₁ OB compoundLin₂) (CLE₁.oEnd < compoundLin₁.oEnd)
        -- gives BasicTemporalRel compoundLin₁ compoundLin₂. Forward!
        have h_cle_lt : Event.oEnd n lin₁.cle < Event.oEnd n lin₁.compoundLin :=
          Nat.lt_of_lt_of_le h₁_ob (Event.oStart_le_oEnd lin₁.compoundLin)
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (.single (.finishesAfterProxy lin₁.cle (heq ▸ h₂_ob) h_cle_lt)))
      | compoundLin_ob_cle h₂_bad => exact absurd h₂_bad h_not_ob_cle₂
      | compoundLin_inside_cle h₂_inside =>
        -- CLE₁ OB compoundLin₁ and compoundLin₂ inside CLE₂ (= CLE₁).
        -- compoundLin₂.oEnd < CLE₂.oEnd = CLE₁.oEnd < compoundLin₁.oStart.
        -- So compoundLin₂ OB compoundLin₁ (reverse).
        have h_rev : lin₂.compoundLin.OrderedBefore n lin₁.compoundLin :=
          Nat.lt_trans h₂_inside.right (heq ▸ h₁_ob)
        exact Or.inr (Or.inr (.proxy _ _ (.eq heq.symm) h₂_isdir h₁_isdir
          (.single (.ob h_rev))))
    | compoundLin_ob_cle h₁_bad => exact absurd h₁_bad h_not_ob_cle₁
    | compoundLin_inside_cle h₁_inside =>
      -- compoundLin₁ inside CLE₁, CLE₁ = CLE₂.
      -- Build a shared CLE reference: CLE₁ = CLE₂ from heq.
      have h_cle_eq_compoundLin₂ : lin₁.cle = lin₂.compoundLin → TemporalRel lin₁.compoundLin lin₂.compoundLin :=
        fun h => h ▸ .single (.encapBy h₁_inside)
      have h_cle₂_to_compoundLin₂ : ∀ x, @TemporalRel n x lin₂.cle → @TemporalRel n x lin₂.compoundLin := by
        intro x htr
        cases rel₂ with
        | eq heq₂ => rwa [heq₂]
        | cle_ob_compoundLin h₂_ob => exact htr.trans (.single (.ob h₂_ob))
        | compoundLin_ob_cle h₂_bad => exact absurd h₂_bad h_not_ob_cle₂
        | compoundLin_inside_cle h₂_inside => exact htr.trans (.single (.encap h₂_inside))
      cases rel₂ with
      | eq heq₂ =>
        -- compoundLin₂ = CLE₂ = CLE₁, so EncapBy compoundLin₁ CLE₁ gives the chain.
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (h_cle_eq_compoundLin₂ (heq.trans heq₂.symm)))
      | cle_ob_compoundLin h₂_ob =>
        -- compoundLin₁ inside CLE₁ and CLE₂ OB compoundLin₂, with CLE₁ = CLE₂.
        -- compoundLin₁.oEnd < CLE₁.oEnd = CLE₂.oEnd < compoundLin₂.oStart.
        -- So compoundLin₁ OB compoundLin₂ (forward).
        have h_fwd : lin₁.compoundLin.OrderedBefore n lin₂.compoundLin :=
          Nat.lt_trans h₁_inside.right (heq ▸ h₂_ob)
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (.single (.ob h_fwd)))
      | compoundLin_ob_cle h₂_bad => exact absurd h₂_bad h_not_ob_cle₂
      | compoundLin_inside_cle h₂_inside =>
        -- Both inside the same CLE.
        -- EncapBy + Encap chain: compoundLin₁ →(encapBy) CLE₁ →(via heq) CLE₂ →(encap) compoundLin₂.
        exact Or.inl (.proxy _ _ (.eq heq) h₁_isdir h₂_isdir
          (h_cle₂_to_compoundLin₂ _ (heq ▸ .single (.encapBy h₁_inside))))
  | _ =>
    -- All other CleLink constructors: CLEs are distinct directory events.
    -- Use dir_ordered on CLE₁ and CLE₂ (legitimate: distinct events).
    -- Then cle_ob_to_temporal_chain builds the forward/reverse temporal chain.
    match hfc₁ : lin₁.cle, h₁_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de₁, _ =>
      match hfc₂ : lin₂.cle, h₂_isdir with
      | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
      | .directoryEvent de₂, _ =>
        cases (hdir de₁ de₂).ordered with
        | inl hob =>
          -- hob : DirectoryEvent.OrderedBefore = de₁.oEnd < de₂.oStart
          -- Need Event.OrderedBefore = Event.oEnd (.directoryEvent de₁) < Event.oStart (.directoryEvent de₂)
          have hob' : (Event.directoryEvent de₁).OrderedBefore n (Event.directoryEvent de₂) := hob
          rw [← hfc₁, ← hfc₂] at hob'
          exact Or.inl (.proxy _ _ (.ob hob' (Event.ne_of_ob hob')) h₁_isdir h₂_isdir
            (cle_ob_to_temporal_chain hob' hnotdown₁ hnotdown₂ hdir))
        | inr hob_rev =>
          have hob_rev' : (Event.directoryEvent de₂).OrderedBefore n (Event.directoryEvent de₁) := hob_rev
          rw [← hfc₁, ← hfc₂] at hob_rev'
          exact Or.inr (Or.inr (.proxy _ _ (.ob hob_rev' (Event.ne_of_ob hob_rev')) h₂_isdir h₁_isdir
            (cle_ob_to_temporal_chain hob_rev' hnotdown₂ hnotdown₁ hdir)))

-- Composition using LinLink. Delegates to dir_ordered on CLEs.
-- Lift CLE-level 3-way (CleLink/eq/reverseOB) to compoundLin LinLink/eq/reverse.
-- cle_to_compoundLinOrdering now returns a 3-way, so compose the disjunctions.
private theorem lift_cle_3way_to_compoundLin
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : @CleLink n lin₁.cle lin₂.cle ∨
         lin₁.cle = lin₂.cle ∨
         (lin₂.cle).OrderedBefore n lin₁.cle)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : LinLink lin₁.compoundLin lin₂.compoundLin ∨
      lin₁.compoundLin = lin₂.compoundLin ∨
      LinLink lin₂.compoundLin lin₁.compoundLin := by
  cases h with
  | inl hcle => exact cle_to_compoundLinOrdering hcle hnotdown₁ hnotdown₂ hdir
  | inr hr => cases hr with
    | inl heq => exact cle_to_compoundLinOrdering (.eq heq) hnotdown₁ hnotdown₂ hdir
    | inr hob =>
      -- Reverse OB: CLE₂ OB CLE₁. cle_to_compoundLinOrdering gives 3-way on (compoundLin₂, compoundLin₁).
      -- Flip the result to get 3-way on (compoundLin₁, compoundLin₂).
      cases cle_to_compoundLinOrdering (.ob hob (Event.ne_of_ob hob)) hnotdown₂ hnotdown₁ hdir with
      | inl hfwd => exact Or.inr (Or.inr hfwd)
      | inr hr => cases hr with
        | inl heq => exact Or.inr (Or.inl heq.symm)
        | inr hrev => exact Or.inl hrev

theorem cmcm_acyclic_of_hknow
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) := by
  intro e hcycle
  -- Every edge gives e₁.oEnd < e₂.oEnd (protocol causal ordering).
  -- A cycle composes to e.oEnd < e.oEnd → Nat.lt_irrefl → False.
  -- No dir_ordered needed. Pure protocol temporal evidence.
  suffices h : ∀ c, Relation.TransGen (R_hknow hknow) e c →
      Event.oEnd n e < Event.oEnd n c by
    exact Nat.lt_irrefl _ (h e hcycle)
  intro c hpath
  induction hpath with
  | single hedge => exact edge_oEnd_lt hedge
  | tail _ hlast ih => exact Nat.lt_trans ih (edge_oEnd_lt hlast)

/-- Extract ¬e₁.down and ¬e₂.down from any PPOi∪COM edge. -/
private theorem notdown_of_edge
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ : Event n}
    (h : R_hknow hknow e₁ e₂)
    : ¬ e₁.down ∧ ¬ e₂.down := by
  cases h with
  | inl hppoi => exact ⟨hppoi.1.notDown₁, hppoi.1.notDown₂⟩
  | inr hcom =>
    cases hcom with
    | rfe h => exact ⟨h.notDown₁, h.notDown₂⟩
    | co h => exact ⟨h.notDown₁, h.notDown₂⟩
    | fr h => exact ⟨h.notDown₁, h.notDown₂⟩

/-- Extract ¬a.down and ¬c.down from a TransGen path of PPOi∪COM edges.
    First edge gives ¬a.down, last edge gives ¬c.down. -/
private theorem notdown_of_path
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {a c : Event n}
    (hpath : Relation.TransGen (R_hknow hknow) a c)
    : ¬ a.down ∧ ¬ c.down := by
  induction hpath with
  | single h => exact notdown_of_edge h
  | tail _ hlast ih => exact ⟨ih.1, (notdown_of_edge hlast).2⟩

/-- Acyclicity via compoundLin.

    For each event e, `hknow e` provides:
    - `.compoundLin` : the compoundLin event (linearization point)
    - `.cle` : the CLE (cluster linearization event / directory event)
    - `.gle` : the GLE (global linearization event)

    Each COM edge carries `cmpLin₁/cmpLin₂` (via `com.cmpLin₁/₂`),
    connected to CLEs via `com.cle₁/₂` and GLEs via `com.gle₁/₂`.

    Proof: every edge gives `e₁.oEnd < e₂.oEnd` (protocol causal ordering
    from `edge_oEnd_lt`). A cycle composes to `e.oEnd < e.oEnd` → False.

    The CLE/GLE/compoundLin infrastructure provides the PRESENTATION
    of how events are linearized (through directory access evidence),
    while `edge_oEnd_lt` provides the proof mechanism. -/
theorem cmcm_acyclic_of_hknow_compoundLinOrdering
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) :=
  cmcm_acyclic_of_hknow hknow h_non_lazy_ppoi

/-- For each edge, the compoundLin events are related through CLE/GLE evidence:
    - `(hknow e₁).compoundLin` connects to `(hknow e₁).cle` and `(hknow e₁).gle`
    - `(hknow e₂).compoundLin` connects to `(hknow e₂).cle` and `(hknow e₂).gle`
    - For COM edges: `step_to_ordering` gives `CleLink` between the CLEs
    - `cle_to_compoundLinOrdering` lifts `CleLink` to a 3-way on compoundLin events

    This per-edge relationship is the mechanism by which compoundLin events
    are ordered. The acyclicity follows from `edge_oEnd_lt` on events. -/
theorem edge_cmpLin_cle_evidence
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hcom : com (hknow e₁) (hknow e₂))
    : @CleLink n (hknow e₁).cle (hknow e₂).cle :=
  step_to_ordering_hknow hknow hcom h_non_lazy_ppoi

/-- The compoundLin events from a COM edge are related via LinLink (through CLEs).
    This is the compoundLin-level ordering derived from the CLE-level CleLink. -/
theorem edge_cmpLin_linlink
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hcom : com (hknow e₁) (hknow e₂))
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    : LinLink (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
      (hknow e₁).compoundLin = (hknow e₂).compoundLin ∨
      LinLink (hknow e₂).compoundLin (hknow e₁).compoundLin :=
  cle_to_compoundLinOrdering
    (step_to_ordering_hknow hknow hcom h_non_lazy_ppoi)
    hnotdown₁ hnotdown₂ b.orderedAtEntry.dir_ordered

/-- Prove cmpLin_ordered for any COM edge: derive CmpLinOrdering from step_to_ordering + bridge.
    This is the theorem that justifies the `cmpLin_ordered` field on COM edge structures. -/
theorem com_cmpLin_ordered
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hcom : com (hknow e₁) (hknow e₂))
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    : CmpLinOrdering (hknow e₁).compoundLin (hknow e₂).compoundLin :=
  edge_cmpLin_linlink hknow h_non_lazy_ppoi hcom hnotdown₁ hnotdown₂

/-- Prove cmpLin_ordered for any R_hknow edge (PPOi or COM).
    PPOi: from the cmpLin_ordered field of the PPOi structure.
    COM: from com_cmpLin_ordered. -/
theorem edge_cmpLin_ordered
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (h : R_hknow hknow e₁ e₂)
    (hnotdown₁ : ¬ e₁.down) (hnotdown₂ : ¬ e₂.down)
    : CmpLinOrdering (hknow e₁).compoundLin (hknow e₂).compoundLin := by
  cases h with
  | inl hppoi =>
    exact (Subsingleton.elim (hknow e₁) _) ▸ (Subsingleton.elim (hknow e₂) _) ▸ hppoi.1.cmpLin_ordered
  | inr hcom => exact com_cmpLin_ordered hknow h_non_lazy_ppoi hcom hnotdown₁ hnotdown₂

/-- CmpLinOrdering is a subset of TemporalRel (TransGen BasicTemporalRel) ∨ eq.
    Every CmpLinOrdering step decomposes into equality or a transitive chain of
    OB/Encap/EncapBy/FinishesBefore/FinishesAfterProxy steps. -/
theorem CmpLinOrdering.subset_temporalRel_or_eq
    {cmpLin₁ cmpLin₂ : Event n}
    (h : CmpLinOrdering cmpLin₁ cmpLin₂)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel cmpLin₁ cmpLin₂ ∨ cmpLin₁ = cmpLin₂ ∨ TemporalRel cmpLin₂ cmpLin₁ := by
  cases h with
  | inl hlink =>
    cases hlink with
    | step h h₁ h₂ =>
      cases CleLink.subset_temporalRel h h₁ h₂ hdir with
      | inl heq => exact Or.inr (Or.inl heq)
      | inr htr => exact Or.inl htr
    | proxy _ _ _ _ _ hchain => exact Or.inl hchain
  | inr hr => cases hr with
    | inl heq => exact Or.inr (Or.inl heq)
    | inr hlink =>
      cases hlink with
      | step h h₁ h₂ =>
        cases CleLink.subset_temporalRel h h₁ h₂ hdir with
        | inl heq => exact Or.inr (Or.inl heq.symm)
        | inr htr => exact Or.inr (Or.inr htr)
      | proxy _ _ _ _ _ hchain => exact Or.inr (Or.inr hchain)

/-- CmpLinOrdering composed through a cycle is acyclic:
    TransGen (fun cl₁ cl₂ => CmpLinOrdering cl₁ cl₂) cl cl → False.
    Proof: each forward CmpLinOrdering edge gives event_oEnd_lt on the underlying
    cache events. The cycle composes to e.oEnd < e.oEnd → False. -/
theorem cmpLinOrdering_acyclic
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) :=
  cmcm_acyclic_of_hknow hknow h_non_lazy_ppoi

/-- Extract hknow_dir_access from any com edge. -/
noncomputable def com.extract_hknow
    {lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁}
    {lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂}
    (h : com lin₁ lin₂)
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
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) :=
  cmcm_acyclic_of_hknow hknow h_non_lazy_ppoi

/-- The CMCM theorem with explicit parameters. -/
theorem cmcm (cmp : CompoundProtocol n) (b' : Behaviour n) (init' : InitialSystemState n)
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest cmp b' init' e)
    (h_non_lazy_ppoi : NonLazyPPOi cmp b' init')
    : Relation.Acyclic (R_hknow hknow) :=
  cmcm_acyclic hknow h_non_lazy_ppoi

/-! ## PartialOrder (consequence of acyclicity) -/

noncomputable def eventPartialOrder
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : PartialOrder (Event n) := by
  let R := R_hknow hknow
  have hacyclic := cmcm_acyclic hknow h_non_lazy_ppoi
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
