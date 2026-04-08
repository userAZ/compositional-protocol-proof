import CMCM.Herd.Proof

/-! # Acyclic Temporal Chain — Irreflexive Subtype of TemporalRel -/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

structure CmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (e₁ e₂ : Event n) : Prop where
  chain : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
          (hknow e₁).compoundLin = (hknow e₂).compoundLin
  level : ProtoOBLevel hknow e₁ e₂

theorem CmpLinForwardStep.trans
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ e₃ : Event n}
    (h₁ : CmpLinForwardStep hknow e₁ e₂) (h₂ : CmpLinForwardStep hknow e₂ e₃)
    : CmpLinForwardStep hknow e₁ e₃ := by
  refine ⟨?_, proto_ob_level_trans h₁.level h₂.level⟩
  cases h₁.chain with
  | inl hfwd₁ => cases h₂.chain with
    | inl hfwd₂ => exact Or.inl (hfwd₁.trans hfwd₂)
    | inr heq₂ => exact Or.inl (heq₂ ▸ hfwd₁)
  | inr heq₁ => cases h₂.chain with
    | inl hfwd₂ => exact Or.inl (heq₁ ▸ hfwd₂)
    | inr heq₂ => exact Or.inr (heq₁.trans heq₂)

theorem CmpLinForwardStep.irrefl
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e : Event n} (h : CmpLinForwardStep hknow e e) : False :=
  proto_ob_level_irrefl h.level

/-- For eventOB (e₁ OB e₂, same CLE): chain_of_sameCLE gives forward or eq, never reverse.
    Reverse cases (cle_ob × eq, cle_ob × inside) are contradicted by eventOB + encapDir.
    Eq × anything and inside × anything give forward or eq (after inside×eq fix). -/
private theorem eventOB_chain_forward_or_eq
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    {e₁ e₂ : Event n}
    (h_ob : e₁.OrderedBefore n e₂)
    (h_cle_eq : (hknow e₁).cle = (hknow e₂).cle)
    (hnd₁ : ¬ e₁.down)
    (rel₁ : CmpLinCleRel (hknow e₁).compoundLin (hknow e₁).cle)
    (rel₂ : CmpLinCleRel (hknow e₂).compoundLin (hknow e₂).cle)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel (hknow e₁).compoundLin (hknow e₂).compoundLin ∨
      (hknow e₁).compoundLin = (hknow e₂).compoundLin := by
  cases chain_of_sameCLE rel₁ (h_cle_eq ▸ rel₂) hdir with
  | inl hfwd => exact Or.inl hfwd
  | inr hor => cases hor with
    | inl heq => exact Or.inr heq
    | inr hrev =>
      -- Reverse: only from cle_ob in rel₁ position.
      -- cle_ob: CLE OB compoundLin₁. compoundLin_eq_of_cle_ob gives compoundLin₁ = e₁.
      -- Then CLE.oEnd < e₁.oStart. e₁ OB e₂: e₁.oEnd < e₂.oStart.
      -- So CLE.oEnd < e₂.oStart.
      -- For rel₂ (eq or inside): dirAccessOfRequest for e₂ gives encapDir
      -- (since eq/inside come from dirLin → reqMissingPerms → encapDir).
      -- encapDir: e₂.Encapsulates CLE₂. e₂.oStart < CLE₂.oStart.
      -- h_cle_eq: CLE₁ = CLE₂. So e₂.oStart < CLE.oStart ≤ CLE.oEnd < e₂.oStart → False.
      exfalso
      cases rel₁ with
      | cle_ob _ _ h₁_ob _ =>
        -- compoundLin₁ = e₁. CLE OB compoundLin₁ → CLE OB e₁ → CLE.oEnd < e₁.oStart.
        have h_cmpLin_eq := compoundLin_eq_of_cle_ob hnd₁ h₁_ob
        -- CLE.oEnd < compoundLin₁.oStart = e₁.oStart. e₁.oEnd < e₂.oStart.
        have h_cle_lt_e₂ : Event.oEnd n (hknow e₁).cle < Event.oStart n e₂ :=
          Nat.lt_trans h₁_ob (Nat.lt_trans (h_cmpLin_eq ▸ Event.oWellFormed n _) (h_cmpLin_eq ▸ h_ob))
        -- h_cle_eq: CLE₁ = CLE₂.
        have h_cle₂_lt := h_cle_eq ▸ h_cle_lt_e₂  -- CLE₂.oEnd < e₂.oStart
        -- dirAccessOfRequest for e₂: encapDir gives e₂.Encapsulates CLE₂.
        cases (hknow e₂).cle_dirAccess with
        | encapDir _ hencap =>
          -- e₂.oStart < CLE₂.oStart (encapDir). CLE₂.oEnd < e₂.oStart (h_cle₂_lt).
          -- e₂.oStart < CLE₂.oStart ≤ CLE₂.oEnd < e₂.oStart → e₂.oStart < e₂.oStart → False.
          exact Nat.lt_irrefl _ (Nat.lt_trans hencap.reqEncapDir.left
            (Nat.lt_trans (Event.oWellFormed n _) h_cle₂_lt))
        | orderBeforeDir hhas _ _ _ _ _ _ _ =>
          -- reqHasPerms for e₂. But rel₂ is eq or inside (from chain_of_sameCLE reverse).
          -- eq/inside come from dirLin → reqMissingPerms. reqHasPerms + reqMissingPerms → False.
          -- However: we don't have reqMissingPerms directly. We have dirAccessOfRequest = orderBeforeDir.
          -- orderBeforeDir IS a case of dirAccessOfRequest — it doesn't carry reqMissingPerms.
          -- The contradiction: cle_ob on rel₂'s CLE = same CLE as rel₁. orderBeforeDir means
          -- predecessor encapsulates CLE. But we also showed CLE.oEnd < e₂.oStart.
          -- predecessor encaps CLE → CLE.oEnd < predecessor.oEnd. predecessor OB e₂.
          -- CLE.oEnd < predecessor.oEnd < e₂.oStart. But we already have CLE.oEnd < e₂.oStart.
          -- These are consistent. Need a different contradiction.
          -- Use: for orderBeforeDir at the SAME CLE as cle_ob: predecessor encapsulates CLE.
          -- predecessor OB e₂. CLE OB e₁ OB e₂. predecessor.oEnd < e₂.oStart.
          -- All consistent. No direct contradiction.
          -- BUT: rel₂ being eq means compoundLin₂ = CLE₂ from compoundLin_cle_to_CmpLinCleRel.
          -- This arises from dirLin (reqMissingPerms). orderBeforeDir needs reqHasPerms.
          -- reqHasPerms_not_reqMissingPerms → False.
          -- The issue: I'm case-splitting on DIFFERENT instances of cle_dirAccess.
          -- rel₂ was derived from one instance, and I'm case-splitting on another.
          -- They should be the same (Subsingleton). Use Subsingleton.elim.
          sorry
        | orderAfterDir hweak _ _ _ =>
          -- orderAfterDir at cluster level: ncWeakReqOnVd for e₂.
          -- For the temporal contradiction: similar to encapDir but via successor.
          sorry
      | eq _ =>
        -- eq × anything: chain_of_sameCLE never gives reverse for eq in position 1.
        -- eq × eq → eq. eq × cle_ob → forward (OB). eq × inside → forward (Encap).
        -- hrev was constructed from a code path that doesn't execute for eq rel₁.
        -- The hrev : TemporalRel carries vacuous evidence.
        -- Since chain_of_sameCLE with eq rel₁ returns Or.inl or Or.inr (Or.inl _),
        -- the Or.inr (Or.inr _) branch is unreachable. But Lean doesn't know this.
        -- The proof: match on (h_cle_eq ▸ rel₂) to show chain_of_sameCLE gives forward/eq.
        -- For eq × eq: Or.inr (Or.inl _). For eq × cle_ob: Or.inl _. For eq × inside: Or.inl _.
        -- None give Or.inr (Or.inr _). So hrev is False.
        -- Actually: we're in the branch where chain_of_sameCLE DID return reverse (hrev).
        -- This means the `cases` chose the inr (inr _) branch. For eq rel₁: this can't happen.
        -- But Lean's `cases` is exhaustive — the branch exists even if unreachable.
        -- The hrev is a valid TemporalRel term constructed from eq × reverse-producing rel₂.
        -- For eq rel₁: chain_of_sameCLE pattern-matches rel₁ = eq → subst → match rel₂.
        -- None of the rel₂ cases produce reverse. So hrev's construction is impossible.
        -- But: Lean has ALREADY done the `cases` on chain_of_sameCLE's result — we're in
        -- the reverse branch. The question: is this branch truly empty?
        -- The answer: chain_of_sameCLE returns an Or. Lean can't simplify the Or at this point.
        -- We need: for eq rel₁, chain_of_sameCLE NEVER returns inr (inr _).
        -- This is a property of chain_of_sameCLE's code, not extractable from its result.
        sorry
      | inside _ _ _ =>
        -- inside × eq → forward (EncapBy). inside × cle_ob → forward. inside × inside → dir_ordered.
        -- For inside × inside with dir_ordered reverse: both cases give OB on dir events.
        -- Same GLE → same cmpLin → dir_ordered on same event → self-OB → vacuous.
        sorry

theorem edge_to_cmpLinForwardStep
    {hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e}
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    {e₁ e₂ : Event n}
    (hedge : R_hknow hknow e₁ e₂)
    : CmpLinForwardStep hknow e₁ e₂ := by
  have pfs := edge_to_proto_forward h_non_lazy_ppoi hedge
  have ⟨hrel₁, hrel₂⟩ := edge_cmpLinCleRels hedge
  have h_cl := Relation.TransGen.single (edge_clelink h_non_lazy_ppoi hedge)
  cases chain_of_obLevel pfs.level hrel₁ hrel₂ h_cl with
  | inl hfwd => exact ⟨Or.inl hfwd, pfs.level⟩
  | inr hor => cases hor with
    | inl heq => exact ⟨Or.inr heq, pfs.level⟩
    | inr hrev =>
      -- Reverse: only from eventOB. gleOB/cleOB always give forward.
      cases pfs.level with
      | gleOB h => exact ⟨Or.inl (temporalRel_of_gleOB_and_cmpLinCleRels h hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered h_cl), .gleOB h⟩
      | cleOB h_eq h => exact ⟨Or.inl (temporalRel_of_cleOB_and_cmpLinCleRels h hrel₁ hrel₂),
          .cleOB h_eq h⟩
      | eventOB h_gle_eq h_cle_eq h_ob =>
        exact ⟨eventOB_chain_forward_or_eq h_ob h_cle_eq (notdown_of_edge hedge).1 hrel₁ hrel₂
          b.orderedAtEntry.dir_ordered, .eventOB h_gle_eq h_cle_eq h_ob⟩

theorem cmcm_acyclic_via_cmpLinForwardStep
    (hknow : ∀ e : Event n, CompoundProtocol.globalLinearizationEventOfRequest compound b init e)
    (h_non_lazy_ppoi : NonLazyPPOi compound b init)
    : Relation.Acyclic (R_hknow hknow) := by
  intro e hcycle
  suffices h : ∀ c, Relation.TransGen (R_hknow hknow) e c →
      CmpLinForwardStep hknow e c by
    exact CmpLinForwardStep.irrefl (h e hcycle)
  intro c hpath
  induction hpath with
  | single hedge => exact edge_to_cmpLinForwardStep h_non_lazy_ppoi hedge
  | tail _ hlast ih =>
    exact CmpLinForwardStep.trans ih (edge_to_cmpLinForwardStep h_non_lazy_ppoi hlast)

end Herd
