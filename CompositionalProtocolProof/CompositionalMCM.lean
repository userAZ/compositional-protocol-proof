import CompositionalProtocolProof.CompoundPPOs

variable (n : Nat)

theorem CompoundProtocol.enforce_compound_consistency
  {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
  (cmp : CompoundProtocol n) (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_not_downgrade : ¬ e₁.down) (he₂_not_downgrade : ¬ e₂.down)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_in_b : e₁ ∈ b) (he₂_in_b : e₂ ∈ b)
  (hsame_cache : e₁.cid = e₂.cid) (hdiff_addr : e₁.addr ≠ e₂.addr)
  : e₁.OrderedBefore n e₂ → cmp.CompoundLinearizationOrder n b init e₁ e₂
  := by
  sorry
