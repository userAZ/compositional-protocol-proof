import CompositionalProtocolProof.CompoundPPOs

variable (n : Nat)

set_option quotPrecheck false
infix:50 " ≺OB " => (Event.OrderedBefore n)

theorem CompoundProtocol.enforce_compound_consistency
  {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
  (cmp : CompoundProtocol n) (hsame_protocol : e₁.sameProtocol n e₂)
  (he₁_not_downgrade : ¬ e₁.down) (he₂_not_downgrade : ¬ e₂.down)
  (he₁_cache : e₁.isCacheEvent) (he₂_cache : e₂.isCacheEvent)
  (he₁_in_b : e₁ ∈ b) (he₂_in_b : e₂ ∈ b)
  (hsame_cache : e₁.cid = e₂.cid) (hdiff_addr : e₁.addr ≠ e₂.addr)
  : e₁ ≺OB e₂ → cmp.CompoundLinearizationOrder n b init e₁ e₂
  := by
  intro he₁_ob_e₂ hppo
  apply CompoundProtocol.ppo_cluster_events_satisfy_CompoundLinearizationOrder
  . case hsame_protocol => exact hsame_protocol
  . case he₁_not_down => exact he₁_not_downgrade
  . case he₂_not_down => exact he₂_not_downgrade
  . case he₁_cache => exact he₁_cache
  . case he₂_cache => exact he₂_cache
  . case he₁_in_b => exact he₁_in_b
  . case he₂_in_b => exact he₂_in_b
  . case hsame_cid =>
    simp[Event.sameCid]
    cases e₁
    . case cacheEvent ce₁ =>
      cases e₂
      . case cacheEvent ce₂ =>
        simp[Event.cid] at hsame_cache
        simp[hsame_cache]
      . case directoryEvent _ =>
        simp[Event.isCacheEvent] at he₂_cache
    . case directoryEvent _ =>
      simp[Event.isCacheEvent] at he₁_cache
  . case hsame_cid' => exact hsame_cache
  . case hdiff_addr => exact hdiff_addr
  . case a => exact he₁_ob_e₂
  . case a => exact hppo
  . case a => exact hppo

#print axioms CompoundProtocol.enforce_compound_consistency
