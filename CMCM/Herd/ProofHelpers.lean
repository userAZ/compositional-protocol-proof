import CMCM.Herd.Defs
import CMCM.CoTheorem

/-! Helper theorems that need extra heartbeats due to cache_ordered case analysis. -/

namespace Herd

variable {n : ℕ} {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}


/-- For same-cache events: derive e₁ OB e₂ from event_fb (direction evidence). -/
theorem event_ob_of_same_cache'
    {b : Behaviour n} {e₁ e₂ : Event n}
    (h₁_cluster : e₁.isClusterCache) (h₂_cluster : e₂.isClusterCache)
    (h₁_notdown : ¬ e₁.down) (h₂_notdown : ¬ e₂.down)
    (event_fb : Event.oEnd n e₁ < Event.oEnd n e₂)
    : e₁.OrderedBefore n e₂ :=
  cache_events_ordered_from_not_reverse (b := b) h₁_cluster h₂_cluster h₁_notdown h₂_notdown
    (fun h => Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans h (Event.oWellFormed n e₁)) event_fb))

end Herd
