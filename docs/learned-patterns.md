# Learned Reasoning Patterns

## Protocol-level patterns

### CLE equality shortcut (same address)
For same-address PPOi (e₁ OB e₂), if CLE₁ = CLE₂, then `cle_eq_implies_gle_eq` gives GLE₁ = GLE₂, and `hierarchicallyOrdered_of_same_cle` closes the goal at level 3. Always check CLE equality first via `by_cases`.

### nc.weak shares CLE with its PPO successor (same address)
For same-address PPOi with nc.weak as e₁: the nc.weak event linearizes at the SAME directory event as its release successor. Trace through `dirAccessOfRequest` cases for nc.weak.

### Predecessor elimination (same address)
When two events e₁ OB e₂ share an address, show GLE₁ ≤ GLE₂ by assuming GLE₂ < GLE₁ for contradiction. Uses `ImmediateBottomPredSatisfyingProp`.

### Cross-cluster co chain StepOrdering is always strict
When co⁺(e_w, e₂) gives StepOrdering and CLEs are at different clusters: `.sameLin`/`.eq` carry CLE₁ = CLE₂ → impossible (different protocols). Only `.ob`/`.obEndLt` remain → strict.

### dir_ordered validity
`dir_ordered` is universally quantified (model over-strength). ONLY use between directory events at the SAME cluster AND same address. Self-application (de de) gives False.

### Junction compatibility (FR+FR impossible)
FR(e₁,e₂) needs e₂.isWrite. FR(e₂,e₃) needs e₂.isRead. Same event can't be both → edge pair vacuous. Extends to: co+FR, rfe+rfe, rfe+co impossible at junction. Use `h_junction_compat : ¬(e₂.isWrite ∧ e₂.isRead)`.

### .ob → same-cluster → same-protocol
StepOrdering.ob from step_to_ordering only arises from same-cluster edges (PPOi sameProtocol, rfe/co/fr same-cluster sub-cases). obFinishBefore h₁ (l₁≠l₂) + .ob h₂ (l₂=l₃) → l₁≠l₃ → same-protocol assumption vacuous.

### by_cases protocol is the universal first move
Every compose_three sorry reduces to `by_cases l₁.protocol = l₃.protocol`. Same → dir_ordered → .ob or l₃ OB l₁. Diff → .obFinishBefore output. Try this FIRST before anything else.

### 2-cluster pigeonhole
Only .cluster1 and .cluster2 for CLEs (not .global). l₁≠l₂ ∧ l₂≠l₃ → l₁=l₃.

## Lean-specific patterns

### Temporal chaining
`Trans.trans` for OB + OB. `Nat.lt_trans` for OB + Encapsulates.left (oStart < oStart). `show Event.OrderedBefore n _ _ from Nat.lt_trans ...` to cast Nat.lt to OB.

### Derive equalities BEFORE matches
After `match hfc₁ : l₁, h₁_isdir with | .directoryEvent de₁, _ =>`: hypotheses before the match keep `l₁`, goal has `de₁`. `rw [hfc₁]` fails in hypotheses. Fix: derive equalities (protocol chains, etc.) BEFORE the match when `l₁` is still abstract.

### Lean match substitution
After `match hfc : l, ... with | .directoryEvent de, _ =>`: Lean substitutes `l` with `.directoryEvent de` in the GOAL. Hypotheses created BEFORE the match keep original `l`. Use `congrArg (Event.protocol n) hfc` to bridge.

### Event.protocol for directory events
`Event.protocol n (.directoryEvent de) = de.pInst` (definitional). `write_cle_protocol_eq_write_protocol` gives `cle.protocol = e.protocol` for any event (despite the name).

### Exists.choose opacity
`Classical.choice` doesn't reduce on concrete witnesses. Use `dirAccessUnique` field or `Subsingleton.elim` to bridge different `Exists.choose` paths.

## Proof architecture patterns

### Push sorry's to infrastructure lemmas
When Proof.lean needs protocol evidence, extend infrastructure (like `cdirEncapsDown_exists`) to return it, keeping the main proof clean.

### Descriptive definitions carry mechanism
Definitions should carry WHAT HAPPENED (which events, their OB/Encap relationships). The ordering is DERIVED from this evidence. A reviewer should see the derivation, not "trust me, CLE advances."

### StepOrdering constructors
- ob: l₁ OB l₂ (same-cluster, from dir_ordered)
- obEndLt: l₁ OB p, p.oEnd < l₂.oEnd (cross-cluster, proxy finishes before target CLE)
- encapOb: p inside l₁, p OB l₂ (proxy chain)
- obFinishBefore: p OB l₂, p.oEnd < l₁.oEnd, l₁≠l₂ protocol (cross-cluster, backward proxy)
- proxyPair: q inside l₁, q OB p, p OB l₂ (two-proxy chain)
- encapObEndLt: q inside l₁, q OB p, p.oEnd < l₂.oEnd (encap + oEnd bound)
- sameLin/eq: identity cases
