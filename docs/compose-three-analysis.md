# compose_three: Detailed Sorry Analysis

## Architecture

compose_three composes `h₁ : StepOrdering l₁ l₂ ∨ l₁ = l₂` (prefix TransGen result) with
`hedge : (PPOi ∧ diff_addr) ∪ com` (current edge) to produce `StepOrdering l₁ l₃ ∨ l₁ = l₃`.

Also takes: `h_prefix_edge` (last prefix edge from TransGen case-split), `hknow`, `hl₂/hl₃`,
`hdir` (dir_ordered), `h₁_isdir`.

Derives internally: `h_junction_compat : ¬(e₂.isWrite ∧ e₂.isRead)`,
`h_e₂_from_hedge/prefix` (read/write from each edge).

## Proven compositions

**ob/encapOb/proxyPair/encapObEndLt h₁ × ob/obEndLt/encapOb/proxyPair/encapObEndLt/sameLin/eq h₂**: All proven via OB transitivity (`Trans.trans`) and `Nat.lt_trans` for oStart/oEnd chains.

**obFinishBefore h₁ + ob h₂ (PPOi)**: Proven. PPOi.sameProtocol → l₂=l₃ → l₁≠l₃ → .obFinishBefore.

**obFinishBefore h₁ + ob h₂ (com)**: Diff-protocol direction proven via `by_cases protocol`. Same-protocol: `exfalso` via protocol chain (l₁=l₃=l₂ contradicts l₁≠l₂). Protocol extraction: co sameCache/sameClusDiffCache proven. rfe/fr: use `Classical.em` + pigeonhole.

**obFinishBefore h₁ + encapOb/proxyPair h₂ (diff-protocol direction)**: Proven. Chain: p₁ OB l₂ + l₂ encaps p₂ → p₁ OB p₂ → p₁ OB l₃ → .obFinishBefore.

**obFinishBefore h₁ + obEndLt h₂ (diff-protocol, same-cluster)**: Proven. dir_ordered(l₂, l₃): l₂ OB l₃ → chain p₁ OB l₃ → .obFinishBefore. l₃ OB l₂ → temporal loop contradiction.

**l₃ OB l₂ contradictions (encapOb/proxyPair h₂)**: Proven via temporal chain: l₃.oEnd < l₂.oStart < p₂.oStart ≤ p₂.oEnd < l₃.oStart ≤ l₃.oEnd → l₃.oEnd < l₃.oEnd.

## Remaining sorry categories

### 1. Same-protocol l₃ OB l₁ (3 sorry's)
After `by_cases hprot + dir_ordered`: l₁ OB l₃ → .ob ✓. l₃ OB l₁ → sorry.
- **For .ob h₂**: VACUOUS (l₂=l₃ protocol from same-cluster edge + l₁≠l₂ → l₁≠l₃ → contradicts same-prot). Needs protocol extraction from com edge.
- **For non-.ob h₂**: cross-cluster h₂ → pigeonhole l₁=l₃. l₃ OB l₁ is protocol-impossible (cycle path advances CLE at shared cluster) but hard to prove from abstract StepOrdering.

### 2. Pigeonhole (2 sorry's)
Need: `l₁≠l₂ ∧ l₂≠l₃ → l₁=l₃` for 2-cluster CLEs (.cluster1, .cluster2).

### 3. PPOi non-ob (1 sorry)
PPOi's step_to_ordering always gives .ob (from dir_ordered). The wildcard catch shouldn't arise. Vacuous but hard to prove without introspecting step_to_ordering.

### 4. Proxy ordering (obEndLt/encapObEndLt h₁ + encapOb/proxyPair h₂) (~4 sorry's)
p₁.oEnd < l₂.oEnd and p₂ inside l₂. Proxies at different clusters → no dir_ordered.
**Key**: use `h_prefix_edge + h_junction_compat` to eliminate impossible pairs:
- FR+FR: e₂.isWrite ∧ e₂.isRead → IMPOSSIBLE
- co+FR: e₂.isWrite ∧ e₂.isRead → IMPOSSIBLE
- rfe+rfe: e₂.isRead ∧ e₂.isWrite → IMPOSSIBLE
Compatible pairs (rfe+FR, etc.): proxies may be at same cluster → dir_ordered resolves.

### 5. Wildcards (h₁+obFinishBefore h₂, h₁+encapObEndLt h₂) (2 sorry's)
Need same `by_cases protocol + dir_ordered + junction check` treatment.

## Junction compatibility table

| Prefix\Current | PPOi | rfe(e₂.W) | co(e₂.W) | fr(e₂.R) |
|----------------|------|-----------|----------|----------|
| PPOi           | ✓    | ✓         | ✓        | ✓        |
| rfe(e₂.R)     | ✓    | **X**     | **X**    | ✓        |
| co(e₂.W)      | ✓    | ✓         | ✓        | **X**    |
| fr(e₂.W)      | ✓    | ✓         | ✓        | **X**    |

X = impossible (e₂.isWrite ∧ e₂.isRead → False via h_junction_compat)

## Key technique: derive protocol BEFORE matches

To avoid Lean type bridging issues with `match hfc₁ : l₁, ...`:
```lean
have h₂₃_prot : l₂.protocol = l₃.protocol := by rw [hl₂, hl₃]; ...
have hprot_diff : l₁.protocol ≠ l₃.protocol := fun h₁₃ => hdiff₁ (h₁₃.trans h₂₃_prot.symm)
exact Or.inl (.obFinishBefore p₁ ... hprot_diff)
```
