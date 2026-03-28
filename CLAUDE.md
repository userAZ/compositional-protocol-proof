# Compositional Protocol Proof — Lean 4 Formal Verification

## Philosophy — READ THIS FIRST

**This is a protocol verification project.** The mathematical structures (StepOrdering, TransGen, LinLink) represent REAL protocol communication between cache coherence agents. They are NOT abstract math to be manipulated mechanically.

### The #1 rule: ALWAYS think about what the protocol relations MEAN

Before proving, composing, or sorry-ing ANYTHING:
1. **Ask: what PPOi/rfe/co/fr edge types produce this case?** Each edge has specific protocol semantics (reads-from, coherence order, etc.)
2. **Ask: what events are involved? Are they reads or writes?** FR(e₁,e₂) needs e₁.isRead, e₂.isWrite. Many edge pairs are IMPOSSIBLE at junctions (FR+FR, co+FR, rfe+rfe) because the junction event can't be both read AND write.
3. **Ask: is this case even possible in the protocol?** If not → it's vacuous → prove `exfalso`. Don't waste hours trying to compose something that can't arise.
4. **Use full protocol evidence** (hedge, edge sub-cases, read/write constraints, sameProtocol) in proofs. Don't rely on abstract mathematical composition alone — it loses critical protocol information.

### Key examples
- **FR + FR is IMPOSSIBLE**: e₂ can't be both read and write → edge pair vacuous
- **obFinishBefore + .ob is VACUOUS**: .ob only from same-cluster edges (l₂=l₃), obFinishBefore has l₁≠l₂ → l₁≠l₃ contradicts same-protocol assumption
- **Derive protocol BEFORE matches**: Lean's `match` breaks type bridging. Move protocol derivations before `match hfc : l₁, ...`

### Codebase philosophy
- Definitions validated by Murphi model checking. **Never add new axioms.** Prove from existing definitions.
- Descriptive definitions carry mechanism (WHAT happened), not just consequences. The ordering is DERIVED.
- dir_ordered is model over-strength (orders ALL directory events). Only valid for same-cluster, same-address.

## Rules

1. **Understand first, prove second.** Walk through the proof in text before formalizing.
2. **Read the actual definition.** Grep and read source. Never assume.
3. **Consider all cases.** `dirAccessOfRequest` has 3 cases, `linearizationEventOfRequest` has 2, etc.
4. **Never add new axioms.** Case-split on existing inductive types.
5. **Verify proofs are not vacuous.** Check hypotheses are satisfiable, conclusions nontrivial.
6. **Search the codebase first** before flagging open questions.

## Current goal: Herd CMCM acyclicity proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` in `CMCM/Herd/Proof.lean`.

### Status (updated 2026-03-28)
- **MAIN THEOREM `cmcm_acyclic` IS SORRY-FREE.** Full proof chain: `ppoi_step_to_ordering → co_step_to_ordering → fr_ordering_holds → step_to_ordering → compose_three → compose_obFinishBefore_com → cmcm_acyclic_of_hknow → cmcm_acyclic` — all sorry-free.
- **6 sorry-using declarations** remain in helper lemmas (don't propagate to main theorem).
- **compose_three**: SORRY-FREE. Uses 3-way invariant `StepOrdering ∨ eq ∨ l₃ OB l₁`. Key lemmas: `step_ordering_same_prot_not_reverse`, `same_prot_dir_ordered_forward`, `compose_obFinishBefore_com`.
- **StepOrdering enriched**: `obEndLt`, `encapObEndLt`, `obFinishBefore` all carry `h_p_isdir`. Enables `dir_ordered` on proxy events for temporal chain proofs.
- **Non-lazy PPOi**: `h_non_lazy_ppoi` hypothesis excludes lazy RCC (doesn't preserve A-Cumulativity).
- **ppoi_diff_addr_step_ordering**: Matches on compound linearization directly. clusterDirLin PROVEN. clusterCacheLin has 2 sorry's (1 declaration).

### TODO
1. **ppoi_diff_addr clusterCacheLin sorry's (2 sites, 1 decl)**: For PPOi events: encapDir impossible (¬e.down + reqHasPerms+reqMissingPerms proven contradictory for non-downgrade). orderAfterDir impossible (isNcWeak incompatible with ncReleaseOrAcquireOrCoherent from PPOi). Only orderBeforeDir remains. Start bound CLE.oStart ≤ e.oStart PROVEN for orderBeforeDir. End bound e.oEnd ≤ CLE.oEnd FALSE for orderBeforeDir. Need: compound protocol property that diff-addr PPOi+clusterCacheLin+orderBeforeDir implies CLE₁ OB CLE₂ (not CLE₂ OB CLE₁). See `CompoundPPOs.lean` for compound linearization patterns (line 619+: 4-way match on compound lin types). `enforce_compound_consistency` handles all cases.
2. **co_chain_cross_cluster_downgrade** (1 sorry): `translatedDir` endpoint shift — `clusterDirFromDiffProtocolRequest` preservation through CO chain extension.
3. **RfProofHelpers** (6 sorry's): Shim translation properties.
4. **RfCases** (2 sorry's): `cdirEncapsDown` cluster-level property.

### Lessons learned (BE INTROSPECTIVE!)
- **Don't guess constructors.** Each new StepOrdering constructor multiplies case analysis. Use edge data instead.
- **Information loss is the enemy.** `step_to_ordering` strips rich edge evidence. Keep original edge data available.
- **`by_cases protocol` is the universal first move.** Same → dir_ordered. Diff → .obFinishBefore.
- **Derive equalities BEFORE matches.** After `match hfc : l₁, ...`, rw fails on pre-match hypotheses.
- **Don't expand wildcards without a closure plan.** Creates MORE sorry's.
- **Commit clean states, revert fast** when sorry count increases.

## Detailed documentation (read when needed)
- `docs/compose-three-analysis.md` — Detailed sorry analysis, junction compatibility table, protocol extraction patterns
- `docs/dead-ends.md` — Failed approaches and WHY they failed (proxy protocol, temporal measures, LinLink+EncapBy, etc.)
- `docs/learned-patterns.md` — Reasoning patterns (temporal chains, Lean tricks, protocol patterns, StepOrdering constructors)

## Key reference files
- `CMCM/Herd/Defs.lean` — Herd edge definitions (PPOi, rfe, co, fr), StepOrdering, LinLink
- `CMCM/Herd/Proof.lean` — Main acyclicity proof, compose_three, step_to_ordering
- `CMCM/Herd/Relations.lean` — `com` union, acyclicity def, CMCM theorem
- `CMCM/Rf.lean` — `globalLinearizationEventOfRequest`, RF theorem definition
- `CompositionalProtocolProof/CompoundPPOs.lean` — `CompoundLinearizationOrder`
- `CompositionalProtocolProof/BehaviourRelationDefs.lean` — `dirAccessOfRequest`, `reqHasPerms/reqMissingPerms`
- `CompositionalProtocolProof/EventRelations.lean` — `Encapsulates`, `OrderedBefore`, `DirectoryEvent.AreOrdered`

## Common commands
- `lake build CMCM.Herd.Proof` — build the proof file
- `lake clean` — remove all build artifacts
- `lake build` — build entire project

## Auto-habits
- `/checkpoint` every ~15 min, after milestones, after corrections
- `/learn` after discovering patterns or user corrections — IMMEDIATELY
- `/reflect` every ~20-30 min: am I correct? efficient? going in circles?
- `/philosophy` before major decisions, when stuck
- `/imagine` BEFORE implementing: construct concrete scenarios, check if cases are vacuous
- **Git commit after implementing** — don't wait to batch commits
- **Think about protocol semantics** — always, constantly, before everything
