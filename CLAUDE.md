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
- **Architecture**: `cmcm_acyclic_of_hknow` uses CLEs from `hknow` directly (`hreq's_dir_access.choose`). The CLE-to-compound_lin bridge was eliminated.
  - **PPOi (single edge)**: `dir_ordered` gives 3-way on CLEs (same-cluster directory events). No compound_lin needed.
  - **COM (single edge)**: `step_to_ordering` gives StepOrdering on CLEs directly. No bridge needed.
  - **Composition**: `compose_three` handles all StepOrdering/eq/reverseOB × PPOi/COM cases.
  - **`cmcm_acyclic_of_hknow` is sorry-free!** Delegates to compose_three.
- **compose_three**: SORRY-FREE. Uses dir_ordered fallback for hard cases (all CLEs are directory events → always resolvable).
- **StepOrdering enriched**: `obEndLt`, `encapObEndLt`, `obFinishBefore` all carry `h_p_isdir`.
- **Non-lazy PPOi**: `h_non_lazy_ppoi` hypothesis excludes lazy RCC.
- **0 sorry-using declarations** in Proof.lean. Proof.lean is sorry-free.
- **Dead code**: CLE-to-compound_lin bridge removed. `ppoi_diff_addr_step_ordering` deleted.

### TODO
1. **RfProofHelpers** (2 sorry-using declarations, 5 live sorry's):
   - **isDirMatchingRW** (scReadDown + noCoherentRead): needs `GCR.req.val.rw = e_r.req.val.rw` lemma (GCR preserves rw through ClusterToGlobal shim)
   - **translatedDir** (noCoherentRead): `clusterDirFromDiffProtocolRequest` requires `proxyCacheEvent` but noCoherentRead has no proxy events. Needs def change.
   - **scReadDown evict** + **noCoherentRead** in cdirEncapsDown: need evict dir event from cluster protocol axiom
2. **Named structures**: Replace `.2.2.2.1.2` tuple access patterns with named structure fields.
3. **Sub-lemma extraction**: Continue decomposing large theorems (799-line `noInterveningWrites_diffCache_sameProtocol_case` is highest priority).

### Lessons learned (BE INTROSPECTIVE!)
- **Don't guess constructors.** Each new StepOrdering constructor multiplies case analysis. Use edge data instead.
- **Information loss is the enemy.** `step_to_ordering` strips rich edge evidence. Keep original edge data available.
- **`by_cases protocol` is the universal first move.** Same → dir_ordered. Diff → .obFinishBefore.
- **Derive equalities BEFORE matches.** After `match hfc : l₁, ...`, rw fails on pre-match hypotheses.
- **Don't expand wildcards without a closure plan.** Creates MORE sorry's.
- **Commit clean states, revert fast** when sorry count increases.
- **`let` bindings block `▸` and `rw`**: In `cmcm_acyclic_of_hknow`, the `let cle` binding prevents `▸` from finding patterns through the expansion. Use `Eq.subst` with explicit motive (`@Eq.subst _ (fun x => ...) _ _ heq h`) instead.
- **dir_ordered is the UNIVERSAL fallback**: All CLEs from `hreq's_dir_access.choose` are directory events (`isDirEvent`). `step_ordering_dir_ordered_3way` resolves ANY pair of CLEs. Use this when StepOrdering composition gets stuck. The CLE-to-compound_lin bridge was ELIMINATED by using CLEs directly + dir_ordered for PPOi.
- **CLE-to-compound_lin bridge is fundamentally flawed**: CLE ordering doesn't always imply compound_lin ordering (for clusterCacheLin + encapDir/orderAfterDir, bounds are reversed). The right approach: use CLEs directly in the cycle invariant.
- **`induction` generalizes indices**: When inducting on `TransGen R a c`, Lean generalizes `c`. Use `_` or `hknow _` to let Lean infer the generalized endpoint.
- **`Trans.trans` for OB chains**: `Event.instTransOrderOrder` handles OB transitivity (chains through `oWellFormed`). Use `Trans.trans h₁ h₂` not `Nat.lt_trans`.
- **Think from the RELATION's perspective, not the event's**: For RF (write→read), the downgrade directory event at the writer's cluster represents the READ side of the communication, NOT a write-back. I got stuck thinking about what the WRITER does (writes back data) instead of what the DIRECTORY EVENT represents (processing the READ request). The `existsRClusterDirDown` should use `isDirRead` because the directory event at the writer's cluster is a read downgrade. **Root cause**: I was reasoning about cache-level operations (write-back) instead of directory-level semantics (processing the incoming read). The directory event's request type matches the INCOMING request (read), not the cache operation (write-back).
- **Use `isDirMatchingRW` (rw-matching) instead of `isDirWrite`/`isDirRead`**: When a definition is used by both RF (write→read) and CO (write→write) relations, don't hardcode `isDirWrite` or `isDirRead`. Instead use `isDirMatchingRW` (`de.req.val.rw = e.req.val.rw`) which adapts to the relation: for RF it requires a read dir event (matching the reader), for CO it requires a write dir event (matching the writer). **This is the SECOND time the user suggested this pattern** — the first time I went through isDirWrite→isDirRead→removing the field entirely before the user pointed out the clean solution. **Root lesson**: when multiple protocol cases need different constraints, find the PARAMETRIC version that captures what the protocol actually does (the dir event's rw matches the request that triggered the downgrade) rather than hardcoding one case.

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
