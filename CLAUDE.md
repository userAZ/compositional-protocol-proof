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

### Status (updated 2026-03-29)
- **Architecture**: `cmcm_acyclic_of_hknow` uses CLEs from `hknow` directly (`hreq's_dir_access.choose`). The CLE-to-compound_lin bridge was eliminated.
  - **PPOi (single edge)**: `dir_ordered` gives 3-way on CLEs (same-cluster directory events). No compound_lin needed.
  - **COM (single edge)**: `step_to_ordering` gives StepOrdering on CLEs directly. No bridge needed.
  - **Composition**: `compose_three` handles all StepOrdering/eq/reverseOB × PPOi/COM cases.
  - **`cmcm_acyclic_of_hknow` is sorry-free!** Delegates to compose_three.
- **compose_three**: SORRY-FREE. Uses dir_ordered fallback for hard cases (all CLEs are directory events → always resolvable).
- **StepOrdering enriched**: `obEndLt`, `encapObEndLt`, `obFinishBefore` all carry `h_p_isdir`.
- **Non-lazy PPOi**: `h_non_lazy_ppoi` hypothesis excludes lazy RCC.
- **Dead code**: CLE-to-compound_lin bridge removed. `ppoi_diff_addr_step_ordering` deleted.
- **`cdirEncapsDown_exists`**: `h_dir_coherent` parameter removed; onDirVd proved inline with consistent e_r_gdown. sameProtocol chain proved via `correspondingCluster_protocol_eq`. Proof.lean call sites cleaned.
- **3 sorry-using declarations** total: `BehaviourHelpers` (Lemma 6 Acquire→Vc), `cdirEncapsDown_exists` (2 sorry's), Proof.lean `fr_ordering_holds` (5 sorry's).
- **`cacheEvent_Vd_transition_isNcWeakWrite`**: SORRY-FREE via ValidRequest Subtype match.
- **`event_Vd_transition_implies_ncWrite_in_b`**: SORRY-FREE.
- **`stateAfter_Vd_implies_exists_ncWrite`**: SORRY-FREE.
- **Proof.lean sorry's (5)**: All in `co_chain_cross_cluster_downgrade` (CO diff-cluster case).

### TODO
1. **`cdirEncapsDown_exists` onDirVd** (2 sorry's in RfProofHelpers): Eliminate `dir_event_properties_from_lin` and `DirectoryEvent.eReq` usage entirely.
   - **Context**: `cdirEncapsDown_exists` constructs the cluster directory downgrade for the diff-cluster case. `e_w` is the writer, `e_r` is the reader, `e_gdown` is the global downgrade at `e_w`'s cluster. The `translateDirectoryEvent` gives onDirVd when directory state at `e_w`'s cluster is Vd.
   - **Why onDirVd is contradictory**: If the directory state is Vd at the time of the downgrade, an NC write must have set it. This NC write is an intervening write between e_w and e_r, violating NIW.
   - **Approach (1)**: `by_cases` on whether there's an intervening write cache event after e_w, before e_gdown. If YES → NIW contradiction. If NO → directory state ≠ Vd (no write modified it from SW), so onDirVd is vacuous.
   - **Approach (2)**: Find an event whose CLE sets the dir state to Vd. Its predecessor at the cache entry is an NC write on Vd cache state (provable by `reverseRecOn` on `eventsUpTo`). Use `cacheEvent_Vd_transition_isNcWeakWrite` for the transition proof. No `DirectoryEvent.eReq` needed.
   - **Key rule**: Use `Event n` with `isDirectoryEvent` prop, NEVER `DirectoryEvent` directly. Don't use `DirectoryEvent.eReq` — use CLE/lin infrastructure instead. Match existing Behaviour proof patterns.
   - **ALWAYS document WHY a sublemma exists**: what protocol argument it serves, what terms it uses (e_w, e_gdown, CLE_r, etc.).
2. **Proof.lean sorry's (5)**: All in `co_chain_cross_cluster_downgrade`. 2× `downIsDown`, 2× cdir OB CLE_w, 1× diff-cluster chain.
3. **BehaviourHelpers Lemma 6 Acquire→Vc**: Separate, independent sorry.

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
- **State→Event bridge needs protocol axioms**: `List.stateAfter` tracks entry states (EntryState = State ⊕ DirectoryState). Directory events have `eReq : CacheEvent` but proving `eReq ∈ b` requires `cacheEncapsulatesCorrespondingDirEvent.reqInB` which needs CompoundProtocol. Similarly, cache events at directory entries need `isClusterCache` which requires knowing the struct is cluster-level. Don't try to bridge state-level facts to event-level conclusions without protocol axioms in scope.
- **`Trans.trans` for OB chains**: `Event.instTransOrderOrder` handles OB transitivity (chains through `oWellFormed`). Use `Trans.trans h₁ h₂` not `Nat.lt_trans`.
- **Think from the RELATION's perspective, not the event's**: For RF (write→read), the downgrade directory event at the writer's cluster represents the READ side of the communication, NOT a write-back. I got stuck thinking about what the WRITER does (writes back data) instead of what the DIRECTORY EVENT represents (processing the READ request). The `existsRClusterDirDown` should use `isDirRead` because the directory event at the writer's cluster is a read downgrade. **Root cause**: I was reasoning about cache-level operations (write-back) instead of directory-level semantics (processing the incoming read). The directory event's request type matches the INCOMING request (read), not the cache operation (write-back).
- **Use `isDirMatchingRW` (rw-matching) instead of `isDirWrite`/`isDirRead`**: When a definition is used by both RF (write→read) and CO (write→write) relations, don't hardcode `isDirWrite` or `isDirRead`. Instead use `isDirMatchingRW` (`de.req.val.rw = e.req.val.rw`) which adapts to the relation: for RF it requires a read dir event (matching the reader), for CO it requires a write dir event (matching the writer). **This is the SECOND time the user suggested this pattern** — the first time I went through isDirWrite→isDirRead→removing the field entirely before the user pointed out the clean solution. **Root lesson**: when multiple protocol cases need different constraints, find the PARAMETRIC version that captures what the protocol actually does (the dir event's rw matches the request that triggered the downgrade) rather than hardcoding one case.
- **`grantRels` was a false shortcut (REVERTED)**: The old `encapGrantAfterDirEvent` had contradictory fields. After the user fixed it (grant is last encapsulated event: `e_grant.oEnd + 1 = e_req.oEnd`), those exfalso proofs broke. **Lesson**: never use axiom artifacts to close cases — always reason about what the protocol actually does.
- **Axiom structure encoding creates vacuity traps**: Axioms like `nonCohReqDowngrades` embed preconditions (e.g., `reqDirOnSW : state = SW`) as FIELDS rather than guards. When preconditions fail (state = Vd ≠ SW), the structure is uninhabitable → axiom vacuously True → field extraction gives False. This is the SAME pattern as grantRels. **Always check**: is the axiom structure genuinely inhabited for the specific events you're applying it to? If any field is False for your inputs, the extraction is vacuous.
- **Dir state coherence from `dirAccessOfRequest`**: To prove dir state ≠ Vd (e.g., `onDirVd` vacuous), case-split on e_w's `dirAccessOfRequest`: `encapDir` → coherent request → dir at SW; `orderBeforeDir` → predecessor had perms, `hinter_leaves_state_at_least` prevents any intermediate event from downgrading coherent perms, so if anything changed dir to Vd it would have violated the state preservation; `orderAfterDir` → NC weak on Vd (implies NC weak READ, likely contradicts e_w.isWrite at call sites). Key insight: "if another access changed the directory to Vd, it would have downgraded the orderBeforeDir's coherent write permissions" — the `hinter_leaves_state_at_least` constraint is the proof mechanism.
- **`isDirDownRW` replaces `isDirMatchingRW`**: Inductive with `readDown` (dir rw=.r) and `writeDown` (dir rw=.w, Vd writeback). Provable by case-splitting on dir event's rw. The old `isDirMatchingRW` (exact equality with CLE) was unprovable in `noGlobalCache` case because CLE.rw comes from a predecessor that could be a write.
- **`Vd ≤ SW` is TRUE** (same perms `some .wr`, different coherence `false ≤ true`). Cannot derive dir ≠ Vd from simple `≤` comparison with SW cache. Need coherence BIT argument: coherent perms require `c=true`, Vd has `c=false`.
- **Write code first, analyze later.** When facing a sorry, just try to fill it with code, build, iterate. Don't write paragraphs theorizing about feasibility. Most sorry's are mechanical once you start writing.
- **Match on ValidRequest (Subtype), not on individual fields**: `RequestState`/`DowngradeState`/`MRS` match on the full `ValidRequest` Subtype `⟨⟨rw, coh, con⟩, hv⟩`, NOT on individual fields. Matching on `ce.req.val.rw`, `ce.req.val.coherent` etc. separately doesn't give Lean enough info to reduce the Subtype match. **Fix**: `match hvr : ce.req with | ⟨⟨.w, false, .Weak⟩, _⟩ => ...` then `rw [hvr] at hs_Vd` to substitute before `simp [ValidRequest.RequestState]`. Lean uses `IsValid'` for exhaustiveness — invalid request patterns (like `⟨_, false, .SC⟩`) are auto-excluded.
- **`simp only` vs `simp` for `if` reduction**: `simp only [...]` does NOT include `ite_true`/`ite_false`, so `if True then x else y` won't reduce. Use `simp [...]` (without `only`) to include default simp lemmas, or add `ite_true`/`ite_false` explicitly.
- **Read definitions immediately, don't guess.** `reqToDirOfRequestEvent` is 5 lines — read it instead of speculating about what it does. `grep -rn 'def ...'` is faster than reasoning from names.
- **Search the codebase aggressively for existing lemmas.** Key finds: `directory_event_is_bottom`, `bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents`, `eventsUpToEvent_ordered_before_sorted`, `eventsUpToEntry_at_e_entry`. Always search before writing new code.
- **Extract helper lemmas proactively for heartbeat management.** `dirEvent_down_true_ne_Vd_of_ne_Vd` extraction solved a timeout. `list_stateAfter_exists_transition_with_inv` carried the invariant cleanly. Don't let proofs grow past ~30 lines without extracting.
- **NEVER use `DirectoryEvent` directly or `DirectoryEvent.eReq`**: Use `Event n` with `isDirectoryEvent` prop, matching the rest of the codebase. The `eReq` field has NO axioms linking it to the dir event's properties (no sameProtocol, no sameDown, no Encapsulates). Use CLE/lin infrastructure instead to get corresponding cache events with full protocol properties via `cacheEncapsulatesCorrespondingDirEvent.dirCorresponds`. I wasted an entire session going down the `eReq` rabbit hole.
- **ALWAYS document WHY a sublemma exists**: Write the protocol argument (e.g., "onDirVd is contradictory because an NC write between e_w and e_gdown violates NIW") BEFORE writing code. Include key terms (e_w, e_gdown, CLE_r, etc.). Without this, context is lost across sessions and you go in circles.
- **Add all needed hypotheses upfront, prune later.** When writing a lemma, aggressively add protocol hypotheses from the call site context. It's easy to remove unused params; it's painful to discover mid-proof that a hypothesis is missing. The `h_dir_req`, `h_eReq_in_b`, `h_cle_is_de`, `h_ncRead_prior_write`, `h_not_global`, `h_s_dir` parameters to `event_Vd_transition_implies_ncWrite_in_b` should have been added in the first draft.
- **`by_cases` on Bool fields is powerful.** `by_cases hisW : de_trans.eReq.req.val.isWrite` cleanly splits NC-read-on-Vd from NC-write cases. `by_cases hevict_down : e_evict.down` cleanly splits `sameCacheConstraints` vs `sameCacheWriteConstraints`.
- **Temporal chains through encapsulation**: `Encapsulates.2` gives `inner.oEnd < outer.oEnd`. Chain with `finishesBefore.endBefore` and `gcache_oEnd_lt_cle` for full CLE temporal bounds.
- **`list_stateAfter_exists_transition_with_inv`**: When the plain `list_stateAfter_exists_transition` loses context (like `s.isDirectoryState`), use the invariant-preserving variant. The invariant `Q` is preserved through the induction and returned with the transition evidence.
- **NC read on Vd → prior NC write**: If a `reqToDirOfRequestEvent` transforms a NC read (Acq/Weak) on Vd cache state to a Weak Write at the dir level, the cache event is a READ, not a write. The actual NC write is a PRIOR event that left the cache at Vd. Use `h_ncRead_prior_write` to delegate to the caller.

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
- `/protocol-proof` BEFORE and DURING implementing any sorry or writing/updating Lean definitions. Think about what the protocol actually does. Check existing Behaviour/proof files for reusable patterns.
- `/checkpoint` every ~15 min, after milestones, after corrections
- `/learn` after discovering patterns or user corrections — IMMEDIATELY
- `/reflect` every ~20-30 min: am I correct? efficient? going in circles?
- `/philosophy` before major decisions, when stuck
- `/imagine` BEFORE implementing: construct concrete scenarios, check if cases are vacuous
- **Git commit after implementing** — don't wait to batch commits
- **Think about protocol semantics** — always, constantly, before everything
