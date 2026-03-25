# Compositional Protocol Proof — Lean 4 Formal Verification

## Project

Formal verification of compositional cache coherence protocols in Lean 4. The codebase proves properties about compound memory consistency models (CMCM), including PPO enforcement (`CompoundLinearizationOrder`), the RF theorem (`readsFrom`), and the Herd CMCM (`acyclic(PPOi ∪ rfe ∪ fr ∪ co)`).

## Philosophy

This codebase is believed to be **complete** — the existing protocol "axioms" are definitions validated by Murphi model checking, and the proof framework is self-supporting. **Never add new axioms or protocol-level fields.** Always prove from existing definitions by case-splitting on inductive types and using existing lemmas.

Use this CLAUDE.md as a living scratchpad: record new reasoning patterns, debugging approaches, lessons learned, and key findings here so they can be reused efficiently. Be introspective — when you learn something new from the codebase or from Anqi's corrections, add it here immediately. Re-read this file before starting work to avoid re-deriving things from scratch.

## Rules

### Before writing any proof code

1. **Understand first, prove second.** Lay out: (a) the precise statement, (b) the proof approach, (c) required definitions and sub-lemmas, (d) open questions. Walk through the proof in text before formalizing.

2. **Analyze tradeoffs of lemma formulations.** Lay out 2–3 candidates with their hypotheses, conclusions, and how they compose with the rest of the proof. Choose the formulation that minimizes proof obligations.

### When reasoning about definitions and claims

3. **Read the actual definition.** Before claiming "X always does Y," grep for and read the source definition. Cross-reference with related definitions. The RF linearization definition (`globalLinearizationEventOfRequest`) is structurally different from the PPO compound linearization (`ClusterRequestLinearizationEvent`). Never assume they're the same — verify.

4. **Verify claims independently.** Do not ask the user to confirm something that can be checked by reading code. Navigate to the source, trace the data flow, and verify structurally.

5. **Consider all cases and the contrapositive.** Try to construct a counterexample, consider the contrapositive, examine all cases, and distinguish formal/structural claims from semantic/protocol-level claims.

### When investigating open questions

6. **Search the codebase first.** Before flagging something as an "open question," search existing proofs, axioms, and lemmas — especially the RF theorem proof, protocol axioms, and `CompoundPPOs.lean`.

7. **Remember key definitions with multiple cases.** `dirAccessOfRequest` has three cases (`encapDir`, `orderBeforeDir`, `orderAfterDir`). `linearizationEventOfRequest` has two cases (`requestLin`, `dirLin`). `clusterDirectoryLinearizationEvent` has two cases (`previousGlobalCacheGotPerms`, `getGlobalCachePerms`). Always consider all cases.

### When writing proofs

8. **Never add new axioms.** Always prove theorems from existing protocol definitions — case-split on existing inductive types and use existing transitivity/encapsulation lemmas rather than introducing new axioms or fields.

9. **Ensure definitions are not vacuous.** Verify hypotheses are satisfiable and conclusions are nontrivial.

10. **Read comments and docstrings.** The codebase has important annotations (e.g., Rf.lean:82-83 warns that GLE terms differ from PPO linearization events).

11. **Test carefully.** When a proof compiles, check it actually proves what was intended — verify the statement, hypotheses, and that the proof isn't vacuous.

12. **Verify implementation matches what was asked AND the philosophy.** After implementing ANY proof or definition, stop and check: does the code ACTUALLY do what the user described? Does it match the project philosophy (descriptive definitions carrying mechanism, not just consequence)? A proof that compiles but contradicts the stated approach is WRONG. Tests passing ≠ correct implementation.

13. **Use imagination to sanity-check ideas.** When the user suggests an approach, use `/imagine` to check: does this make sense? Is there a scenario where it breaks? Is there a subtle bug? Construct concrete counterexamples before coding. If an idea has a flaw, catch it BEFORE implementing.

14. **Verify implementation is correct.** Separate from matching philosophy: proofs can match the design but be vacuous or prove the wrong thing. Check statements, hypotheses, and conclusions against concrete examples.

15. **Use your experience, reference files, and skills to solve problems independently.** You have: imagination (construct scenarios), philosophy (question foundations), CLAUDE.md (accumulated knowledge), prior code examples (Rf.lean, CompoundPPOs.lean, EventRelations.lean), and the user's cycle examples. Use ALL of these to work through complex proofs without stopping to ask.

16. **Check that ideas are sound before implementing.** Before coding, ask: is this approach actually correct? Does it have a subtle bug? Example: `finishesBefore` (e₁.oEnd < e₂.oEnd) seemed correct but fails for orderAfterDir — the nc.weak reader finishes before the writer. Caught by imagination (construct a concrete timeline). ALWAYS imagine concrete scenarios BEFORE implementing to catch bugs in the approach itself.

## Current goal: Herd CMCM acyclicity proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` in `CMCM/Herd/Proof.lean`.

### Status (updated 2026-03-24, late session)
- **Main proof architecture**: `cmcm_acyclic` → `cmcm_acyclic_of_hknow` → StepOrdering
  - `step_to_ordering`: maps each PPOi ∪ com edge to `StepOrdering CLE₁ CLE₂`
  - `StepOrdering.trans`: composes edges (FULLY PROVEN, 0 sorry's)
  - `StepOrdering.irrefl`: cycle gives contradiction (FULLY PROVEN, 0 sorry's)
  - Old lex pair approach (`step_advances`, `co_step_advances`) DELETED — failed for PPOi orderAfterDir
- **StepOrdering**: 3 constructors: `ob` (CLE₁ OB CLE₂), `obEncap` (CLE₁ OB p, p EncapsulatedBy CLE₂), `sameLin` (CLE₁ = CLE₂ with encapsulating events ordered)
- **Edge definitions**: DONE (Defs.lean)
- **Irreflexivity**: DONE for all edge types
- **write_event_cle_isDirWrite**: FULLY PROVEN (all 3 dirAccessOfRequest cases, in RfProofHelpers.lean)
- **reqToDir_preserves_write_of_coherent/on_vd_ncrel**: moved to RfProofDefs.lean
- **14 sorry's remain** in `step_to_ordering` — see categories below

### Key insight: `hierarchicallyOrdered` IS `CompoundLinearizationOrder` (same concept)

`CompoundLinearizationOrder` says: PPO events linearize at specific points in the hierarchy (cache, CLE, or GLE level), and their linearization points are ordered. `hierarchicallyOrdered` says: events are ordered at the highest differing level (GLE, CLE, cache). **These are the same concept** — both ask "where does this event meet the protocol hierarchy, and what's the order at that meeting point?"

The "GMO bridge" is NOT a separate thing — it's recognizing they're the same. There's no gap to bridge. The compound linearization event for each request IS its position in the (GLE, CLE, cache) hierarchy.

**CONSEQUENCE**: `hierarchicallyOrdered` should carry communication evidence (like `readsFrom.cases` does for RF), not just abstract ordering proofs. Each edge type provides its OWN communication evidence:
- **PPOi**: uses `CompoundLinearizationOrder` from CompoundMCM (proven in CompoundPPOs.lean)
- **RF**: uses `readsFrom.cases` (downgrade chains, noBetween)
- **CO**: uses `co.cases` (overwrite communication pattern)
- **FR**: uses rf⁻¹ ; co composition (noBetween ensures validity)

The GLE/CLE/cache lex ordering falls out as a CONSEQUENCE of this communication evidence, used for irrefl/trans.

### Remaining sorry's (all in `step_to_ordering`, updated 2026-03-24 late)

**Category 1: gcacheEncap → EncapsulatedBy CLE (5 sorry's)**
- `encapDirRelation.gcacheEncap` gives GCR encaps cdir_down. Need CLE encaps cdir_down.
- **Resolution**: CLE encaps GCR (from `encapGlobalCache` shim, via `clusterDirEncapCorrespondingGlobalCache.encapGlobalCache`). Then `Event.encap_encap_trans` gives CLE encaps cdir_down.
- The `noGlobalCache` shim case should NOT produce `gcacheEncap` — it produces `cleEncap` (CLE directly handles cluster-level downgrade when it already has global perms).
- **Approach**: case-split on `cmp.shimAxioms.clusterToGlobal` to extract `encapGlobalCache`, then transitivity.

**Category 2: PPOi → StepOrdering (1 sorry)**
- Need to map PPOi(e₁, e₂) to StepOrdering CLE₁ CLE₂.
- For encapDir × encapDir: `.ob` (CLE₁ inside e₁ OB e₂ inside CLE₂ → CLE₁ OB CLE₂).
- For same CLE (nc.weak sharing): `.sameLin`.
- For orderAfterDir: CLE₁ = CLE₂ must be PROVEN (nc.weak CLE sharing insight).

**Category 3: co sameCache non-encapDir (4 sorry's)**
- Same CLE → need `.sameLin` with CLE inside two ordered events.
- For orderBeforeDir: CLE inside predecessor. For orderAfterDir: CLE inside successor.
- Key issue: finding two events that BOTH encapsulate the shared CLE and are ordered.

**Category 4: rfe noEvictBetween orderAfterDir (1 sorry)**
- nc.weak e₁ with wHasPermsAfter → contradiction (nc.weak can't leave ≥ SW state).

**Category 5: fr cross-cluster (3 sorry's)**
- `notBetweenCles` needs sameProtocol. For cross-cluster: need `diffClusterNotBetweenCles_sameCache`.

**Sorry #1 (line ~538): PPOi, e₂ encapDir, e₁ orderAfterDir, CLE₂ OB CLE₁**
- nc.weak e₁ with CLE₁ from successor. Successor succ₁ encaps CLE₁ (de₁).
- Need: show succ₁ OB e₂ (then de₁ OB de₂ → contradicts hob) or CLE₁ = CLE₂.
- Approach: nc.weak CLE sharing — if succ₁ = e₂ or succ₁ OB e₂, de₁ inside succ₁ gives de₁.oEnd < succ₁.oEnd < e₂.oStart < de₂.oStart → de₁ OB de₂ contradiction.
- Missing: formal proof that succ₁ is before or equals e₂ on same cache (needs cache event total ordering + immediacy argument).

**Sorry #2 (line ~541): PPOi, e₂ orderBeforeDir, CLE₂ OB CLE₁ (all e₁ sub-cases)**
- pred₂ encaps CLE₂ (de₂), pred₂ OB e₂.
- Approach: if e₁ OB pred₂ → de₁.oEnd < e₁.oEnd < pred₂.oStart < de₂.oStart → de₁ OB de₂, contradicts hob.
  If pred₂ OB e₁ → e₁ between pred₂ and e₂ → predecessor elimination: e₁ satisfies P (reqHasNoPermsLeavesStateAtLeast from stateBeforeAndAfterAtLeast + reqMissingPerms) → contradicts noIntermediateSatisfyingP.
- Missing: cache event total ordering between e₁ and pred₂, plus verification that encapDir e₁ satisfies P.

**Sorry #3 (line ~575): PPOi, both orderAfterDir, CLE₂ OB CLE₁**
- Both e₁ and e₂ are nc.weak with CLEs from successors. Both successors on same cache.
- Approach: nc.weak CLE sharing — both should share CLE or have CLE ordering following cache order. If succ₁ encaps de₁ and succ₂ encaps de₂, and succ₁ OB succ₂ (or succ₁ = succ₂), then de₁ OB de₂ or de₁ = de₂.
- Missing: same as #1 + relating two successors on same cache.

**Sorry #4 (line ~695): rfe noEvictBetween, e₁ orderAfterDir, de_cdir OB de_w**
- Same structure as #1: nc.weak e₁ with CLE from successor, de_cdir OB CLE₁.
- Approach: show succ₁'s position relative to the downgrade chain gives temporal contradiction.
- Missing: formal proof that orderAfterDir successor position excludes de_cdir OB CLE₁.

**Sorry #5 (line ~783): fr, de_w OB de₂ OB de₁ with NoInterveningWrites**
- CLE₂ between CLE_w and CLE₁. Need to apply NoInterveningWrites to e₂.
- Approach: `h_no_between` gives `NoInterveningWrites.constraints` for e₂ (if e₂ ∈ b, isClusterCache, isWrite, ¬down). Then `notBetweenCles` says CLE₂ NOT between CLE_w and CLE₁ (if same protocol + isDirWrite). Contradicts de_w OB de₂ OB de₁.
- Missing: (1) extract e₂ ∈ b, isClusterCache, ¬down from fr/co evidence; (2) verify same-protocol condition; (3) verify isDirWrite for CLE₂; (4) handle cross-cluster case with `diffClusterNotBetweenCles`.

**CRITICAL INSIGHT (2026-03-24): For PPOi + orderAfterDir, CLE₁ = CLE₂ must be PROVEN, not assumed.**

The lex pair approach assumes CLE.oEnd monotonically advances along each edge. But for PPOi with e₁ having `orderAfterDir`, CLE₁ comes from a SUCCESSOR of e₁ (after e₂), so CLE₂ OB CLE₁ is the natural ordering. The lex pair goes BACKWARDS — this is NOT a contradiction to derive `False` from.

The fix: prove `CLE₁ = CLE₂` for same-address PPOi with e₁ `orderAfterDir`. This routes through the `by_cases hcle_eq` equality case (secondary advance via e₁ OB e₂). The protocol reason: nc.weak's `dirAccessOfRequest.orderAfterDir` gives CLE₁ from the successor's directory write-back, which for same-address PPOi IS the same directory event as e₂'s `encapDir` CLE₂.

**Proof sketch**: Show `immBottomSuccOnVdEncapCorrDir` successor for nc.weak e₁ produces the SAME `e_dir` as e₂'s `cacheEncapsulatesCorrespondingDirEvent`. For same-address events on same cache, there's one directory entry and one write-back per release sequence.

**Common needs for sorry's #1-4**: `cache_ordered` (Behaviours.lean:21) gives total ordering for cache events, but needs `CacheEvent` extraction from `Event` (pattern match on `.cacheEvent ce`). For `ImmediateBottomPredSatisfyingProp` → predecessor elimination, need `stateBeforeAndAfterAtLeast` fields from `orderBeforeDir`. For sorry's #1 and #3 (orderAfterDir): proving CLE₁ = CLE₂ is the CORRECT approach, not temporal contradiction.

### Key insight: communication events (downgrades) are the fundamental mechanism

The hierarchy ordering (GLE/CLE/cache) is a CONSEQUENCE of communication events, not the mechanism itself. For each relation:

- **RF(e_w, e_r)**: A downgrade from e_r's cluster reaches e_w's cache at some common level (cache/CLE/GLE). The downgrade makes e_w write back its value → e_r reads it. The downgrade is AFTER e_w and INSIDE e_r's CLE/GCR. GLE ordering falls out of this chain.
- **CO(e_w1, e_w2)**: e_w2 sends a downgrade to e_w1 at some common level. Same mechanism.
- **FR(e₁, e₂)**: COMPOSITION of two communication events through intermediate e_w:
  1. rf(e_w, e₁): downgrade from e₁ to e_w at level L₁ (how e₁ reads e_w's value)
  2. co(e_w, e₂): downgrade from e₂ to e_w at level L₂ (how e₂ overwrites e_w)
  The `noBetween` condition from RF ensures the composition is valid.

### NEEDED: Custom TransGen (ProtocolChain) for acyclicity proof

Standard TransGen + per-edge measures DON'T WORK (oEnd dead end).
Need custom inductive `ProtocolChain` with DESCRIPTIVE constructors for each
communication level junction (like RF's verbose inductives).

**Two communication levels**:
1. **Cluster cache level**: e_w OB e_r_down (from existsRDownAtW)
2. **Cluster directory level**: CLE₁ OB CLE₂ (from co.cases CLE ordering)

**Constructor cases** (PPOi↔COM junctions at each level):
- ppoi_to_cache_com: PPOi gives e₁ OB e₂, COM gives e₂ OB e_r_down
- ppoi_to_dir_com: PPOi gives e₁ OB e₂, COM gives CLE₂ OB CLE_next
- cache_com_to_ppoi: e_r_down inside e₃ (EncapsulatedBy), PPOi gives e₃ OB e₄
- dir_com_to_ppoi: CLE inside e₃ (EncapsulatedBy), PPOi gives e₃ OB e₄
- COM↔COM: similar junctions at each level
- trans: compose chains

Each gives strict oEnd increase on SPECIFIC protocol events.
A cycle loops: X.oEnd < ... < X.oEnd. Contradiction.

### THE APPROACH: OB between protocol events in COM relations

**The COM relations (rfe, co, fr) order specific protocol events via OrderedBefore.**
- rfe: e_w OB e_r_down (write before downgrade at common level)
- co: e_w₁ OB e_w₂_down (first write before overwrite downgrade)
- fr: composition via rf⁻¹;co through intermediate write

**The acyclicity proof chains these OB's across edges in a cycle.**
Each edge gives OB between specific protocol events (e_w, e_r_down, e_r_cdir_down, CLE).
EncapsulatedBy connects the output of one edge to the input of the next.
A cycle forms a loop: X.oEnd < ... < X.oEnd — contradiction.

**Per-edge measures (e.oEnd, finishesBefore) AND per-edge OB on cache events DO NOT WORK.**
OB between cache events fails: reader can start before writer finishes (sends request to directory early). Only OB between PROTOCOL EVENTS (e_w OB e_r_down, CLE₁ OB CLE₂) holds.
The transitive relation must carry the encapsulation evidence (e_r_cdir_down encaps e_r_down) that bridges cluster cache and cluster directory levels.

**CROSS-EDGE COMPOSITION IS REQUIRED**: The proof cannot use per-edge temporal properties. It must compose OB on protocol events ACROSS consecutive edges. The composition at PPOi↔COM junctions uses EncapsulatedBy + OB → OB (Trans instances). The key compositions:
- PPOi(e₁,e₂) then COM(e₂,e₃): e₁ OB e₂ Encapsulates protocol_events OB ... inside e₃
- COM(e₁,e₂) then PPOi(e₂,e₃): protocol_events inside e₂, e₂ OB e₃
The encapsulation bridge (cdirEncapsDown) connects cluster cache and directory levels within each COM edge. The composition uses the fact that protocol events are EncapsulatedBy cache events (or past them for orderAfterDir, in which case the chain goes through the successor).
The chain goes through PROTOCOL events, not cache events.
The proof MUST compose across edges.

### DEAD END: lex pair (CLE.oEnd, e.oEnd) for acyclicity
The `step_advances` approach with `(CLE.oEnd, e.oEnd)` as a lex pair FAILS for PPOi + orderAfterDir. For nc.weak events, the CLE comes from a SUCCESSOR (after e₂), so CLE₂ OB CLE₁ is the natural ordering — the lex pair goes BACKWARDS. Deleted in commit `b9e58ec`.

### DEAD END: obEndLt (weakening obEncap to oEnd < oEnd)
Weakened `obEncap`'s `EncapsulatedBy` to just `p.oEnd < l₂.oEnd` to handle `gcacheEncap`. This was WRONG — `gcacheEncap` should give full `EncapsulatedBy` via shim transitivity (CLE encaps GCR encaps cdir_down → CLE encaps cdir_down). The weakening was unnecessary and lost structural information. Reverted in commit `f272fa8`.

**Key insight**: In the `gcacheEncap` case, the GCR is from `encapGlobalCache` shim (CLE encapsulates GCR to get global permissions). The `noGlobalCache` case produces `cleEncap` instead (CLE directly handles the downgrade since it already has global perms). So `gcacheEncap` ALWAYS has CLE encaps GCR available.

### DEAD END: ALL per-edge temporal properties for acyclicity

**e₁.oEnd < e₂.oEnd (finishesBefore)**: FAILS for orderAfterDir (CLE past target) and co diff-cache (slow grant on first write makes e₁.oEnd > e₂.oEnd).

**e₁ OB e₂ (OrderedBefore on cache events)**: FAILS for cross-cluster COM (reader starts before writer finishes — sends request to directory early).

**CLE₁ OB CLE₂**: FAILS for same-CLE PPOi (CLE₁ = CLE₂, no ordering).

**NO per-edge temporal property works for ALL edge types.** The proof MUST use the custom cross-edge composition with protocol events (e_r_down, e_r_cdir_down, CLE) and the encapsulation bridge (cdirEncapsDown).

### DEAD END (subsumed): oEnd-based arguments for acyclicity

**oEnd values (cache event oEnd) CANNOT prove acyclicity for orderAfterDir cycles.**
Concrete counterexample to oEnd monotonicity:
- Cycle: e₁ →(PPOi)→ e₂ →(rfe)→ e₃ →(co)→ e₄ →(PPOi)→ e₁
- e₃ has orderAfterDir. oEnd values: B₃ < A₄ < A₁ < A₂ < CLE(e₃).oEnd
- All oEnd values are consistent — NO contradiction from oEnd alone!
- The contradiction must come from PROTOCOL PROPERTIES, not temporal oEnd ordering.

This applies to ALL oEnd-based approaches: finishesBefore, per-edge e.oEnd, max(e.oEnd, CLE.oEnd), cross-edge composition.

### Anqi's cycle examples (KEY — use these as the proof template!)

**Example 1**: e₁ PPOi e₂, e₂ Rfe e₃, e₃ Fr e₁ (nc.weak write + nc.rel write + coherent read)
- CLE₁ = CLE₂ (nc.weak shares CLE with PPO successor)
- Rfe: CLE₂ OB e_r_cdir_down (downgrade after CLE₂)
- Fr: e_r_cdir_down OB CLE₁ (downgrade reads from prior write, so before CLE₁)
- Chain: CLE₁ = CLE₂ OB e_r_cdir_down OB CLE₁. Loop on CLE₁!

**Example 2**: e₁ PPOi e₂, e₂ Rfe e₃, e₃ Fr e₁ (e₁ encaps CLE, e₂ has perms)
- PPOi: CLE₁ OB e₂ (e₁ lins at CLE, e₂ lins at cache because e₁ got perms)
- Rfe: e₂ OB e_r_down (write before downgrade at e₂'s cache)
- e_r_cdir_down encaps e_r_down
- Fr: e_r_cdir_down OB CLE₁
- Chain: CLE₁.oEnd < e₂.oEnd < e_r_down.oEnd < e_r_cdir_down.oEnd, and e_r_cdir_down.oEnd < CLE₁.oStart ≤ CLE₁.oEnd
- So: CLE₁.oEnd < e_r_cdir_down.oEnd < CLE₁.oEnd. Contradiction!

**Key insight**: The chain goes through SPECIFIC protocol events (CLE, e_r_down, e_r_cdir_down), NOT cache event oEnd. The contradiction is on a SPECIFIC protocol event (CLE₁) that loops. The proof traces OB on these protocol events, NOT oEnd on cache events.

### How the acyclicity proof works (no ranking needed!)

**The cycle contradiction chains SPECIFIC OB relationships between protocol events:**

Example cycle: e1 PPOi e2, e2 Rfe e3, e3 Fr e1 (all same address).
- PPOi: CLE1 OB e2 (e1 lins at CLE, e2 lins at cache)
- Rfe: e2 OB e_r_down, e_r_cdir_down encaps e_r_down (write before downgrade)
- Fr: e_r_cdir_down OB CLE1 (the cluster dir downgrade is before e1's CLE — FR MUST carry this!)

Chain: CLE1 OB e2 OB e_r_down (inside e_r_cdir_down) OB CLE1 → CLE1 OB CLE1. Contradiction!

**Each edge provides:**
- **PPOi**: lin(e1) OB lin(e2) — linearization events at whatever level they land
- **Rfe**: e_w OB e_r_down, e_r_cdir_down encaps e_r_down, e_r_cdir_down inside CLE(e_r)/GCR(e_r)
- **CO**: similar downgrade structure (e_w1 OB downgrade inside e_w2)
- **FR**: carries e_r_cdir_down and its OB with target CLE — NOT just e_r_down!

**The proof composes these using Trans instances** (EncapsulatedBy → OB → OB, etc.) to build a temporal chain that loops back, contradicting OB irreflexivity.

### Design principle: descriptive definitions (like RF's inductives)

**Definitions should be descriptive (carry mechanism), not just prescriptive (carry consequence).**

RF's `readsFrom.cases` is the gold standard: it carries the SPECIFIC communication events (e_r_cdir_down, noBetween, temporal chain), not just "GLE₁ OB GLE₂." The ordering is a CONSEQUENCE visible in the structure.

**`hierarchicallyOrdered` must follow this pattern.** Each constructor carries BOTH:
1. **Communication evidence**: the specific protocol events (downgrades at common levels, PPOi compound linearization events)
2. **Ordering consequence**: the eventLt-style ranking decrease (GLE OB, CLE OB, or cache OB)

These aren't separate — the ordering IS derived from the communication. Having both makes the definition self-documenting for reviewers.

**The PartialOrder** is built from the communication events themselves (the concrete downgrades), with properties (irrefl, trans) proven via the eventLt ranking embedded in each constructor.

**Apply everywhere**: CO should carry specific downgrade communication (not just abstract `co.cases`). FR should carry rf⁻¹;co decomposition with specific events. PPOi should carry CompoundLinearizationOrder evidence.

### Reviewer concerns / vacuity checks

**Always verify proofs are not vacuous.** A proof that exploits single-address model quirks (e.g., all dir events share address → different addresses impossible) does NOT convince reviewers that the right thing was proven. Specifically:
- `ppoi_hierarchicallyOrdered_diff_addr`: Currently vacuous. MUST use CompoundMCM's `enforce_compound_consistency` to give a real proof via CompoundLinearizationOrder.
- All edge-type proofs should use the actual communication evidence, not shortcuts.

### Strategy: PPOi hierarchical linearization points + linking def/lemma to Com edges

**KEY INSIGHT (from Anqi):** PPOi events have **hierarchical linearization points**. For example, a coherent SC write linearizes at cache if it has coherent write permissions. The communication edges (rfe/fr/co) then pick up from those linearization points. The RF theorem covers the bridge: an SC write with/that got coherent perms gets a downgrade when a read from another cluster occurs after it in GLE (or CLE after from same cluster, different cache).

**Approach:**
1. Use **CompoundMCM** PPOi definition and **RF/FR/CO linearization orderings** as building blocks
2. Define a **linking/bridging definition** that connects WHERE a PPOi event linearizes (its hierarchical linearization point) to WHERE the next com edge (rfe/fr/co) communicates
3. Prove the linking def is satisfiable (the def "makes sense")
4. The acyclicity proof composes: PPOi linearization → linking def → com edge ordering → contradiction

**The linking def bridges between:**
- PPOi's `CompoundLinearizationOrder` (compound linearization events — cache or directory level)
- Com's linearization orderings (rfe uses `readsFrom.cases`, co/fr use `gleOrdering.Cases`)

The key: communication is **implicit** beyond the linearization point. The RF theorem already handles this — if the SC write has or got permissions, a subsequent read from another cluster sends a downgrade to the write's cache, establishing GLE ordering.

**KEY DESIGN DECISION (2026-03-23): CO and FR carry Prop-valued communication ordering, not Type-valued or hierarchy directly.**

CO and FR now carry `co.cases` — a Prop-valued inductive mirroring `readsFrom.cases` with `sameGle`/`wObRGle` cases, reusing RF's Prop-valued sub-types where possible. This replaces the old `Nonempty(gleOrdering.Cases)` approach.

**Implementation (2026-03-23):**
- `co.cases` and `co.sameGle.cases` — Prop-valued inductives in `CMCM/Herd/Defs.lean`
- CO structure carries `ordering : co.cases w₁_lin w₂_lin`
- FR carries BOTH the rf⁻¹ ; co⁺ witness (decomposition) AND `ordering : co.cases e₁_lin e₂_lin` (direct hierarchy)
- The `co.cases → hierarchicallyOrdered` bridge is `co_hierarchicallyOrdered` (nearly complete)

**FR PHILOSOPHY (2026-03-23): FR needs direct ordering, not just rf + co composition.**
Composing rf hierarchy(e_w, e₁) + co hierarchy(e_w, e₂) does NOT automatically give hierarchy(e₁, e₂).
The "no intermediate write" argument from rf's `noBetween` is needed to exclude e₂ being between e_w and e₁.
Rather than implementing this complex composition proof, FR carries `co.cases e₁_lin e₂_lin` directly.
The rf/co⁺ witness documents the protocol-level justification.

**STATUS (2026-03-24): CMCM acyclicity PROOF COMPLETE (cle_advance approach)**

Tagged: `v-cle-advance-sorry-free` — zero sorry's, full compilation.

The proof uses `cle_advance` fields on PPOi/rfe/fr that carry the CLE ordering conclusion.
This is a "scaffolding" proof — a reviewer should see the ordering DERIVED from communication
evidence, not assumed as a field. The honest redesign is the next task.

**Proof architecture (all sorry-free):**
```
co_step_advances (honest: uses wObRDown + encapDirRelation chains)
  → co_chain_cle_advance (chains co steps)
step_advances (PPOi: cle_advance field, rfe: cle_advance field, co: co_step_advances, fr: cle_advance field)
  → lex_lt_trans → transgen_lex_advance → cmcm_acyclic_of_hknow
cmcm_acyclic (ppoi_acyclic for pure PPOi, extract_hknow + cmcm_acyclic_of_hknow for mixed)
eventPartialOrder (from cmcm_acyclic)
```

**NEXT: Redesign to honest proof (in progress on branch `pldi26-honest-proof`):**
1. [x] Tag cle_advance approach as fallback (`v-cle-advance-sorry-free`)
2. [ ] Redesign `rfe`: `diffProtocol` → `diffCache` (struct ≠). Same-cluster diff-cache is rfe.
3. [ ] Redesign `co.ordering` as DESCRIPTIVE inductive (like RF):
   - `sameCache`: direct cache ordering (e₁ OB e₂)
   - `sameClusDiffCache`: CLE₁ OB CLE₂ from cluster directory serialization
   - `diffClus`: downgrade chain (wObRDown + encapDirRelation, like rfe diffCluster)
4. [ ] Write `rfe_step_advances`: derive from readsFrom.cases communication chain
   - wEqRGle.wEqRCle: absurd (sameCache contradicts diffCache)
   - wEqRGle.wObRCle: CLE₁ OB CLE₂ from GleOrCle.cases
   - wObRGle: chain through diffCluster sub-cases (same as co_step_advances)
5. [ ] Write `ppoi_step_advances`: derive from dir_ordered + dirAccessOfRequest
   - Same-addr: temporal chain from e₁ OB e₂ + dirAccessOfRequest cases
   - Diff-addr: CompoundLinearizationOrder from enforce_compound_consistency
6. [ ] Write `fr_step_advances`: DERIVE from rf + co composition + NoInterveningWrites
   - co_chain gives CLE_w ≤ CLE₂
   - rf gives CLE_w ≤ CLE₁
   - NoInterveningWrites + dir_ordered: CLE₂ < CLE₁ → e₂ is intervening write → contradiction
7. [ ] Remove ALL cle_advance fields from PPOi, rfe, fr
8. [ ] cdirEncapsDown (2 sorry's in RfCases/) — separate task

**DESIGN PHILOSOPHY (2026-03-24): Communication evidence, not conclusions**
Each edge type must carry DESCRIPTIVE evidence of the communication mechanism:
- WHAT downgrades happened, WHAT directory events were involved
- The ordering is DERIVED from this evidence in the proof
- A reviewer should see the derivation, not "trust me, CLE advances"
CO must be a descriptive inductive (like RF), not an abstract GLE/CLE mirror.
FR must derive from rf⁻¹;co⁺ + NoInterveningWrites, not carry the conclusion.

**CRITICAL INSIGHT (2026-03-24): CLE lex pair was wrong abstraction**
The CLE lexicographic pair `(CLE.oEnd, e.oEnd)` exploited `dir_ordered` across clusters
(model over-strength, NOT a real protocol property). Cross-cluster CLEs have NO inherent
ordering — the ordering comes from the DOWNGRADE CHAIN (e_r_down, e_r_cdir_down) that
connects them. The honest proof should:
1. Define a `StepOrdering` inductive with PPO (direct OB) and COM (downgrade chain) cases
2. Each COM case carries the specific protocol events (e_r_down, e_r_cdir_down) and their
   OB/Encapsulates relationships
3. The acyclicity proof composes these chains via Trans instances
4. A cycle produces e.oEnd < ... < e.oEnd through the chain → contradiction

`dir_ordered` is ONLY valid for directory events at the SAME cluster. Cross-cluster ordering
comes from the communication mechanism (downgrades), not from `dir_ordered`.

**CORRECT DESIGN (2026-03-24): StepOrdering between linearization points**
Each cache event e has a linearization point `lin(e)` = CLE (from globalLinearizationEventOfRequest).
Each edge `(PPOi ∪ com)(e₁, e₂)` derives `StepOrdering lin(e₁) lin(e₂)` — an ordering between
linearization EVENTS (not cache events), connected via auxiliary protocol events.

StepOrdering has 4 constructors: ob, obEncap, encapOb, encapObEncap.
These capture the OB/Encap/EncapBy chains between linearization points.
The auxiliary events (e_r_down, e_r_cdir_down, cache events) from PPOi/COM
serve as intermediaries in these chains.

Example: PPOi(e₁, e₂) + RF(e₂, e₃) where e₂ is SC write (lin at cache):
  lin(e₁) OB lin(e₂) = e₂ OB e_3r_down EncapBy lin(e₃)
  Composition: obEncap(e_3r_down) between lin(e₁) and lin(e₃).
  NOT simple OB transitivity — needs the Encap chain through e_3r_down.

Key: StepOrdering is between LINEARIZATION EVENTS, not cache events.
The `orderAfterDir` problem vanishes: lin(e) = CLE regardless of its
temporal relationship to the cache event e. The chain connects CLEs
through downgrades, not through cache events.

Transitivity: 4×4 case analysis on StepOrdering constructors.
Most compositions use OB + Encap Trans instances.
The "both EncapBy at junction" cases (4 of 16) need the junction
linearization point to be the SAME event (proof irrelevance on lin(e₂)).
Irreflexivity: all 4 cases derive contradiction from OB irreflexivity
or OB + EncapBy circular chain.

**Key tools for honest proof:**
- `wObRDown` field: CLE₁ OB e_r_cdir_down (added to rCleOrDownAtWAfterWCle.diffCluster)
- `encapDirRelation`: e_r_cdir_down.oEnd < CLE₂.oEnd
- `dir_ordered`: total ordering on directory events (eliminates wrong CLE direction)
- `cache_ordered`: total ordering on cache events
- `dirAccessOfRequest.isDirEvent`: extract DirectoryEvent from CLE
- `succ_ord_impl`: e₁ OB successor from ImmediateBottomSuccSatisfyingProp
- `immediate_bottom_successor_satisfying_p_unique`: successor uniqueness
- Temporal Trans instances: OB→OB, EncapsulatedBy→OB, OB→Encapsulates

**DEAD ENDS (don't repeat):**
00. **ANY per-edge measure (eventLt, compoundLinEvent.oEnd, e.oEnd, finishesBefore) for acyclicity.** The proof is NOT about a ranking that decreases. It's about chaining SPECIFIC OB relationships between protocol events across edges. Each edge gives OB between specific events (CLE, cache events, directory downgrades). A cycle chains these into X OB X. No ranking function needed. STOP looking for rankings.
0. **eventLt (GLE/CLE/cache lex order) as universal ranking.** GLEs can be from the past (previousGlobalCacheGotPerms). For different-address PPOi, GLE₂ OB GLE₁ is possible even when CLE₁ OB CLE₂. The PPO linearization order (compound lin events from CompoundMCM) determines ordering, NOT GLE temporal order. The PartialOrder should be PPOi + COM directly, not mediated through eventLt.
0b. **Event.OrderedBefore as PartialOrder.** Event.OrderedBefore is TEMPORAL ordering (e₁.oEnd < e₂.oStart). It's a proven strict partial order (irrefl, asymm, trans). But com edges (especially rfe) connect events at different clusters that might be temporally concurrent. The PartialOrder we need is COHERENCE ordering (GMO), not temporal ordering. Event.OrderedBefore ≠ GMO.
0c. **Constructing PartialOrder from PPOi ∪ com is circular.** `CMCM.suffices_inclusion` proves acyclicity FROM a PartialOrder. Building the PartialOrder from PPOi ∪ com's transitive closure requires acyclicity for antisymmetry — circular. The GMO must be axiomatized or constructed independently from protocol axioms.
1. Temporal chaining of GLE/CLE for PPOi is a rabbit hole. The `previousGlobalCacheGotPerms` case decouples GLEs from CLE ordering for different addresses. Don't re-derive this.
2. Trying to show CLE₂ OB CLE₁ → False WITHOUT case-splitting on `dirAccessOfRequest`. The `orderAfterDir` case means CLE₁ can be temporally after e₂. Must case-split on dirAccessOfRequest and use the nc.weak CLE-sharing insight (see below).
3. Don't ask the user about protocol semantics derivable from reading `dirAccessOfRequest` and `linearizationEventOfRequest` definitions. Trace through the cases yourself.
4. **Don't wrap `gleOrdering.Cases` (Type) with `Nonempty`** — define Prop-valued inductives mirroring RF instead.
5. **FR composition proof via ranking is genuinely hard** — but the proof should use SPECIFIC protocol events (e_r_cdir_down, CLE), not a ranking. FR should carry e_r_cdir_down and its OB with the target's CLE. rf(e_w, e₁) + co⁺(e_w, e₂) gives e_w < e₁ and e_w < e₂, but NOT e₁ < e₂ without the "no intermediate write" argument. FR carries `co.cases` directly instead.

**CONFIRMED (2026-03-23): The per-edge `hierarchicallyOrdered` approach IS correct for same-addr PPOi.**

The key insight (from Anqi): same-address PPOi events share a CLE or have CLE ordering that follows the PPOi direction. The `hierarchicallyOrdered` ranking function works.

**TODO (updated 2026-03-24):**
- [x] Redefine CO with descriptive `co.ordering` inductive (sameCache/sameClusDiffCache/diffClus)
- [x] Redefine FR as rf⁻¹ ; co⁺ (existential intermediate write + NoInterveningWrites)
- [x] Wire `cmcm_acyclic` through lex pair approach (step_advances → transgen_lex_advance → lex_lt_irrefl)
- [x] co_step_advances: ALL cases sorry-free
- [ ] Close PPOi sorry's #1-3 (orderAfterDir nc.weak CLE sharing — needs cache_ordered + immediacy)
- [ ] Close rfe sorry #4 (noEvictBetween × orderAfterDir — same nc.weak pattern)
- [ ] Close fr sorry #5 (NoInterveningWrites application — needs e₂ membership + protocol classification)
- [ ] Optional: clean up StepOrdering code (non-critical, kept for reference)

## Key architecture

- **Hierarchical order**: 3-level lexicographic (GLE, CLE, cache). GCR is redundant (functionally determined by CLE: CLE₁ = CLE₂ → GCR₁ = GCR₂ → GLE₁ = GLE₂). Defined in `CMCM/Herd/Defs.lean`.
- **PPOi ordering**: `CompoundLinearizationOrder` in `CompoundPPOs.lean` — gives ordering on compound linearization events (CLE level). Proven for different-address pairs.
- **RF theorem**: `readsFrom.cases` in `Rf.lean` / `RfTheorem.lean` — gives GLE ordering for cross-cluster reads-from.
- **Lazy case**: `lazyCompoundLinearizationOrder` arises only for (nc.weak → c.release) PPO pairs in the `orderAfterDir` subcase. Gives `finishesBefore` (weaker than `OrderedBefore`). No cumulativity across transitive PPOi chains.

### Two linearization frameworks (don't confuse them!)
1. **`globalLinearizationEventOfRequest`** (Rf.lean) — used by Herd hierarchy. Has `hreq's_dir_access` (CLE) and `hreq's_global_lin` (GLE via GCR).
2. **`ClusterRequestLinearizationEvent`** (CompoundLinearization.lean) — used by CompoundPPOs. Has `clusterCacheLin` (linearizes at cache) and `clusterDirLin` (linearizes at directory+). `.linearizationEvent` extracts the Event.

The GMO bridge lemma connects framework 2 to framework 1.

## Learned reasoning patterns

### CLE equality shortcut (same address)
For same-address PPOi (e₁ OB e₂), if CLE₁ = CLE₂, then `cle_eq_implies_gle_eq` gives GLE₁ = GLE₂, and `hierarchicallyOrdered_of_same_cle` closes the goal at level 3 (cache ordering from PPOi.orderedBefore). This handles the common case where both events share a directory access (e.g., both use `orderBeforeDir` pointing to the same predecessor). Always check CLE equality first via `by_cases` before doing harder case analysis.

### nc.weak shares CLE with its PPO successor (same address) — KEY INSIGHT (2026-03-23)
For same-address PPOi with nc.weak as e₁ (PPO pairs: nc.weak → nc.release, nc.weak → c.release):
The nc.weak event linearizes at the SAME directory event as its release successor. They share a CLE.

**Trace through `dirAccessOfRequest` cases for nc.weak (e₁):**
- **nc.weak WRITE on Vd**: `orderAfterDir` → CLE₁ from successor. The successor IS the release (e₂), which writes back to directory. So CLE₁ = CLE₂.
- **nc.weak READ on Vd**: `orderAfterDir` → same as write case. The read observes a value that gets written out when the release writes back. CLE₁ = CLE₂.
- **nc.weak READ on Vc**: CLE₁ comes from the event that originally brought the entry to Vc (a predecessor). If the release is nc, there can't be a coherent state between them. Even if there was, the weak nc read IS the system-lin event.
- **nc.weak READ on Invalid**: `encapDir` → the read encapsulates its own directory event. Standard temporal chaining gives CLE₁ before CLE₂.

**Consequence**: For same-address PPOi where e₁ is nc.weak, either CLE₁ = CLE₂ (handled by `by_cases hcle_eq`) or CLE₁ OB CLE₂ (standard temporal). The CLE₂ OB CLE₁ case (sorry #2) is vacuous for nc.weak.

**How to verify**: Read `dirAccessOfRequest` (BehaviourRelationDefs.lean:569-592) and `ncWeakReqOnVd` (line 536). The `orderAfterDir` successor from `immBottomSuccOnVdEncapCorrDir` encapsulates the SAME directory event that the release's `encapDir` gives. They share a CLE because the directory event corresponds to the same cache-level operation.

### Predecessor elimination (same address)
When two events e₁ OB e₂ share an address, to show GLE₁ ≤ GLE₂:
1. Assume GLE₂ < GLE₁ for contradiction
2. e₂ has an "immediate bottom predecessor" pred₂ satisfying `reqHasNoPermsLeavesStateAtLeast`
3. e₁ also satisfies this property (from `reqMissingPerms`, `notDown`, `stateAfterAtLeast`, `reqCache`)
4. e₁ is closer to e₂ than pred₂ → contradicts "immediate"
Key helper: `pred_ord_impl` (RfProofHelpers.lean:2387) extracts `e_pred.OrderedBefore n e` from `ImmediateBottomPredSatisfyingProp`. And `es₁_ordered_es₂_imm_bottom_pred_satisfying_p_contradiction` (Behaviours.lean:179) proves that two ordered events can't both be immediate bottom predecessors of the same successor.

This pattern appears in CompoundPPOs.lean (E,B) case and the RF theorem proof. For the (E,B) case specifically, the proof uses protocol axioms like `acqInvals` to chain ordering through invalidation events.

### GLE/CLE inconsistency (different address AND same address)
CLE₁ OB CLE₂ does NOT imply GLE₁ OB GLE₂ — even for same-address events! In the `noGlobalCache` shim case, GCR finishes before CLE, so GLE (which is at-or-before GCR) can be anywhere before CLE. When CLE₁ OB CLE₂ but both GLEs are before their respective CLEs, their relative order is undetermined by temporal chaining alone. This is why the `CLE₁ OB CLE₂ + GLE₂ OB GLE₁` sorry in same-address case requires protocol-level reasoning (not just temporal composition).

### Temporal chaining: what works and what doesn't
**Works (direct temporal contradiction for CLE₂ OB CLE₁):** When both events use `encapDir` (e encapsulates CLE), or one uses `encapDir` and the other uses `orderAfterDir` (CLE after event) — temporal chain e₁ OB e₂ forces CLE₁ before CLE₂.
**Doesn't work:** When e₁ uses `orderAfterDir` (CLE₁ after e₁) and e₂ uses `encapDir` or `orderBeforeDir` — CLE₁ could be after CLE₂ even with e₁ OB e₂. Requires predecessor elimination.
**Key structural fact:** GLE.oEnd < CLE.oEnd in ALL cases (proven by 4-case analysis on shim×global-dirAccessOfRequest). But GLE.oStart can be before CLE.oStart (noGlobalCache case).

### GCR constraints
All GCRs are SC (from `matchingOp` in `clusterDirEncapCorrespondingGlobalCache`) and non-downgrade (from `notDowngrade`). This eliminates `orderAfterDir` at the global level for GCRs, leaving only `encapDir` and `orderBeforeDir`.

### GMO and the different-address problem
For different-address PPOi events, ordering is only determined when a load observes the latest prior access at an address (loads "observe" via the directory). This is the GMO (Global Memory Order) concept — cf. RISC-V memory model tutorial slide 18. The CompoundMCM approach avoids needing an explicit GMO by stating the request linearizes in cache, or at dir access, or global access, then letting successive downgrades be ordered after it.

### CRITICAL: Compound linearization event ≠ GLE in `previousGlobalCacheGotPerms` case
`clusterDirectoryLinearizationEvent` (CompoundLinearization.lean:97-105) has two sub-cases:
- **`previousGlobalCacheGotPerms`**: `e_glin = e_cdir` — compound lin event IS the CLE. Arises when the CLE has global cache perms (`noGlobalCache` shim case). The Herd GLE comes from `dirAccessOfRequest(cDir'sGReq(CLE))` which goes through a PREVIOUS GCR that finished before CLE. The GLE is from the past, temporally decoupled from the compound lin event.
- **`getGlobalCachePerms`**: compound lin event is a global directory event obtained from `linearizationEventOfRequest` of the GCR. Arises when CLE lacks global cache perms (`encapGlobalCache` shim case). This compound lin event should be closely related to the Herd GLE.

**Implication for different-address PPOi**: When both events have `previousGlobalCacheGotPerms`, compound linearization gives `CLE₁ OB CLE₂`, but GLEs are from past events at DIFFERENT global directory entries (different addresses). GLE ordering is unconstrained by CLE ordering. The `dir_ordered`-based contradiction for `GLE₂ OB GLE₁` does NOT follow from temporal composition alone.

**Concrete scenario**: Address a₂ accessed first (GLE₂ from t=0), then a₁ (GLE₁ from t=1), then PPOi(e₁@a₁, e₂@a₂) gives CLE₁ OB CLE₂ but GLE₂ OB GLE₁. `hierarchicallyOrdered` requires GLE₁ ≤ GLE₂ or GLE₁ = GLE₂, but neither holds.

### Cache events ENCAPSULATE compound linearization events (key fact from CompoundPPOs.lean)
For ncRelease, acquire, and coherent requests: `e.Encapsulates n e_lin` is proven (CompoundPPOs.lean:644-786). This holds for ALL sub-cases of `clusterDirectoryLinearizationEvent` (`previousGlobalCacheGotPerms` AND `getGlobalCachePerms`). The (dir,dir) case proof is at line 784: `calc e_lin₁.EncapsulatedBy n e₁ → e₁.OrderedBefore n e₂ → e₂.Encapsulates n e_lin₂`.

This means compound linearization events are INSIDE cache events, but GLEs are not necessarily inside them (GLEs can be from past events via `orderBeforeDir` at global level).

### Temporal relationships: compound lin event vs CLE vs GLE
For each event e, the compound lin event (e_lin) relates to CLE and GLE as follows:
- **`clusterCacheLin`** (has coherent perms): e_lin = e (the cache event itself). `dirAccessOfRequest` is `orderBeforeDir` → CLE is from a predecessor. Chain: GLE.oEnd < CLE.oEnd < pred.oEnd < e.oStart = e_lin start. So **CLE finishes BEFORE e_lin starts**.
- **`previousGlobalCacheGotPerms`** (CLE has global cache perms): e_lin = CLE. GLE.oEnd < CLE.oEnd. So **e_lin IS the CLE**, and GLE finishes before it.
- **`getGlobalCachePerms`** (CLE lacks global cache perms): e_lin is the GCR's directory event (≈ GLE). CLE encapsulates GCR, GLE is at-or-inside CLE. So **e_lin is INSIDE or BEFORE CLE**.

Key implications:
- e_lin is NOT uniformly "below" CLE — it can be above (clusterCacheLin) or equal to (previousGotPerms) or below (getPerms)
- GLE.oEnd < CLE.oEnd always holds (proven by 4-case analysis)
- Cache event encapsulates e_lin (CompoundPPOs.lean:644-786) — so e_lin.oEnd < e.oEnd always

### Encapsulates means strict containment
`e₁.Encapsulates n e₂ := e₁.oStart < e₂.oStart ∧ e₂.oEnd < e₁.oEnd` — strict on both ends.
Trans instances: `EncapsulatedBy → OB → OB`, `OB → Encapsulates → OB`, `Encap → Encap → Encap`.

### RF theorem: rfe carries "downgrade after system-lin" directly
- `readsFrom.cases` (Rf.lean:636-656): `wObRGle` carries GLE_w OB GLE_r + rich sub-structure
- For `diffCluster` (which all rfe edges are): carries `diffClusters.encapGDown` (Rf.lean:610) + `diffCache.case`
- **KEY STRUCTURE** `encapProxyAndDirAndCDown` (Rf.lean:321-328):
  ```
  existsRDownAtW : ∃ e_r_down ∈ b, e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  ```
  This says: downgrade at e_w's cache, e_w OB e_r_down → **downgrade is after the write (and thus after system-lin)**
- **Downgrade is inside reader's CLE or GCR**: `encapDirRelation` (Rf.lean:294-305) has two cases:
  - `cleEncap`: CLE(e_r) encapsulates cluster dir downgrade
  - `gcacheEncap`: GCR encapsulates cluster dir downgrade
- **Chain**: system_lin(e_w).oEnd ≤ e_w.oEnd < e_r_down.oStart, and e_r_down relates to CLE(e_r)/GCR → temporally connected to system_lin(e_r)
- Sub-cases of `diffCache.case` (Rf.lean:514-551): `wHasPermsAfter` (coherent write), `wNoPermsAfter` (nc write), `wCleAfter`
- The `wCoherent.immPred` case carries the full downgrade chain; other cases carry `rCleOrDownAtWAfterWCle`
- **Conclusion**: existing rfe definitions carry all the structure needed for the cycle contradiction. No extra linking definition required.

### RF communication structure (key for rfe_advances_compoundLin)

For rfe (wObRGle, diffCluster case — the main one), the communication chain:
1. `e_w OB e_r_down` — write before downgrade at e_w's cache (from `encapProxyAndDirAndCDown.existsRDownAtW`)
2. `e_r_cdir_down` — cluster directory downgrade at e_w's cluster (from `encapDir.existsRClusterDirDown`)
3. `encapDirRelation`: e_r_cdir_down inside CLE(e_r) (`cleEncap`) or GCR(e_r) (`gcacheEncap`)

**Connection to compoundLinEvent:**
- e_w's compoundLinEvent is at-or-inside e_w (cache events encapsulate their compound lin — CompoundPPOs.lean:644-786)
- e_r_down is AFTER e_w (temporal)
- e_r_cdir_down is inside e_r's CLE or GCR
- e_r's compoundLinEvent is at-or-inside e_r's CLE/GCR (from ClusterRequestLinearizationEvent sub-cases)
- **Chain**: compoundLin(e_w).oEnd ≤ e_w.oEnd < e_r_down.oStart ... relates to ... compoundLin(e_r)

**CRITICAL GAP**: GLE ordering alone is INSUFFICIENT for compoundLin ordering. When e_w has `clusterCacheLin` (compoundLin = e_w, which is AFTER GLE(e_w)) and e_r has `getGlobalCachePerms` (compoundLin = GLE(e_r)), we need e_w.oEnd < GLE(e_r).oStart, but only have GLE(e_w).oEnd < GLE(e_r).oStart. The proof MUST use the e_w OB e_r_down chain, not just GLE ordering.

**CONFIRMED: e_r_cdir_down encapsulates e_r_down** (from `requestDowngradePrevOwner.dirEncapDowngrade : e_dir.Encapsulates n e_fwd_down` at BehaviourRelationDefs.lean:256). The directory event encapsulates the cache downgrade. So e_r_cdir_down.oStart < e_r_down.oStart and e_r_down.oEnd < e_r_cdir_down.oEnd.

**Complete temporal chain for rfe:**
1. compoundLin(e_w).oEnd ≤ e_w.oEnd (encapsulation or equality)
2. e_w.oEnd < e_r_down.oStart (e_w OB e_r_down from existsRDownAtW)
3. e_r_cdir_down.oStart < e_r_down.oStart (e_r_cdir_down encapsulates e_r_down)
4. e_r_cdir_down is inside CLE(e_r) or GCR(e_r) (from encapDirRelation)
5. compoundLin(e_r) relates to CLE(e_r)/GCR(e_r) (from ClusterRequestLinearizationEvent)

From steps 1-2: compoundLin(e_w).oEnd < e_r_down.oStart
From step 3: e_r_cdir_down starts BEFORE e_r_down (encapsulation)
From step 4: e_r_cdir_down.oEnd < CLE(e_r).oEnd (both encapDirRelation cases)

So: compoundLin(e_w).oEnd < e_r_down.oStart, and e_r_down is inside e_r_cdir_down, which is inside CLE(e_r) or GCR(e_r). The chain from here to compoundLin(e_r) depends on whether compoundLin(e_r) = CLE(e_r) (previousGotPerms) or is inside CLE/GCR (getPerms).

**PROBLEM**: For `previousGlobalCacheGotPerms` + `cleEncap`: compoundLin(e_r) = CLE(e_r). CLE encapsulates e_r_cdir_down, so CLE STARTS BEFORE e_r_cdir_down. The chain gives compoundLin(e_w) < e_r_down, but CLE.oStart < e_r_cdir_down.oStart < e_r_down.oStart. So CLE.oStart could be before compoundLin(e_w).oEnd — the inequality doesn't give compoundLin(e_w) OB CLE(e_r).

**QUESTION**: Is `previousGlobalCacheGotPerms` + `cleEncap` even reachable for rfe? For rfe, e_w and e_r are in different clusters. `cleEncap` says CLE(e_r) encapsulates e_r_cdir_down. But CLE(e_r) is at e_r's cluster, and e_r_cdir_down is at e_w's cluster (different protocol). Can a CLE at one cluster encapsulate a dir event at another cluster? This might be impossible — need to check.

**GAP (remaining)**: The exact chain from e_r_cdir_down to compoundLin(e_r) depends on:
- Whether e_r_cdir_down is the SAME as or related to compoundLin(e_r)
- How `encapDirRelation`'s CLE/GCR encapsulation connects to `clusterDirectoryLinearizationEvent`'s sub-cases (previousGlobalCacheGotPerms vs getGlobalCachePerms)
- This bridge is the core of `rfe_advances_compoundLin`

### RF theorem patterns for dirAccessOfRequest case analysis
- **wEqRGle/wObRGle split**: First split on GLE equality, then on CLE within each branch
- **`orderBeforeDir` handling**: Uses `stateBeforeAndAfterAtLeast` to ensure intermediate events preserve permissions
- **Predecessor property reasoning**: Shows events satisfy (or don't satisfy) `reqHasNoPermsLeavesStateAtLeast` based on request types and cache states
- **Temporal composition**: Uses `encap_by_order_trans`, `order_encap_trans` to chain ordering through encapsulation

## Key reference files

- `CMCM/Herd/Defs.lean` — Herd edge definitions (PPOi, rfe, co, fr) and 3-level hierarchy
- `CMCM/Herd/Proof.lean` — Main acyclicity proof
- `CMCM/Herd/Relations.lean` — `com` union, acyclicity def, CMCM theorem statement
- `CMCM/Rf.lean` — `globalLinearizationEventOfRequest`, `cDir'sGReq`, RF theorem definition
- `CompositionalProtocolProof/CompoundPPOs.lean` — `CompoundLinearizationOrder`, `ppo_cluster_events_satisfy_CompoundLinearizationOrder` (line 2294)
- `CompositionalProtocolProof/CompositionalMCM.lean` — `enforce_compound_consistency`
- `CompositionalProtocolProof/BehaviourRelationDefs.lean` — `dirAccessOfRequest` (line 569), `reqHasNoPermsLeavesStateAtLeast` (line 470)
- `CompositionalProtocolProof/BehaviourShim.lean` — `ClusterToGlobal` (encapGlobalCache vs noGlobalCache), `clusterDirEncapCorrespondingGlobalCache` (matchingOp, notDowngrade)
- `CompositionalProtocolProof/EventRelations.lean` — `Encapsulates`, `OrderedBefore`, `DirectoryEvent.AreOrdered`
- `CompositionalProtocolProof/Events.lean` — `isPPOPair`, `DirectoryEvent`
- `CompositionalProtocolProof/RequestPPOs.lean` — `ValidRequest.isPPOPair` (10 valid PPO pair combinations)
- `CompositionalProtocolProof/CompositionalProof/CompoundLinearization.lean` — `ClusterRequestLinearizationEvent`

## Debugging lessons

- **Stale `.olean` cache**: When definitions change, always use `lake clean` (not manual deletion) before rebuilding. `lake env lean <file>` may use stale cached dependencies.
- **`unfold ... at *` in Lean 4**: Can cause unexpected interactions between hypotheses and goals. When proofs break after structural changes, try unfolding only in hypotheses (`at h12 h23`) and constructing the goal explicitly.
- **`dir_ordered` scope**: `dir_ordered : ∀ (e₁ e₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n e₁ e₂` is universally quantified over ALL directory events in the Lean code (not per-protocol). Applied to equal events, it produces `False` (model over-strength, not a code bug). The intent is per-protocol-instance ordering.

## Auto-habits (run these without being asked)

- **`/checkpoint`** every ~15 min, after milestones, after corrections, before risky changes
- **`/learn`** after discovering patterns, user corrections, dead ends — IMMEDIATELY when you figure something out or learn something new, not later
- **`/reflect`** every ~20-30 min: am I correct? efficient? going in circles?
- **`/philosophy`** before major proof decisions, when stuck, when something feels architecturally wrong
- **Consult philosophy PROACTIVELY** — before proving, implementing, planning, or thinking about anything significant. Ask: "Is the abstraction right? Does this match the protocol mechanism? Will a reviewer find this convincing? Am I being vacuous?" Don't wait until stuck — think deeply FIRST.
- **Consult TODOs and philosophy AS you implement** — after each proof step, check: am I still on track? Does this match the TODO? Is the abstraction still right? This work is tricky — repeatedly verify direction.
- **Don't just close sorry's — verify the replacement does what the TODO describes.** A sorry replaced with wrong semantics is worse than a sorry. (Learned from ParaMC CLAUDE.md.)
- **Work iteratively**: plan → check TODOs/philosophy/CLAUDE.md → implement a step → ask "is this correct? am I on track?" → repeat. This applies to BOTH planning and implementing. Don't go far without checking direction.
- **CHECK: does the implementation match what the user instructed?** Before committing, verify: am I using the approach the user described (OB on communication events), not a shortcut I invented (finishesBefore on cache events)? Does the proof use the specific protocol events (e_r_down, e_r_cdir_down, CLE) as the user showed in their cycle examples? If not, STOP and restructure.
- **USE OB (OrderedBefore) for COM relations in the proof, NOT finishesBefore.** The COM relations order specific protocol events via OB. The proof chains these OB's. DO NOT substitute finishesBefore (e.oEnd comparison) — it's wrong for orderAfterDir and CLE gap cases. ALWAYS use the OB between the actual communication events.
- **Record gaps and TODOs IMMEDIATELY — never let them silently slip past.** If something is incomplete, partially working, or a known limitation, add it to CLAUDE.md TODO right away. A gap you recorded is manageable; a gap you forgot is a blind spot. (From ParaMC CLAUDE.md.)
- **Ask "am I missing something?" after each step.** Are there cases not covered? Edge cases not handled? Properties not checked? If yes, record them as gaps immediately. (From ParaMC CLAUDE.md.)
- **Always give full context when asking the user a question.** Specify: which events, which edge type, which dirAccessOfRequest case, what the temporal chain looks like, and what specifically is unclear. Don't make the user ask "give me more context."
- **Before flagging something as a problem, try to construct a scenario where it IS a problem.** If you can't construct one, it's probably not a problem. Don't raise false alarms — verify the issue exists by imagining a concrete counterexample first.
- **Imagine critical examples to guide implementation.** Before and during implementation, construct concrete cycle scenarios. "What would a PPOi→rfe→fr cycle look like? What events connect?" Trace through mentally. This catches bugs before they happen. (From ParaMC CLAUDE.md.)
- **When reading protocol structures, trace ALL fields and their temporal relationships.** Don't just note what fields exist — understand HOW they relate temporally (encapsulation, OrderedBefore, etc.). Missed `dirEncapDowngrade` in `requestDowngradePrevOwner` because I only traced the top-level structure, not the internal fields. Read EVERY field.
- **Always save key insights to CLAUDE.md** (not just memory files) — this file is loaded every session
- **Re-read CLAUDE.md before investigating questions** — the accumulated knowledge answers most protocol questions. Trace through definitions yourself using what's recorded here.
- **Track all TODOs in CLAUDE.md** — sessions crash! Progress must survive.
- **Git commit after implementing** — after completing any code change, commit immediately to avoid losing progress on crash. Don't wait to batch commits.

## Common commands

- `lake clean` — remove all build artifacts (preferred over manually deleting `.olean`/`.ilean` files)
- `lake build` — build the entire project
- `lake build <module>` — build a specific module and its dependencies (e.g., `lake build CMCM.Herd.Proof`). Faster than full `lake build` for iterating on one file.
- `lake env lean <file.lean>` — compile a single file (doesn't rebuild dependencies — can use stale cache!)
- `lake env lean <file.lean> 2>&1 | tail -20` — compile and check for errors/warnings
