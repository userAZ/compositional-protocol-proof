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

### Status (updated 2026-03-26 session 12)
- **CO edge**: FULLY PROVEN
- **rfe edge**: FULLY PROVEN
- **FR edge**: `fr_ordering_holds` SORRY-FREE. 1 translatedDir sorry in helper.
- **PPOi edge**: Restricted to diff-addr. All non-lazy PROVEN. 1 lazy sorry.
- **StepOrdering.trans**: DELETED (19 sorry's removed). Replaced by LinLink (TransGen LinStep).
- **LinLink.irrefl**: FULLY PROVEN (oStart measure).
- **Cycle proof**: Uses `stepOrdering_to_three` → `compose_three` → cycle contradiction.
- **13 active sorry's** in Proof.lean (down from 37 at session 10 start, 15 at session 11).
- **CompoundProtocol.dirAccessUnique**: Field bridging compound lin ↔ Herd CLEs.

**TODO (post-deadline):**
1. Replace `dirAccessUnique` field with proof by unifying CLE definitions (Type/Prop blocker).
2. Implement lazy PPOi+com pair composition (see TODO in `ppoi_diff_addr_step_ordering`).
3. Prove `reqHasPerms + reqMissingPerms → False` — closes 5 helper sorry's. Key: ALL reqHasPerms cases give `b.hasPerms` (= `eventOnStateHasPerms`). `reqMissingPerms.noPermsForNonNcRelAcqWeakWrite` gives `¬eventOnStateHasPerms` (direct contradiction). `reqMissingPerms.downgrade` needs `¬down` (from PPOi). `reqMissingPerms.ncRelAcqWeakWriteNotOnCoherentState` needs either `coherentState + hasPerms` (from `ncRelAcqWeakWriteHasCoherentPerms`) or request type exclusion (`isCoherent ∧ isNcRelAcq → False`).
4. Fix `compose_three` sorry's — needs structural change (see analysis below).

### Remaining sorry categories (13 active)

**Helper lemma sorry's (5, unreachable at call sites):**
- `compound_lin_start/end_bound` clusterCacheLin branches (lines 161, 162, 220, 223, 226).
- Fix approach: add `¬e.down` param (from PPOi.notDown), then case-split reqMissingPerms. `downgrade` closed via ¬down. `noPerms` closed via hasPerms/noPerms complementarity. `ncRelAcqWeakWriteNotOnCoherentState`: 2 sub-cases need request type exclusion. Line 223 (orderBeforeDir end bound) genuinely fails — needs restructuring or clusterDirLin precondition.

**compose_three sorry's (3, lines 2083/2095/2101):**
- Cross-cluster FR gives `obFinishBefore` → maps to `diff_protocol` in stepOrdering_to_three.
- `diff_protocol` doesn't compose with `LinLink` or other `diff_protocol`.
- VACUOUS at cycle level (diff_prot(cle(e), cle(e)) = absurd rfl), but intermediate composition fails.
- **Root cause**: `obFinishBefore` and `obEndLt diff-protocol` only give oEnd bounds, not oStart bounds. LinLink tracks oStart. Cross-cluster CLEs have no inherent oStart ordering.
- **Potential fixes**: (a) Track BOTH oStart and oEnd in the invariant; (b) Use min-element argument on the cycle; (c) Handle cross-protocol edges at the cycle level, not in step-by-step composition; (d) Eliminate obFinishBefore by strengthening FR evidence.

**Lazy PPOi (1, line 1500):** `lazyCompoundLinearizationOrder` gives `finishesBefore`. Needs PPOi+com pair composition.

**translatedDir (1, line 608):** `clusterDirFromDiffProtocolRequest` endpoint shift through CO chain.

**Deep protocol FR sorry's (3, lines 1899/1996/2000):**
- 1899: `cdir_w OB CLE_w + evict_w OB CLE_w` — temporal loop argument incomplete.
- 1996: `cdir OB CLE_w` — deeper protocol argument needed.
- 2000: diff-cluster e_w — CLE_w OB evict from co chain + encap chain.

### KEY INSIGHT (session 10): FR proof via RF evidence + encapOb

For diff-cluster FR(e₁, e₂) with e_w same cluster as e₂:
1. RF rf(e_w, e₁) is cross-cluster → gives d_rf at e_w's cluster (= e₂'s cluster)
2. `encapDirRelation.cleEncap`: CLE₁ encapsulates d_rf (d_rf inside CLE₁)
3. dir_ordered d_rf CLE₂ at e_w's cluster (both at same cluster) → d_rf OB CLE₂
4. `StepOrdering.encapOb d_rf`: d_rf inside CLE₁, d_rf OB CLE₂ → StepOrdering CLE₁ CLE₂

This avoids the entire `cdirEncapsDown_exists` approach for this sub-case.
For "e_w same as e₁": use cdirEncapsDown_exists at e₁'s cluster (existing approach).
2-cluster constraint eliminates the "e_w diff from both" case.

### 2-cluster model constraint
Only 2 clusters exist (from `isClusterCache.eCluster : protocol = .cluster1 ∨ .cluster2`).
For diff-cluster e₁/e₂: e_w MUST be at e₁'s or e₂'s cluster. The "third cluster" case is vacuous.

### CRITICAL LESSON (session 10): Protocol impossibility vs formal axiom gaps

**The pattern that kept blocking FR**: I had `d_co OB CLE_r` (e_w2's downgrade at e_r's cluster before e_r's CLE) and knew it was protocol-impossible (e_r can't read e_w1's value if e_w2 already downgraded it). But I couldn't formally derive False because the NIW constraints didn't cover d_co (a directory READ with down=False, isDirWrite=False — the `sameCacheConstraints` required isDirWrite + down=True which only the EVICT has).

**The key reasoning pattern**: When something is protocol-impossible but formally unprovable:
1. **Identify WHY it's impossible** — what protocol property is violated?
2. **Check if existing axioms capture it** — trace through the NIW/constraint definitions
3. **If not, determine the minimal axiom extension** — what field/constraint is missing?
4. **Verify the extension is sound** — does the RfTheorem proof provide this evidence?

**The specific fix for FR**: Added `e_r_cdir_down.req.val.rw = e_r.req.val.rw` to `existsRClusterDirDown`. This ties the directory event's request type to the triggering event: for CO (e_r=e_w2, a write), d_co.isDirWrite=True. Combined with a new `sameCacheWriteConstraints` (isDirWrite + ¬down), the NIW covers d_co. The field is provable from the shim's `reqToDirOfRequestEvent` translation.

**Meta-lesson**: Don't try to prove impossibility from temporal bounds alone when the impossibility comes from STATE (directory state after downgrade doesn't have the value). Instead, find/add the axiom that captures the state constraint (NIW constraining which events can be between writer and reader). The axioms ARE the formal representation of protocol state machine properties — if an axiom is missing, ADD it (with user approval), don't try to derive it from temporal chains.

### KEY INSIGHT (session 9): FR proof should mirror RF's structure + case-split on e₁ coherence

**From Anqi:** FR = rf(e_w, e₁) ; co⁺(e_w, e₂). FrOrdering should use rf's cases directly AND add cases for e₂'s downgrade at e₁'s cluster. The current approach (cdirEncapsDown_exists + dir_ordered) tangles because it doesn't account for e₁'s coherence state.

**The right structure for diff-cluster FR(e₁, e₂):**
1. Case-split on e₁'s `dirAccessOfRequest` (encapDir / orderBeforeDir / orderAfterDir)
2. **e₁ coherent (encapDir):** e₁ got perms → e₂ downgrades e₁'s CACHE → `e₁ OB e_w2_down`.
   The cluster dir downgrade encapsulates e_w2_down. CLE₁ OB cdir (via e₁ OB e_w2_down inside cdir).
   Proxy: cdir with CLE₁ OB cdir, cdir.oEnd < CLE₂.oEnd.
3. **e₁ non-coherent / evict:** e₂'s downgrade goes through e₁'s CLUSTER DIRECTORY.
   The downgrade proxy is at e₁'s cluster dir. Different evidence path.
4. This mirrors RF's `wHasPermsAfter` / `wNoPermsAfter` split but applied to the e₂→e₁ direction.

**Why this works:** Each case naturally gives CLE₁ OB proxy (no dir_ordered needed across clusters).
The current sorry's arise because cdirEncapsDown_exists gives evict at e₁'s cluster but dir_ordered
CLE₁ vs evict can go either way. With e₁'s coherence split, the ordering is determined by the
communication mechanism, not by an arbitrary dir_ordered case split.

**Implementation plan:**
- Restructure `fr_ordering_holds`'s diff-cluster branch to case-split on RF evidence first
- For RF same-cluster (e_w at e₁'s cluster): CO crosses → use co_chain_cross_cluster_downgrade
- For RF diff-cluster (e_w diff from e₁): use RF's proxy + compose with CO bound
- In all cases, case-split on e₁'s dirAccessOfRequest for the e₂ downgrade direction
Then `dir_ordered e_de CLE₁`:
- `e_de OB CLE₁` → `diffClusterNotBetweenCles_sameCache` with e_de between CLE_w and CLE₁ → contradiction
- `CLE₁ OB e_de` → `.obEndLt e_de (CLE₁ OB e_de) (e_de.oEnd < CLE₂.oEnd)` → StepOrdering ✓

**FR NEEDS DESCRIPTIVE INDUCTIVE (like RF and CO) — ROOT CAUSE OF ALL FR SORRY'S:**
The current FR definition is a bare existential (∃ e_w, rf ∧ NIW ∧ co⁺) without descriptive
cases. RF has `readsFrom.cases`, CO has `co.ordering` — both carry specific communication
evidence. FR carries NOTHING, forcing re-derivation of everything in step_to_ordering.

The fix: define `fr.ordering` inductive with cases:
- `sameCluster`: e₁/e₂ same cluster → CLEs at same directory → notBetweenCles directly
- `sameClusDiffE_w`: e₁/e₂ same cluster, e_w diff → carries downgrade at e_w's cluster
  with temporal bounds (CLE_w OB cdir evidence from co chain)
- `diffCluster`: e₁/e₂ diff clusters → carries downgrade at e₁'s cluster + evict evidence

Each case carries the protocol events and their OB relationships that make StepOrdering
derivable. The co⁺ chain composes on top of the first rf;co step.

This is NOT a "nice-to-have" — it's LOAD-BEARING. The 3 remaining sorry's exist because
the bare existential doesn't carry the cluster-specific communication evidence.

**FR `cdir OB CLE_w` sorry's — SOLVED via co step's wObRDown:**
The co step's `diffClus` case carries `wObRDown : CLE_w OB e_r_cdir_down` — CLE_w is BEFORE
the cluster directory downgrade. This is the SAME event as `cdir` from cdirEncapsDown_exists
(via Subsingleton). So instead of `dir_ordered CLE_w cdir` (which gives both directions),
use `wObRDown` from the FIRST co step DIRECTLY to get `CLE_w OB cdir`.

For `sameClusDiffCache` co: the `cleOrdering.Cases` also carries temporal bounds.
For `sameCache` co: CLE_w = CLE₂, so the downgrade is at a different event level.

The fix: extract the FIRST co step from `h_co_chain : TransGen co e_w e₂`,
get its `co.ordering`, case-split on sameCache/sameClusDiffCache/diffClus,
and use the temporal evidence directly.

**FR `cdir OB CLE_w` sorry's (939, 1036, 1040) — OLD ANALYSIS (superseded):**
The `CLE_w OB cdir` case is proven via temporal loop (de_w < de_cdir < de_evict < de_w → False).
The `cdir OB CLE_w` case is the "real" direction but the contradiction is still needed:
CLE₂ OB CLE₁ (at e₁/e₂'s cluster) + FR means e₁ reads e_w not e₂ → contradiction.
But `notBetweenCles` needs `CLE₂.protocol = CLE_w.protocol` (fails for diff-cluster e_w).
And `diffClusterNotBetweenCles_sameCache` needs the downgrade BETWEEN CLE_w and CLE₁
(but in this case the downgrade is BEFORE CLE_w, not between them).
And `notBetweenGles` needs GLE_w OB GLE₂ which isn't derivable from CLE_w OB CLE₂
(GLEs can be before their CLEs in the noGlobalCache case).
**Possible fix**: use GLE-level ordering from the co chain (not CLE-level), or
add a new NIW constraint that handles the "downgrade before CLE_w" case.

**Remaining FR approach for sorry 853/855:**
For `CLE_w OB evict` (needed for OrderedBetween): chain through co → CLE₂ → encap → evict.
- Co chain `.ob(CLE_w OB CLE₂)` + `encapGlobalCache` shim: `CLE_w.oEnd < CLE₂.oStart < e_gcache.oStart < ... < evict.oStart` ✓
- Co chain `.obEndLt` or `noGlobalCache` shim: chain breaks. Need sub-case analysis.
- For `evict OB CLE_w` sub-case: should be impossible (co means e₂ after e_w, downgrade after write), but needs protocol state reasoning.

### Key insight: `hierarchicallyOrdered` IS `CompoundLinearizationOrder` (same concept)

`CompoundLinearizationOrder` says: PPO events linearize at specific points in the hierarchy (cache, CLE, or GLE level), and their linearization points are ordered. `hierarchicallyOrdered` says: events are ordered at the highest differing level (GLE, CLE, cache). **These are the same concept** — both ask "where does this event meet the protocol hierarchy, and what's the order at that meeting point?"

The "GMO bridge" is NOT a separate thing — it's recognizing they're the same. There's no gap to bridge. The compound linearization event for each request IS its position in the (GLE, CLE, cache) hierarchy.

**CONSEQUENCE**: `hierarchicallyOrdered` should carry communication evidence (like `readsFrom.cases` does for RF), not just abstract ordering proofs. Each edge type provides its OWN communication evidence:
- **PPOi**: uses `CompoundLinearizationOrder` from CompoundMCM (proven in CompoundPPOs.lean)
- **RF**: uses `readsFrom.cases` (downgrade chains, noBetween)
- **CO**: uses `co.cases` (overwrite communication pattern)
- **FR**: uses rf⁻¹ ; co composition (noBetween ensures validity)

The GLE/CLE/cache lex ordering falls out as a CONSEQUENCE of this communication evidence, used for irrefl/trans.

### Remaining sorry's (updated 2026-03-25 session 3)

**All PPOi sorry's are `CLE₂ OB CLE₁` direction only** — `CLE₁ OB CLE₂` gives `.ob` (proven).

**Proof.lean (6 sorry's):**

1. **Line 228: StepOrdering.irrefl `.eq`** — DEAD CODE. `cmcm_acyclic_of_hknow` handles `.eq` inline via `dir_ordered de de → False`. The sorry in `irrefl` is never reached from the main proof path.

2. **Line 386: PPOi encapDir×orderBeforeDir, pred₂ OB e₁** — e₁ between pred₂ and e₂. Need predecessor elimination: show e₁ satisfies `reqHasNoPermsLeavesStateAtLeast` (from encapDir's `reqMissingPerms` + orderBeforeDir's `hinter_leaves_state_at_least`), contradicting `noIntermediateSatisfyingP`. Other 3 cache_ordered sub-cases proven (encap→downgrade contradiction, e₁ OB pred₂ → temporal `.ob`).

3. **Line 424: PPOi orderBeforeDir×orderBeforeDir, CLE₂ OB CLE₁** — Both have `clusterCacheLin` (CompoundMCM). Needs predecessor elimination or CompoundMCM temporal contradiction. CompoundMCM alone insufficient for (cacheLin, cacheLin) case — needs protocol state reasoning.

4. **Line 457: PPOi orderAfterDir(e₁), CLE₂ OB CLE₁** — e₁ has `clusterDirLin` → e_lin₁ at-or-inside CLE₁. For e₂ with encapDir/orderAfterDir: CompoundMCM temporal contradiction works. For e₂ with orderBeforeDir: needs predecessor elimination.

5. **Line 751: FR same-cluster diff-e_w** — needs `diffClusterNotBetweenCles_sameCache` from NIW.

6. **Line 784: FR diff-cluster, cdir OB CLE₁** — needs NIW application. `h_constraints` extracted but need to show e_cdir between CLE_w and CLE₁. Depends on e_w cluster location.

**RfProofHelpers.lean (2 sorry's in `cdirEncapsDown_exists`):**

7. **Line 3431: cWriteOnMR** — needs sharer extraction from MR directory state.

8. **Line 3483: noCoherentRead** — VD write-back mechanism. May use `nonCohReqDowngrades` axiom for `onDirSW` sub-case. May be vacuous for FR (reader IS coherent → shim should give `bothCoherentWriteAndRead`).

### CompoundMCM bridge analysis (2026-03-25)

`CompoundLinearizationOrder` gives `e_lin₁ OB e_lin₂` where:
- `clusterCacheLin`: `e_lin = e_creq` (cache event). Arises when `reqHasPerms` (= `orderBeforeDir` in dirAccessOfRequest). `e_lin.oEnd > CLE.oEnd` (CLE in predecessor).
- `clusterDirLin`: `e_lin` at-or-inside CLE. Arises when `reqMissingPerms` (= `encapDir` or `orderAfterDir`).
  - `previousGlobalCacheGotPerms`: `e_lin = CLE`
  - `getGlobalCachePerms`: `e_lin` inside CLE

**Contradiction for `CLE₂ OB CLE₁ + e_lin₁ OB e_lin₂`** works when BOTH are `clusterDirLin`:
- Chain: CLE₂.oEnd < CLE₁.oStart ≤ e_lin₁.oStart ≤ e_lin₁.oEnd < e_lin₂.oStart, and e_lin₂.oEnd ≤ CLE₂.oEnd → CLE₂.oEnd < CLE₂.oEnd → False.
**Does NOT work** when one/both are `clusterCacheLin` — need predecessor elimination.

**Implementation status (2026-03-26 session 12):**
- 4 Subsingleton bridge sorry's consolidated into 2 helper lemmas: `compound_lin_start_bound` and `compound_lin_end_bound` (Proof.lean lines 125-141). The 4 call sites use `rwa [hfc]` to rewrite the match hypothesis. Net reduction: 4 → 2 sorry's.
- orderBeforeDir×orderBeforeDir diff-addr: Temporal chain implemented. Non-lazy case derives `Nat.lt_irrefl` via `calc` using the helper lemmas.
- orderAfterDir diff-addr non-lazy: Same temporal chain pattern using the helper lemmas.
- orderAfterDir diff-addr lazy: Needs `hlazy` instantiation.
- encapDir×orderBeforeDir diff-addr: Still a single sorry (same pattern as orderBeforeDir×orderBeforeDir).

**`compound_lin_start_bound` / `compound_lin_end_bound` — PARTIALLY PROVEN (session 11)**

Structure implemented: match on `ClusterRequestLinearizationEvent` (clusterCacheLin / clusterDirLin), then for clusterDirLin: `simp[OfReqEncapDirAccess] + split` to decompose match on `linearizationOfEvent`, then `cases` on `clusterDirectoryLinearizationEvent` (previousGlobalCacheGotPerms / getGlobalCachePerms).

**Proven cases:**
- `clusterCacheLin + orderBeforeDir` for start_bound: temporal chain `CLE.oStart < CLE.oEnd < pred.oEnd < e.oStart`
- `clusterDirLin + requestLin`: closed by contradiction (OfReqEncapDirAccess is False)

**Remaining sorry categories (updated session 12):**

1. **Choose bridge: RESOLVED** via `dirAccessUnique` field on CompoundProtocol (session 11).

2. **clusterCacheLin contradictions (5 sorry's):** Lines 161, 162, 220, 223, 226. Approach: add `¬down` param + case-split `reqMissingPerms`. `downgrade` → `¬down` contradiction. `noPermsForNonNcRelAcqWeakWrite` → `hasPerms` vs `¬hasPerms` (definitional: `Behaviour.hasPerms = Behaviour.eventOnStateHasPerms`). `ncRelAcqWeakWriteNotOnCoherentState`: `ncRelAcqWeakWriteHasCoherentPerms` sub-case → `⟨coherentState, hasPerms⟩` contradicts `¬(coherentState ∧ hasPerms)`. Other sub-cases need request type exclusion: `isCoherent ∧ isNcRelAcq → False` (Acquire has coherent=false, NcRelease has coherent=false) and `isNcWeakRead ∧ isNcRelAcq → False`. Line 223 (`orderBeforeDir` end bound) genuinely fails — restructure call site.

3. **compose_three (3 sorry's):** Lines 2083, 2095, 2101. `obFinishBefore` maps to `diff_protocol` which doesn't compose with `LinLink`. VACUOUS at cycle endpoints. Root cause: cross-cluster CLEs have no oStart ordering. Need structural redesign of cycle proof (min-element, dual tracking, or cycle-level cross-protocol handling).

**Key technique discovered:** `simp[compoundLinearization.OfReqEncapDirAccess] + split` decomposes the match on the opaque `compound.linearizationOfEvent b init e`. The `split` tactic handles the match case analysis. After the split, the `h_2` case (dirLin) gives access to `hdir_lin` and the `clusterDirectoryLinearizationEvent` evidence. This pattern is from CompoundPPOs.lean lines 638-641.

**Key finding: nc.weak + nc.release always has (dir,dir) compound lin.**
From `weakWriteAndNonCoherentRelCannotLinearizeAtCache` (CompoundProtocol axiom): in a PPO pair involving nc.weak and nc.release, NEITHER can linearize at cache. So `clusterCacheLin` is impossible for both. Only the (dir,dir) case survives.
For nc.weak + c.release: the (cache,cache), (cache,dir), (dir,cache) cases are all possible and handled by different lemmas in CompoundPPOs.lean. The lazy case only arises for (dir,dir) with nc.weak + c.release.

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

### RESOLVED: obEndLt is CORRECT (not a dead end)
`obEndLt` uses `p.oEnd < l₂.oEnd` instead of full `EncapsulatedBy`. This IS necessary because of the `noGlobalCache` shim case in `diffCache_coherent_encapProxyAndDir` (RfProofHelpers.lean:3296):
- `noGlobalCache`: CLE already has global perms from a PREVIOUS GCR. The previous GCR encapsulates cdir_down, but CLE does NOT encapsulate the previous GCR (it's a past event). Only `cdir_down.oEnd < GCR.oEnd < CLE.oEnd` holds.
- `encapGlobalCache`: CLE encapsulates GCR (new request). Full `EncapsulatedBy` would hold here, but `oEnd <` also works.
- The construction ALWAYS uses `gcacheEncap` (line 3346), even for `noGlobalCache`. So `oEnd <` is the general bound.
- `obEndLt` is sufficient for irrefl (`l.oEnd < p.oStart ≤ p.oEnd < l.oEnd` → contradiction) and trans (chains through `oEnd < oStart`).

### CRITICAL: `dir_ordered` is ONLY valid for same-directory events
`dir_ordered` in the Lean code is universally quantified over ALL directory events (model over-strength). But it must ONLY be used between events at the SAME directory (same protocol/cluster). Using it between events at different directories gives spurious ordering that doesn't correspond to actual protocol behavior.

**Impact on FR proof**: The FR `step_to_ordering` uses `dir_ordered de₁ de₂` where CLE₁ (cluster A) and CLE₂ (cluster B) may be at different directories. This is INVALID for cross-cluster FR. Same for `dir_ordered de_w de₂`. The FR proof needs to derive CLE ordering from RF+CO communication evidence, NOT from cross-directory `dir_ordered`.

**Valid uses of `dir_ordered`**:
- rfe noEvictBetween: `dir_ordered de_cle de_cdir` — both at e_w's cluster ✓
- co sameClusDiffCache: same cluster ✓
- PPOi same-addr: same cache → same directory ✓
- Any case where both CLEs are at the same `protocol` ✓

**Invalid uses** (must fix):
- FR `dir_ordered de₁ de₂` for cross-cluster FR
- FR `dir_ordered de_w de₂` for cross-cluster FR

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

### LinLink approach (session 11-12): TransGen LinStep replaces StepOrdering.trans

**LinStep** has 2 constructors: `ob` (OrderedBefore) and `encap` (Encapsulates). Both strictly increase `oStart`. **LinLink** = `TransGen LinStep` — gets transitivity for free. **LinLink.irrefl** proven via `oStart_lt` measure.

**stepOrdering_to_three** converts StepOrdering to `LinLink ∨ eq ∨ diff_protocol`:
- `ob` → LinLink (single step)
- `encapOb` → LinLink (2 steps: encap + ob)
- `proxyPair` → LinLink (3 steps: encap + ob + ob)
- `sameLin`/`eq` → eq
- `obFinishBefore` → diff_protocol (l₁.protocol ≠ l₂.protocol)
- `obEndLt` same-protocol → LinLink (via dir_ordered: both are directoryEvents at same cluster)
- `obEndLt` diff-protocol → diff_protocol

**compose_three GAP**: `diff_protocol` doesn't compose with `LinLink`. At cycle endpoints (l₁ = l₃), `diff_protocol(l, l) = absurd rfl` — trivially contradicted. But intermediate composition can't derive the result. This is because cross-cluster CLEs have no oStart ordering. The 3 sorry's (lines 2083/2095/2101) represent this structural gap.

**Potential fix for compose_three**: Track a RICHER invariant through the induction, e.g., `LinLink l₁ l₂ ∨ l₁ = l₂ ∨ (∃ p, p.OrderedBefore n l₂ ∧ p.oEnd < l₁.oEnd)` where the third case carries the actual obFinishBefore payload (proxy + temporal bounds). This composes: `(∃ p, p OB l₂ ∧ p.oEnd < l₁.oEnd) + LinLink l₂ l₃` gives `(∃ p, p OB l₃ ∧ p.oEnd < l₁.oEnd)` because `LinLink l₂ l₃ → l₂.oStart < l₃.oStart` and `p OB l₂ → p.oEnd < l₂.oStart < l₃.oStart` → `p OB l₃`. At cycle level: `∃ p, p OB l ∧ p.oEnd < l.oEnd` → `p.oEnd < l.oStart` (from OB) and `p.oEnd < l.oEnd`, consistent — need additional argument. Alternatively `p OB l → p.oEnd < l.oStart ≤ l.oEnd` and we're back to needing l not before itself.

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
5. **FR needs descriptive inductive `fr.ordering` (like RF and CO)** — bare existential (∃ e_w, rf ∧ NIW ∧ co⁺) doesn't carry cluster-specific communication evidence. All 3 remaining FR sorry's exist because of this. Define `fr.ordering` with sameCluster/sameClusDiffE_w/diffCluster cases carrying the protocol events and OB relationships. The first rf;co step gives the initial relationship; co⁺ chain composes on top.

**CONFIRMED (2026-03-23): The per-edge `hierarchicallyOrdered` approach IS correct for same-addr PPOi.**

The key insight (from Anqi): same-address PPOi events share a CLE or have CLE ordering that follows the PPOi direction. The `hierarchicallyOrdered` ranking function works.

**TODO (updated 2026-03-25 session 2):**
- [x] CO edge: fully proven
- [x] rfe edge: fully proven
- [x] FR CLE₁ OB CLE₂ direction: proven for all 3 by_cases
- [x] CO, rfe: fully proven
- [x] FR same-cluster same-e_w: closed via notBetweenCles
- [x] cdirEncapsDown_exists SW + scReadDown: fully proven
- [x] PPOi encapDir×encapDir, orderBeforeDir×encapDir, *×orderAfterDir(e₂): proven
- [x] PPOi encapDir×orderBeforeDir: 3 of 4 cache_ordered sub-cases proven
- [x] PPOi orderBeforeDir², orderAfterDir(e₁): CLE₁ OB CLE₂ → `.ob` proven
- [x] StepOrdering.irrefl `.eq`: handled at cycle level (dead code in irrefl)
- [ ] **PPOi `CLE₂ OB CLE₁` contradiction**: CompoundMCM bridge for (dirLin,dirLin) cases. Predecessor elimination for (cacheLin,*) cases. User wants CompoundMCM usage for reviewer appeal.
- [ ] **PPOi pred₂ OB e₁**: predecessor elimination (reqHasNoPermsLeavesStateAtLeast)
- [ ] **FR: redesign FrOrdering to be DESCRIPTIVE (not carry StepOrdering)**
  - Current FrOrdering carries StepOrdering directly → VACUOUS
  - Redesign: carry descriptive evidence (protocol events, OB relationships)
  - Write FrTheorem proving FrOrdering from protocol axioms (like RfTheorem)
  - Derive StepOrdering from FrOrdering in step_to_ordering
- [ ] **CO: write CoTheorem proving co.ordering from protocol axioms**
  - co.ordering IS descriptive (sameCache/sameClusDiffCache/diffClus with protocol evidence)
  - co_step_to_ordering DERIVES StepOrdering from co.ordering — honest derivation
  - Missing: CoTheorem showing co.ordering FOLLOWS from protocol axioms (like RfTheorem)
  - Currently co.ordering is a field on the co structure — assumed, not proven
  - Lower priority than FR (co.ordering is at least descriptive, not vacuous)
- [ ] **FR: old design plan (superseded by above):**
  - `sameCluster`: e₁/e₂ same protocol → CLE₁ and CLE₂ at same directory → `dir_ordered` + `notBetweenCles` gives StepOrdering directly. Carries evidence that CLE_w, CLE₁, CLE₂ are at same cluster, same addr, and CLE₂ not between CLE_w and CLE₁.
  - `sameClusDiffE_w`: e₁/e₂ same cluster, e_w different → carries downgrade evidence at e_w's cluster with `CLE_w OB cdir` from co chain. The first co step (rf;co) gives the initial CLE_w → CLE₂ relationship.
  - `diffCluster`: e₁/e₂ different clusters → carries downgrade at e₁'s cluster (evict + cdir from cdirEncapsDown) with temporal bounds.
  - The co⁺ chain: first rf;co step gives fr.ordering. Subsequent co steps compose via co_chain_step_ordering.
  - Add `ordering : fr.ordering` field to `fr` structure.
  - Rewrite step_to_ordering FR case to case-split on fr.ordering.
- [ ] **cdirEncapsDown_exists sorry's** (6 total):
  - isDirWrite derivation (3489): needs reqToDirOfRequestEvent + isSCWrite → isWrite
  - translatedDir components (3496, 3498): downgradeAtPrevOwner wrapper + correspondingDirectoryEvent
  - cWriteOnMR (3502): needs sharer extraction from MR directory state
  - scReadDown evict (3553): scReadDown has single dir event (read, not write) — isDirWrite fails
  - noCoherentRead (3555): VD write-back mechanism, different axiom needed

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

### orderAfterDir temporal chain pattern (PPOi)
For PPOi(e₁, e₂) where e₂ has `orderAfterDir`:
- `hsucc_encap.choose_spec.right` gives `ImmediateBottomSuccSatisfyingProp`
- `.isImmBottomSucc.isSucc` gives `e₂ OB succ₂` (as `Event.oEnd n e₂ < Event.oStart n succ₂`)
- `.satisfyP.encapCorresponding.reqEncapDir` gives `succ₂.Encapsulates n CLE₂`
- Chain: CLE₁ < e₁ < e₂ < succ₂ encaps CLE₂ → CLE₁ OB CLE₂ → `.ob`
- Works for ANY e₁ dirAccessOfRequest case (encapDir, orderBeforeDir, or orderAfterDir)
- `Event.oWellFormed n e₂` bridges `e₂.oStart` to `e₂.oEnd` in the chain

### dir_ordered validity: MUST guard with same_cluster AND same_addr
`dir_ordered` is ONLY valid between directory events at the SAME cluster AND SAME address entry.
- PPOi: `sameProtocol` gives same cluster. `h_same_addr` guard needed for address.
- FR: `h_same_prot` gives same cluster. `sameAddr` from FR structure gives same addr.
- rfe: both CLEs at same cluster (from rfe structure). Same addr from rfe.
- CO: same cluster from CO structure. Same addr from CO.
- Self-application (de de): always valid — trivially gives False.
EVERY `dir_ordered` call must be justified by both same_cluster and same_addr.

### Cross-cluster co chain StepOrdering is always strict
When co⁺(e_w, e₂) gives `StepOrdering CLE_w CLE₂` and CLE_w, CLE₂ are at different clusters:
- `.sameLin` carries `CLE_w = CLE₂` → impossible (different protocols/clusters)
- `.eq` carries `CLE_w = CLE₂` → impossible (different protocols/clusters)
- Only `.ob` and `.obEndLt` remain → both give `CLE_w.oEnd < CLE₂.oEnd` (strict)
This eliminates the equality cases, simplifying FR cross-cluster proofs.

### Lean match substitution is inconsistent
After `match hfc : e, hprop with | .directoryEvent de, _ =>`, Lean substitutes `e` with
`.directoryEvent de` in the GOAL and some hypotheses, but NOT all. Hypotheses that were
created BEFORE the match keep their original `e` type. Always use explicit `rw [hfc]` or
`show ... from ...` to bridge between the original and substituted types. Don't assume
the match propagates everywhere.

### FrOrdering design rationale (verified by imagination)
FR = rf⁻¹;co. The CO part determines the communication structure.
- `sameCluster`: e₁/e₂ same protocol → CLEs at same directory → dir_ordered + NIW → CLE₁ OB CLE₂.
  `sameCLE` is a sub-case (CLE₁ = CLE₂). No need to subdivide into sameCache/diffCache —
  the derivation handles both uniformly via dir_ordered. Whether sameCache or diffCache is
  INTERNAL to the proof of `fr_ordering_holds`, not exposed in the inductive.
- `diffCluster`: e₁/e₂ diff protocol → proxy from cdirEncapsDown_exists at e₁'s cluster.
  Proxy has CLE₁ OB proxy and proxy.oEnd < CLE₂.oEnd → .obEndLt.
Concrete scenarios verified: sameCache (all at one cache), sameClusDiffCache (CLEs at same dir),
diffCluster (CLEs at different dirs), diffCluster with e_w at third cluster.

### FR exhaustive case design (verified by imagination)
FR = rf(e_w, e₁) + co⁺(e_w, e₂). All three at same address.
**Config 1: A=B=C** (all same cluster): dir_ordered + notBetweenCles. PROVEN ✓.
**Config 2: A=B≠C** (e₁/e₂ same, e_w diff): dir_ordered CLE₁ CLE₂. CLE₁ OB CLE₂ → done.
  CLE₂ OB CLE₁ → need cross-cluster co step's wObRDown → downgrade between CLE_w and CLE₁
  → diffClusterNotBetweenCles_sameCache → contradiction.
  Helper needed: extract first cross-cluster co step from TransGen.
  CRITICAL: do NOT use cdirEncapsDown_exists for Config 2! The co step's encapDir is
  parameterized on e_w_next (not e₂), so Subsingleton bridge fails between them.
  Use the co step's wObRDown DIRECTLY instead.
**Config 3: A≠B** (e₁/e₂ diff): cdirEncapsDown_exists → proxy at cluster A.
  CLE₁ OB proxy → .diffCluster. proxy OB CLE₁ → same approach as Config 2.
  Sub-configs 3a/3b/3c based on e_w cluster.
The FrOrdering inductive (sameCluster/diffCluster/sameCLE) covers all configs.
The fr_ordering_holds PROOF handles configs 1-3 with the helper.

### LESSON: Plan inductive cases EXHAUSTIVELY before implementing (FR case study)
I circled for hours on FR sorry's because I didn't plan the cluster configurations:
- Same-cluster co step (sameCache/sameClusDiffCache): NO cross-cluster downgrade at e_w's cluster!
  The first co step's downgrade goes to the OVERWRITER's target, not back to e_w.
- `cdir_w` from `cdirEncapsDown_exists` comes from e₂'s GLOBAL downgrade chain — which traverses
  ALL co steps, not just the first. Connecting to the first co step was wrong.
- The FrOrdering cases must be defined by CLUSTER CONFIGURATION, not by temporal case split:
  1. All same cluster: dir_ordered + notBetweenCles
  2. e₁/e₂ same, e_w different: downgrade from co chain at e_w's cluster
  3. e₁/e₂ different: downgrade from e₂ at e₁'s cluster
  4. All different: most complex
- **Always plan inductives EXHAUSTIVELY before implementing.** Define cases on paper, trace
  scenarios for each, verify each case has the right evidence. Don't start implementing
  until all cases are clear. This would have saved hours.

### CRITICAL: Definitions must be DESCRIPTIVE, not carry conclusions
FrOrdering carrying `StepOrdering` directly is VACUOUS — it's the thing we're trying to prove!
A reviewer would reject this as circular. The definition must carry DESCRIPTIVE evidence
(protocol events, temporal relationships, communication chains), and the PROOF must DERIVE
StepOrdering from this evidence. The derivation IS the proof.

Pattern for honest definitions:
1. Inductive carries WHAT HAPPENED (which events, their OB/Encap relationships)
2. Theorem proves the inductive FOLLOWS from protocol axioms (like RfTheorem)
3. step_to_ordering DERIVES StepOrdering from the inductive's evidence

If the inductive directly carries the conclusion → scaffolding, not proof.

### EVERY relation needs descriptive inductives (RF/CO/FR pattern)
RF has `readsFrom.cases`. CO has `co.ordering`. FR needs `fr.ordering`. PPOi uses CompoundMCM.
**Each relation must carry its communication evidence as inductive cases**, not bare existentials.
Without cases, the proof can't case-split on communication structure, and protocol-specific
evidence (same-cluster vs diff-cluster, temporal bounds) must be re-derived from scratch.
The DESCRIPTIVE cases carry the mechanism; the ordering is a CONSEQUENCE visible in the structure.
**If you're fighting to prove StepOrdering from a relation, the relation's definition is wrong.**

### Push sorry's to infrastructure lemmas (cdirEncapsDown_exists pattern)
When Proof.lean needs protocol evidence from the shim (isDirWrite, down, translatedDir, etc.),
extend `cdirEncapsDown_exists` to return it rather than constructing it inline in Proof.lean.
This keeps the main proof clean and concentrates protocol plumbing in one file. The pattern:
1. Identify what Proof.lean needs
2. Add the field to `cdirEncapsDown_exists` return type
3. Prove it inside the lemma (using shim access)
4. Extract it in Proof.lean with simple destructuring

### Exists.choose bridge problem and solution
`Exists.choose` uses `Classical.choice` — does NOT reduce even on concrete `⟨a, h⟩` witnesses.
`Subsingleton.elim` gives `hdown = hdown'` but `hdown'.choose` still doesn't reduce to `e_dw`.
**Solution**: Don't use `choose` in goals. Return existential witnesses directly from lemmas.
`cdirEncapsDown_exists` provides `e_cdir` as explicit existential (not `hdown.choose`).
Pattern: when a lemma needs to state something about a SPECIFIC event from a construction,
return that event as an existential witness rather than going through `choose`.

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
- **`/imagine`** BEFORE implementing: construct a concrete scenario (name the events, trace the chain, check reachability). 30 seconds of imagination saves hours of wrong-direction coding. Use for: "can this case actually arise?", "what does the temporal chain look like?", "is this case vacuous?"
- **Use creativity**: when stuck, don't just try harder — try differently. Question whether the definition is right, whether a different intermediate event works, whether a constructor should be weaker/stronger. The `obEndLt` insight came from asking "what does `noGlobalCache` actually give us?" not from trying to force `EncapsulatedBy`.
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
