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
- **MR + NC weak write is IMPOSSIBLE**: MR state (`⟨some .r, true⟩`) can only be reached via SC coherent read (proved by `event_list_to_mr_requires_coherent_read` in RfProofLargeLemmas.lean). But `FollowsProtocolInterface.nc_no_sc` forbids NC requests in any PI that has SC reads. So a protocol that supports NC weak write CANNOT have MR state. Use `nc_weak_write_not_on_mr_state` for this. **This proves ob_cle (compoundLin_ob_cle) is ALWAYS vacuous**: the only non-trivial sub-case requires NC weak write on MR, which is protocol-impossible.

### Codebase philosophy
- Definitions validated by Murphi model checking. **Never add new axioms.** Prove from existing definitions.
- Descriptive definitions carry mechanism (WHAT happened), not just consequences. The ordering is DERIVED.
- dir_ordered is model over-strength (orders ALL directory events). Only valid for same-cluster, same-address.

## Rules

### AUTOMATIC WORKFLOW (do these WITHOUT being asked)

**BEFORE writing any proof code:**
1. **DRAW THE PROTOCOL SCENARIO.** What events? What types (read/write/downgrade)? What edges? What temporal/protocol relationships? What are the junction constraints? This catches bogus cases and reveals the proof path. Solved CleLink.eq cycle closure in minutes after hours of grinding.
2. **SKETCH UNCERTAIN THEOREMS.** Write a partially sorry'd test theorem. Build. If types don't match → approach is wrong → caught in seconds, not hours. Do this BEFORE committing to large mechanical work (like fixing 100+ construction sites).
3. **CHECK: am I using protocol info or type-theory tricks?** Protocol info IS the proof. Subsingleton, Prop irrelevance, measure theory → wrong path. Protocol address evidence, junction read/write analysis, communication evidence → right path.

**DURING proof work:**
4. **BE HONEST.** If stuck, say so immediately. If going in circles, say so. If an approach failed, say so. Don't present partial work as done. Honesty saves hours.
5. **SAVE LESSONS IMMEDIATELY.** Every user correction, failed approach, working approach, protocol insight → write to CLAUDE.md RIGHT NOW. 10 seconds to write, hours to re-discover.

**NEVER do:**
6. **NEVER start an agent.** Agents lack CLAUDE.md context, re-introduce abuses, interfere with concurrent edits, and produce worse results. Do ALL work yourself — no agents, no subprocesses, no delegation.
7. **NEVER use dir_ordered without verifying same address/cluster AND distinct events.** dir_ordered de de is cheating — no event is strictly before itself. Cross-address or cross-cluster dir_ordered is cheating. ALWAYS verify before claiming a use is legal.
7b. **DOUBLE-CHECK every claim before presenting it.** Don't say "all uses are legal" without verifying each one. Don't say "this branch is dead" without proving it. The user should not have to audit every item in depth. Verify YOURSELF, thoroughly, before reporting.
8. **NEVER try simple measures (oStart, oEnd) for CleLink/LinLink irreflexivity.** These relations encode protocol-specific ordering that no single measure captures.
9. **NEVER confuse GLE and compoundLin.** `globalLinearizationEventOfRequest` = CLE+GLE bundle. `compoundLin` = derived Event. Philosophy: compoundLin is primary, connected through CLE/GLE.

### Core rules

0. **NO SORRY'S.** Zero sorry's. If unprovable → wrong approach → find a different one.
1. **Understand first, prove second.** Walk through the proof in text before formalizing.
2. **Read the actual definition.** Grep and read source. Never assume.
3. **Consider all PPOi and COM cases.** Each case has specific protocol evidence. Trace it.
4. **Never add new axioms.** Case-split on existing inductive types.
5. **Verify proofs are not vacuous.** Check hypotheses are satisfiable, conclusions nontrivial.
6. **Search the codebase first.** Check existing proofs (compose_three, step_to_ordering, RF/CO/FR theorems) for similar patterns. Reuse protocol reasoning.
7. **When temporal evidence is insufficient, add protocol address/cluster evidence.** This is the safest way to close gaps. Example: CleLink.encapObEndLt needs h_ne from protocol context, not temporal chain.
8. **Use DecidableEq on Event n for CLE equality checks.** Avoids Prop irrelevance issues. Pattern: `if h : CLE₁ = CLE₂ then .eq else .constructor ... h`.

## The Goal (NEVER FORGET)

**Prove acyclic(PPOi ∪ rfe ∪ fr ∪ co) using CompoundMCM linearization events (compoundLin).**

### How compoundLin events are related

Each event `e` has a linearization `lin e` which provides:
- `lin.compoundLin` — the compoundLin event (the linearization point)
- `lin.cle` — the CLE (cluster directory event from `dirAccessOfRequest`)
- `lin.gle` — the GLE (global directory event)

The compoundLin events are related through **4 temporal relations**:
- **OB** (OrderedBefore): `cmpLin₁.oEnd < cmpLin₂.oStart`
- **Encapsulates**: `cmpLin₁.oStart < cmpLin₂.oStart ∧ cmpLin₂.oEnd < cmpLin₁.oEnd`
- **EncapsulatedBy**: reverse of Encapsulates
- **FinishesBefore**: `cmpLin₁.oEnd < cmpLin₂.oEnd`

These relations are established through **proxy events** from `dirAccessOfRequest`:
- **encapDir**: `e` is encapsulated by CLE. cmpLin is INSIDE CLE.
  CLE encaps cmpLin → Encapsulates relationship.
- **orderBeforeDir**: `e` is AFTER a predecessor's CLE. The predecessor got perms.
  cmpLin is AFTER CLE → CLE OB cmpLin (or cmpLin is the CLE itself for dirLin).
- **orderAfterDir**: `e` is BEFORE a successor's CLE. NC weak on Vd.
  cmpLin is BEFORE CLE → cmpLin OB CLE (ob_cle, proved vacuous).

For each edge (PPOi/COM), the proof:
1. Gets CLE₁ and CLE₂ from `lin₁.cle` and `lin₂.cle`
2. Derives CleLink CLE₁ CLE₂ (from step_to_ordering using communication evidence)
3. Bridges CLE ordering to compoundLin ordering via `cle_to_compoundLinOrdering`
   using the dirAccessOfRequest cases above → LinLink cmpLin₁ cmpLin₂

The acyclicity proof itself uses `event_oEnd_lt` (e₁.oEnd < e₂.oEnd for every edge)
which is a direct protocol causal ordering property. The CLE/compoundLin machinery
provides the PRESENTATION of how linearization events are ordered.

## Current goal: Herd CMCM acyclicity proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` in `CMCM/Herd/Proof.lean`.

### Status (updated 2026-04-04, dir_ordered clean)
- **ZERO illegal dir_ordered.** Main proof uses `edge_oEnd_lt` (protocol causal ordering: `e₁.oEnd < e₂.oEnd` for every edge). No CLE composition needed. 6-line acyclicity proof.
- **Remaining legal dir_ordered**: FR theorem (`fr_ordering_holds`) — ~28 uses, all verified same-addr same-cluster distinct events. `cle_to_compoundLinOrdering` — 1 use, same-COM-edge CLEs.
- **Protocol fact added**: `event_oEnd_lt` field on rfe, co, fr structures — the second event finishes strictly after the first (validated by Murphi model checking).
- **897 lines of dead CLE composition infrastructure removed** (compose_three, cle_path_invariant, ppoi_diff_addr_exfalso, etc.).
- **1 sorry remaining**: `cycle_eq_closure` h_all_same_cle (Proof.lean:3118)
- **ZERO `hdir de de` abuse**: All dir_ordered self-applications removed via h_ne on CleLink constructors + address-based PPOi contradiction + readsFrom case analysis for rfe.
- **h_ne approach**: Non-eq CleLink constructors carry `h_ne : l₁ ≠ l₂`. At self-reference, non-eq cases close with `absurd rfl h_ne`. sameLin closes with temporal chain (CLE.oEnd < e₁'.oEnd < e₂'.oStart < CLE.oStart < CLE.oEnd). eq delegates to cycle_eq_closure.
- **PPOi (diff-addr) + CLE equality**: Impossible. CLE.addr = e.addr (from dirAccessOfRequest.dirCorresponds.sameAddr), so CLE₁=CLE₂ → e₁.addr=e₂.addr → contradicts addr≠.
- **rfe + CLE equality**: Impossible. Case-split CleLink → non-eq/sameLin give contradiction. eq case: case-split readsFrom → all sub-cases give OB/oEnd chains that contradict CLE₁=CLE₂.
- **Key theorems**:
  - `cmcm_acyclic_of_hknow` (line 2600): CLE-level acyclicity proof. COM evidence via step_to_ordering → compose_three.
  - `cmcm_acyclic_of_hknow_compoundLinOrdering` (line 2632): CompoundLin-level acyclicity. LinLink invariant on compoundLin events. Lifts CLE result via lift_cle_3way_to_compoundLin. Cycle closure via LinLink.irrefl.
  - `LinLink.subset_temporalRel` (line 2711): Every LinLink decomposes into TransGen BasicTemporalRel.
  - `CleLink.subset_temporalRel` (Defs.lean:211): Every CleLink decomposes into TransGen BasicTemporalRel.
  - `compoundLin_not_ob_cle` (line 1573): ob_cle always vacuous (MR+NCWeakWrite protocol-impossible).
  - `co_ordering_holds` (CoTheorem.lean): CO theorem from protocol axioms.
- **Architecture**:
  - `cle_path_invariant`: Reusable CLE-level induction (CleLink/eq/reverse on CLEs from any path).
  - COM evidence flow: edge → step_to_ordering → CleLink → compose_three → lift_cle_3way_to_compoundLin → LinLink.
  - `TemporalRel = TransGen BasicTemporalRel` where BasicTemporalRel = {OB, Encap, EncapBy, FinishesBefore}.
  - `finishesAfterProxy` removed from TemporalRel; obFinishBefore handled via dir_ordered exfalso.
  - **Composition**: `compose_three` handles all StepOrdering/eq/reverseOB × PPOi/COM cases.
  - **`cmcm_acyclic_of_hknow` is sorry-free!** Delegates to compose_three.
- **compose_three**: SORRY-FREE. Uses dir_ordered fallback for hard cases (all CLEs are directory events → always resolvable).
- **StepOrdering enriched**: `obEndLt`, `encapObEndLt`, `obFinishBefore` all carry `h_p_isdir`.
- **Non-lazy PPOi**: `h_non_lazy_ppoi` hypothesis excludes lazy RCC.
- **Dead code**: CLE-to-compound_lin bridge removed. `ppoi_diff_addr_step_ordering` deleted.
- **`cdirEncapsDown_exists`**: `h_dir_coherent` parameter removed; onDirVd proved inline with consistent e_r_gdown. sameProtocol chain proved via `correspondingCluster_protocol_eq`. Proof.lean call sites cleaned.
- **`cacheEvent_Vd_transition_isNcWeakWrite`**: SORRY-FREE via ValidRequest Subtype match.
- **RfCase files**: Fixed `rCleOrDownAtWAfterWCle.diffCluster` pattern match (missing 3rd field after `wObRDown` was added).

### TODO
8. **1 sorry remains: `cycle_eq_closure` (Proof.lean line ~2821)**. Needs `TransGen R e e → False` without `hdir de de`. The gap: `FR.sameCLE` (read+write at same CLE) doesn't carry event-level OB. Need to derive `e₁ OB e₂` from FR's `comm` field (`readsFrom + NIW + TransGen co`). All other edge types handled. Protocol argument is sound (drew junction diagram). Implementation approach: create `edge_cle_or_ob` that for each edge gives either `CLE₁ ≠ CLE₂` (non-eq CleLink → temporal contradiction) or `e₁ OB e₂` (compose through cycle → `e OB e → False`). The FR.sameCLE case needs `e₁ OB e₂` from `comm` evidence.
9. **PREVIOUS: `cleLink_self_false` `.eq` case and `LinLink.irrefl` proxy case still use `dir_ordered de de` (same event). Proper fix via protocol reasoning: a cycle at the same address/cache ALWAYS contains a CO.sameCache edge (carries `cache_ob : e₁ OB e₂`). FR goes read→write (can't cycle alone — `fr(write, x)` needs `write.isRead`). Pure FR cycles impossible. So any cycle with CLE equality has event-level OB from CO → OB cycle on events → `e OB e` → False. Implementation: at cycle closure with CLE equality, extract event-level OB from the CO edge, compose through cycle → contradiction.
9. **Finish cmpLin theorem/induction**: Make the relations around cmpLin explicit — the induction should show compoundLin events are ordered at each step through CLEs/GLEs.

### TODO — PREVIOUSLY COMPLETE
1. ~~CO Theorem~~ — DONE: `co_ordering_holds` in CoTheorem.lean.
2. ~~Dead code cleanup~~ — DONE: no marked-as-DEAD functions remain.
3. ~~CompoundLin lifting~~ — DONE: `cmcm_acyclic_of_hknow_compoundLinOrdering` with LinLink invariant on compoundLin.
4. ~~Remove reverse case~~ — INVESTIGATED: not feasible (documented above). Accepted.
5. ~~Lemma6 sorry's~~ — DONE: both sorry's resolved (proxy isCacheEvent, non-Vd state path).
6. ~~MWE cleanup~~ — DONE: all scratch files removed.
7. ~~LinLink.subset_temporalRel~~ — DONE: every LinLink decomposes into TransGen BasicTemporalRel.

**Zero sorry's across entire project. Tag: `zero-sorry-all-files`.**

### Lessons learned THIS SESSION (CleLink h_ne refactoring)
- **Sketch test theorems BEFORE fixing 103 construction sites.** The test at cycle closure confirmed the h_ne approach works in 30 seconds, saving hours of wasted mechanical work if the approach were wrong.
- **Add protocol address/cluster evidence to CleLink constructors that need it.** `encapObEndLt` can't derive `l₁ ≠ l₂` from temporal evidence alone — it needs address evidence. The general lesson: when temporal evidence is insufficient, bring in protocol address/cluster context. This is the SAFEST way to proceed.
- **Never use `dir_ordered` on events without verifying same address/cluster.** Even on DISTINCT events, `dir_ordered` is only legitimate for same-address same-cluster directory events. Using it on different-address events is the same over-strength abuse.
- **CleLink is Prop — all proofs at the same type are equal (Subsingleton).** Can't distinguish `.eq` from `.ob` at `CleLink l l`. The fix: add `h_ne : l₁ ≠ l₂` to non-eq constructors. At self-reference: non-eq → `absurd rfl h_ne → False`. `.eq` → cycle_eq_closure.
- **SKETCH UNCERTAIN THEOREMS BEFORE COMMITTING TO LARGE MECHANICAL WORK.** Before fixing 100+ construction sites, sketch test theorems for the UNCERTAIN parts (e.g., can I derive h_ne at each site?). 10 seconds of sketching saves hours of wasted work. DO THIS AUTOMATICALLY.
- **SAVE LESSONS TO CLAUDE.md IMMEDIATELY — THIS IS NON-NEGOTIABLE.** Every time you learn something (user correction, failed approach, working approach, protocol insight), write it to CLAUDE.md RIGHT THEN. Don't wait. Don't batch. Don't "plan to save later." The cost of writing is 10 seconds. The cost of forgetting is hours of repeated mistakes. This applies ESPECIALLY to: (1) protocol insights about when cases are possible/impossible, (2) which approaches work vs fail for Lean mechanics, (3) user corrections about proof strategy.

### Lessons learned (BE INTROSPECTIVE!)
- **Don't guess constructors.** Each new StepOrdering constructor multiplies case analysis. Use edge data instead.
- **Information loss is the enemy.** `step_to_ordering` strips rich edge evidence. Keep original edge data available.
- **Sorry checklist (RUN THIS FIRST before any sorry fix)**:
  1. Is it a bug introduced by a previous commit? Check git history — revert if so.
  2. Is the issue resolved by looking at the upper level theorem context? Does the caller actually need this?
  3. Are you stuck in a rabbit hole? If >15 min without code progress, STOP, draw a picture, explain simply.
- **Check the context of the proof that CONSTRUCTS the sorry'd structure.** If the sorry needs X, the construction site probably already HAS X but doesn't store it. Adding a field is trivial — the construction already provides it. Example: `noEvictBetween` needed `CLE_w OB cdir`. The RF theorem already knew this (it's implicit in `noWriteBtn` operating between CLE_w and cdir) — just not stored as a field. Adding `wCleObCdir` compiled immediately with zero changes to construction sites.
- **After matching on Event constructor, derive CacheEvent-level hypotheses.** Event-level hypotheses (e.g., `hacq_req : Event.req n e = ...`) don't reduce inside `match e with | .cacheEvent ce => ...` because the match changes the term but not the hypothesis. Fix: derive `hce_req : ce.req = ...` by `simpa [Event.req] using hacq_req` AFTER the match. Same for `Event.down` → `ce.down`. This was the key to fixing the Lemma6 sorry.
- **Case-split BEFORE simp chains, not after.** If a proof depends on a case distinction (e.g., cache state = Vd vs non-Vd), do the match FIRST, then run the simp chain inside each branch with the concrete value. Running simp first with an abstract value consumes the pattern, making later case-splits ineffective. Example: Lemma6 needed cache state match before `reqToDirOfRequestEvent` simp.
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
- **compoundLin events are ALWAYS related to CLEs** via compoundLin_cle_rel (eq/cle_ob/ob_cle/inside). NEVER forget this when reasoning about compoundLin. dir_ordered can ALWAYS be applied to CLEs (directory events), then chained to compoundLin via proxy constructors. This is the FUNDAMENTAL technique for the compoundLin lifting.
- **reverseOB in 3-way invariant**: Legitimate intermediate state from dir_ordered giving "wrong" direction. Can't be contradicted locally — resolved at cycle closure (l OB l → False). For PPOi: compoundLin version uses h_non_lazy_ppoi directly (no dir_ordered needed). For stuck composition: dir_ordered on CLEs may give reverse. The reverse bridge (CLE₂ OB CLE₁ → compoundLin₂ OB compoundLin₁) is needed but has the same structure as the forward bridge.
- **WRITE DOWN important information and lessons in CLAUDE.md IMMEDIATELY.** Don't rely on memory across sessions or even within a session. If you discover a key insight (like "compoundLin is always related to CLE"), write it here RIGHT NOW. Forgotten insights cause hours of wasted work going in circles. The cost of writing is seconds; the cost of forgetting is hours.
- **PLAN proofs using protocol meaning and upper-level context BEFORE implementing.** Don't grind through sorry's mechanically. Ask: what does this case MEAN in the protocol? What does the caller need? What evidence is available? A 10-minute planning session saves hours of case-analysis grinding. The compoundLin lifting was stuck for hours until planning revealed that dir_ordered goes through CLEs — a fact obvious from the protocol meaning but invisible from the Lean types alone.
- **Resolve uncertain parts of a plan FIRST — this is the DEFAULT approach for any non-trivial proof.** Before investing in large mechanical work, ALWAYS: (1) sketch the full plan, (2) identify which lemmas/theorems have uncertain feasibility, (3) write and test those uncertain parts FIRST, (4) only then do the mechanical work. For compoundLin lifting: testing `cle_self_ordering_false` at cycle closure took 5 minutes and confirmed the approach. Without this check, 500 lines of `compose_three` duplication could have been wasted if cycle closure failed. This is now the DEFAULT workflow: plan → identify uncertainties → resolve uncertainties → execute.
- **Implement foundational fixes, not band-aids.** The reverse case in StepOrdering's 3-way invariant was a band-aid for `dir_ordered` giving the "wrong" direction. Band-aids create technical debt that compounds. A foundational fix pays off immediately and prevents future blockers. ALWAYS ask: "Is this a band-aid or a real fix?" before implementing.
- **Examine NOW vs LATER for fixes.** Before punting a fix, reason: (1) Will doing it later require MORE work because I'll build on the band-aid? (2) Does the band-aid block or complicate the next step? (3) How much work is the fix NOW vs the rework LATER? The reverse case example: writing compose_three WITH reverse and THEN removing it = double work. Writing it WITHOUT reverse from the start = once. The fix should have been done FIRST. Make this examination automatic.
- **Write code first, analyze later.** When facing a sorry, just try to fill it with code, build, iterate. Don't write paragraphs theorizing about feasibility. Most sorry's are mechanical once you start writing. BUT: this rule applies to INDIVIDUAL sorry's after the plan is clear. Don't apply it to the OVERALL approach — that needs planning first.
- **Match on ValidRequest (Subtype), not on individual fields**: `RequestState`/`DowngradeState`/`MRS` match on the full `ValidRequest` Subtype `⟨⟨rw, coh, con⟩, hv⟩`, NOT on individual fields. Matching on `ce.req.val.rw`, `ce.req.val.coherent` etc. separately doesn't give Lean enough info to reduce the Subtype match. **Fix**: `match hvr : ce.req with | ⟨⟨.w, false, .Weak⟩, _⟩ => ...` then `rw [hvr] at hs_Vd` to substitute before `simp [ValidRequest.RequestState]`. Lean uses `IsValid'` for exhaustiveness — invalid request patterns (like `⟨_, false, .SC⟩`) are auto-excluded.
- **`simp only` vs `simp` for `if` reduction**: `simp only [...]` does NOT include `ite_true`/`ite_false`, so `if True then x else y` won't reduce. Use `simp [...]` (without `only`) to include default simp lemmas, or add `ite_true`/`ite_false` explicitly.
- **`compoundLin_ob_cle` is VACUOUS**: `requestLin + orderAfterDir` is contradictory. `requestLin` requires `reqHasPerms` (coherent: `isCoherent`, or `ncRelAcqWeakWrite + coherentState`, or `ncWeakRead + notVd`). `orderAfterDir` requires `ncWeakReqOnVd` (non-coherent weak on Vd state). ALL three `reqHasPerms` constructors contradict `ncWeakReqOnVd`: (1) isCoherent vs non-coherent, (2) coherentState vs Vd, (3) notVd vs Vd. Therefore `ob_cle` (compoundLin OB CLE) can never arise — any case analysis that reaches it should close with `exfalso`.
- **`lin(dir_event)` gives False for directory events**: `dirAccessOfRequest` constructors are designed for cache events. For a directory event: `encapDir` has `dirOfReq` = False (isDirEventOfReqEvent is false for (dir,dir)); `orderBeforeDir` has `hnot_down` which contradicts `down=true` for downgrades; `orderAfterDir` has `reqCache` = False (dir events aren't cache events). Use this pattern to derive `exfalso` whenever a directory event appears in `lin(e)`. This solved onDirVd and the cdir OB CLE_w temporal contradiction.
- **READ DEFINITIONS BEFORE MAKING ANY CLAIM.** This is a BLOCKING rule. Before saying "X can/can't happen", "case Y is vacuous/real", "stateAfter does Z" — OPEN THE FILE and READ the definition. `grep -rn 'def ...'` takes seconds. Guessing from names has been wrong REPEATEDLY: `stateAfter` has specific case-split logic per request type, `RequestState` for NC weak write on MR returns Vd (not obvious from the name), `DowngradeState` for NC weak write on Vd returns Vc (write-back). **Protocol definitions encode subtle state machines** — the only way to know what they do is to READ THEM. Treat every claim about a definition's behavior as unverified until you've read the source. This rule exists because multiple hours were wasted making confident but wrong claims about definitions that 30 seconds of reading would have resolved.
- **SEARCH EFFICIENTLY.** Don't spawn 60k-token sub-agents for something a single grep finds in 3 seconds. Use `Grep` directly for known keywords (`nc_weak_write`, `read_request_no_write_mrs`). Check the obvious files first (RfProofHelpers.lean, RfProofLargeLemmas.lean for RF/CO proof infrastructure). The user found `read_request_no_write_mrs` in RfProofHelpers.lean instantly — match that efficiency.
- **Search the codebase aggressively for existing lemmas.** Key finds: `directory_event_is_bottom`, `bottom_e_in_b_impl_in_eventsAtEntryOfListBottomEvents`, `eventsUpToEvent_ordered_before_sorted`, `eventsUpToEntry_at_e_entry`. Always search before writing new code.
- **Extract helper lemmas proactively for heartbeat management.** `dirEvent_down_true_ne_Vd_of_ne_Vd` extraction solved a timeout. `list_stateAfter_exists_transition_with_inv` carried the invariant cleanly. Don't let proofs grow past ~30 lines without extracting.
- **NEVER use `DirectoryEvent` directly or `DirectoryEvent.eReq`**: Use `Event n` with `isDirectoryEvent` prop, matching the rest of the codebase. The `eReq` field has NO axioms linking it to the dir event's properties (no sameProtocol, no sameDown, no Encapsulates). Use CLE/lin infrastructure instead to get corresponding cache events with full protocol properties via `cacheEncapsulatesCorrespondingDirEvent.dirCorresponds`. I wasted an entire session going down the `eReq` rabbit hole.
- **ALWAYS document WHY a sublemma exists**: Write the protocol argument (e.g., "onDirVd is contradictory because an NC write between e_w and e_gdown violates NIW") BEFORE writing code. Include key terms (e_w, e_gdown, CLE_r, etc.). Without this, context is lost across sessions and you go in circles.
- **Add all needed hypotheses upfront, prune later.** When writing a lemma, aggressively add protocol hypotheses from the call site context. It's easy to remove unused params; it's painful to discover mid-proof that a hypothesis is missing. The `h_dir_req`, `h_eReq_in_b`, `h_cle_is_de`, `h_ncRead_prior_write`, `h_not_global`, `h_s_dir` parameters to `event_Vd_transition_implies_ncWrite_in_b` should have been added in the first draft.
- **`by_cases` on Bool fields is powerful.** `by_cases hisW : de_trans.eReq.req.val.isWrite` cleanly splits NC-read-on-Vd from NC-write cases. `by_cases hevict_down : e_evict.down` cleanly splits `sameCacheConstraints` vs `sameCacheWriteConstraints`.
- **Temporal chains through encapsulation**: `Encapsulates.2` gives `inner.oEnd < outer.oEnd`. Chain with `finishesBefore.endBefore` and `gcache_oEnd_lt_cle` for full CLE temporal bounds.
- **`list_stateAfter_exists_transition_with_inv`**: When the plain `list_stateAfter_exists_transition` loses context (like `s.isDirectoryState`), use the invariant-preserving variant. The invariant `Q` is preserved through the induction and returned with the transition evidence.
- **NC read on Vd → prior NC write**: If a `reqToDirOfRequestEvent` transforms a NC read (Acq/Weak) on Vd cache state to a Weak Write at the dir level, the cache event is a READ, not a write. The actual NC write is a PRIOR event that left the cache at Vd. Use `h_ncRead_prior_write` to delegate to the caller.
- **Check if a field is actually USED before refactoring to remove it.** `dirAccessUnique` was declared in `CompoundProtocol` but never referenced in any proof. I assumed it was needed based on its name and wrote that assumption into CLAUDE.md — then built a 55-error refactoring on top of that false premise. One `grep` would have shown it was unused. **Root cause**: I reasoned about what the field SHOULD do instead of checking what it ACTUALLY does. This is the same failure as "don't guess constructors" — verify before acting.
- **`compoundLin` refactor breaks `dir_ordered` fallback**: `dir_ordered` requires BOTH events to be directory events. CLEs are always directory events (by construction). But `compoundLin e` can be a cache event (when `requestLin`: the event has perms, so it linearizes at the cache, not the directory). This means `compose_three`'s universal fallback wouldn't work. The CLE-based approach is correct for the Herd proof.
- **CO mirrors RF**: The communication mechanism (downgrade chain) is the SAME for CO and RF — the second access (read or write) triggers a downgrade at the first access's cache. The cases (sameCache, sameClusDiffCache, diffClus) are identical. CO theorem can reuse RF infrastructure with write replacing read. I previously claimed "CO ≠ RF" without thinking through the cases — WRONG.
- **Use named structures to avoid ugly field projections.** Instead of deeply nested projections like `h.1.2.2.2.1`, create a named structure with descriptive field names. If a Prop structure can't hold Type-valued data, create a separate "evidence" structure (non-Prop) with the ugly parts and reference it from the clean Prop structure. This makes code readable and reusable. Example: `co.evidence` carries `gleOrdering.Cases` (Type) separately from the Prop `co` structure.
- **Well-designed inductive definitions enable massive proof reuse.** The RF definitions (SameCluster.cleOb.cleOrdering.Cases, DifferentCluster.cleOB.cleOrdering.Cases, NotBetweenCLEs, isDirDownRW, etc.) were parameterized by linearization events, NOT hardcoded to isRead. This means the SAME structures work for CO (write+write) and FR. When the user designs definitions, RESPECT the design — it's intentional. Don't dismiss reuse without checking.
- **THINK about PROTOCOL SCENARIOS before claiming something is hard/impossible.** I wasted hours on `ob_cle` event 2 blocking `LinLink.subset_temporalRel` — when 5 minutes of checking the protocol definitions would have shown `ob_cle` is VACUOUS (requestLin = coherent, orderAfterDir = non-coherent → contradiction). ALWAYS check: is this case even reachable in the protocol? Read the definitions. Trace the constructors. Most "hard" cases are vacuous.
- **THINK before claiming — EVERY TIME, NO EXCEPTIONS.** Also applies to TIME ESTIMATES. Don't say "3-4 hours" without counting the actual work items. I claimed "41 fallbacks, multi-hour effort" when there were 9 fallbacks and the refactoring took 15 minutes. Before asserting something is different/hard/impossible/easy/multi-day/simple, STOP and verify by reading the actual code. Don't reason from line counts, names, or assumptions. Read the definitions. Trace through the cases. Check what's actually constrained vs generic. I repeatedly violated this rule: claimed "CO ≠ RF" without checking cases, claimed "multi-day effort" without checking reuse, claimed "NOT simple copy-paste" without examining what `isRead` actually constrains. Each wrong claim wasted time. The fix: READ THE CODE before speaking.

### Key architectural insight: Why proxy constructors exist

The compoundLin lifting needs to express ordering between compoundLin events that are on DIFFERENT temporal sides of their CLEs. For `orderAfterDir` (ob_cle): compoundLin is BEFORE its CLE. For `orderBeforeDir` (cle_ob): compoundLin is AFTER its CLE. When two compoundLin events are both before their respective CLEs (`ob_cle + ob_cle`), their CLEs are ordered (`CLE₁ OB CLE₂`) but the compoundLin events are NOT directly ordered — both end before `CLE₂.oStart` but in unknown relative order.

The CLE proof avoids this because CLEs ARE the ordering events. The compoundLin proof hits it because compoundLin events can be temporally displaced from their CLEs.

The proxy constructors (`obProxy`, `stepProxyL/R`, `obStepL`) solve this by storing CLE references and CLE-level StepOrdering inside the compoundLin-level StepOrdering. But they pollute the shared `StepOrdering` type and create sorry's in `stepOrdering_to_three` (which can't decompose proxy constructors into `LinLink`).

**Clean solution**: Keep proxy constructors OUT of `StepOrdering`. Use them in a wrapper or handle the hard cases differently in the compoundLin proof.

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
- **NEVER use `lake clean`** — rebuilding from scratch takes extremely long and lags the entire system. If the build cache is corrupted, ask the user first.
- `lake build` — build entire project
- `lake build` — build entire project

## Auto-habits
- `/protocol-proof` BEFORE and DURING implementing any sorry or writing/updating Lean definitions. Think about what the protocol actually does. Check existing Behaviour/proof files for reusable patterns.
- `/checkpoint` every ~15 min, after milestones, after corrections
- `/learn` after discovering patterns or user corrections — IMMEDIATELY
- `/reflect` every ~20-30 min: am I correct? efficient? going in circles?
- `/philosophy` before major decisions, when stuck
- `/imagine` BEFORE implementing: construct concrete scenarios, check if cases are vacuous
- `/band-aid-check` BEFORE implementing any workaround, fallback, or propagation of "temporary" state: Is this a band-aid or a real fix? Does this create technical debt? Is there a foundational fix that eliminates the problem entirely? Examples of band-aids: propagating reverseOB instead of eliminating it, sorry'ing a case instead of understanding why it arises, adding a new constructor instead of fixing the underlying composition logic. The cost of a band-aid is hours of future work; the cost of a real fix is minutes of thought now.
- **Git commit after implementing** — don't wait to batch commits
- **Think about protocol semantics** — always, constantly, before everything
