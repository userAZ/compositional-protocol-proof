# Compositional Protocol Proof — Lean 4 Formal Verification

**READ FIRST: [Lessons learned](docs/learned-patterns.md) and the lessons in this file.**

## Lean mechanics lessons (reference before writing proofs)
- `▸` direction: `h_eq.symm ▸ h` when `h_eq : a = b` and you need to rewrite `a→b` in `h`
- **After `match hfc : event, isDir with | .directoryEvent de, _ =>`: the goal rewrites `event` to `.directoryEvent de`, but hypotheses DON'T.** Use `rwa [hfc₁, hfc₂]` to convert DirectoryEvent.OrderedBefore back to Event.OrderedBefore. Or use `show` to reset the goal type. Don't waste time fighting the match rewrite — learn this pattern once.
- **Dependent type transport (`Eq.mpr`/`▸` on `.choose`): use `generalize` + `subst`.** When you need `(Eq.mpr h proof).choose = proof.choose` (i.e., `.choose` is preserved through type transport): `generalize` the transported term to a fresh variable `w`, then `subst h` collapses `Eq.mpr rfl` to identity, then `rfl`. This resolved `same_cle_implies_same_gle` where `hreq's_global_lin.choose` needed to be equal for two structures with the same CLE but different `hreq's_dir_access` proofs.
- `compoundLin_cle_of_dirLin` returns `EncapsulatedBy ∧ protocol=global` — use `.1` to extract
- `reqHasPerms_not_reqMissingPerms` (Rf.lean): proves `reqMissingPerms + ¬down → ¬reqHasPerms`. Use for orderBeforeDir contradiction in dirLin branch.
- Case-split `compoundLinearizationEvent` (clusterCacheLin/clusterDirLin) AND `dirAccessOfRequest` (encapDir/orderBeforeDir/orderAfterDir) simultaneously. Matching: clusterCacheLin↔orderBeforeDir, clusterDirLin↔encapDir. Cross-cases contradictory via reqHasPerms_not_reqMissingPerms. Write helper lemmas for this matched context.
- `orderAfterDir` is NOT vacuous for `e.Encapsulates cmpLin`. Only vacuous for `cmpLin OB CLE` (self-OB). For orderAfterDir: CLE at successor, e OB successor ⊃ CLE, so e does NOT encapsulate CLE. Handle as third case (e OB cmpLin) or show it can't arise for the specific event type.
- **cmpLinLinLink (clll) must be an INDUCTIVE with h_ne.** Like CleLink, each clll constructor must carry specific protocol events AND `h_ne : l₁ ≠ l₂`. This makes irreflexivity trivial (`absurd rfl h_ne` at self-reference). The constructors mirror protocol scenarios (PPOi through e₁/e₂, COM through CLE₁/CLE₂/downgrades). This is the same pattern as CleLink/StepOrdering/LinLink. Don't use opaque `TemporalRel` as the sole ranking — use specific named temporal evidence that implies `h_ne`.
- **CmpLinCleRel.cle_ob now carries h_not_dir.** `cle_ob` → cmpLin is NOT a directory event (from requestLin = cache event). This enables h_ne derivation for cle_ob+eq suffix case (cache ≠ dir).
- **Write inductive definitions with cases carrying protocol scenario info.** Don't be afraid of writing new inductives. When you need to track information through case-splits (like `cmpLin = e` from requestLin), use an inductive where each constructor carries the relevant evidence. Disjunctions (`∨`) lose the connection between cases and their evidence. An inductive with named constructors preserves it. Example: `CmpLinEventRel` should carry `cmpLin = e` in its requestLin constructor, not just `¬ isDirectoryEvent`.
- **Write inductive definitions with cases carrying protocol scenario info.** Don't be afraid of writing new inductives where each constructor carries the relevant protocol evidence. When you need to track information through case-splits (like `cmpLin = e` from requestLin), use an inductive where each constructor carries the equation explicitly. Disjunctions (`∨`) lose the connection between cases and their evidence after pattern matching. An inductive with named constructors preserves it. This is the FUNDAMENTAL technique for this project — CleLink, LinLink, CmpLinCleRel, FrOrdering all follow this pattern.
- **Don't go in circles on type issues.** When `▸`/`rw` fail because existentials from pattern matching lose connection to original parameters, use `compoundLin_event_rel` which returns equations with the ORIGINAL event parameters (not existentials). Or write a new inductive that carries the equation with the original param.
- **Use OB/Encap/EncapBy for temporal evidence, not FinishesBefore.** `event_oEnd_lt` (= FinishesBefore) is the weakest temporal relation. Many edges have STRONGER evidence: PPOi has `e₁ OB e₂`, COM has CLE₁ OB CLE₂, etc. Edge structures should carry or derive OB/Encap/EncapBy between the appropriate proxy events. `event_oEnd_lt` should be REPLACED with the stronger relation where available. This gives h_ne directly (OB/Encap/EncapBy all imply strict oStart inequality → h_ne). Don't think of `event_oEnd_lt` as a "fallback" — think of ALL temporal relations as tools, and use the strongest one.

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
7b. **THINK about what you're saying before saying it.** You've likely forgotten some key detail in the protocol. Think about the protocol's cases carefully and deeply. Don't claim something is vacuous without tracing through ALL protocol cases. Don't claim a direction is impossible without checking every dirAccessOfRequest case for every request type.
7c. **DOUBLE-CHECK every claim before presenting it.** Don't say "all uses are legal" without verifying each one. Don't say "this branch is dead" without proving it. The user should not have to audit every item in depth. Verify YOURSELF, thoroughly, before reporting.
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

## THE PHILOSOPHY — cmpLin ordering through proxy events (READ THIS BEFORE EVERY PROOF)

**cmpLin events are NOT directly ordered.** Two compoundLin events (cmpLin₁, cmpLin₂) from different cache events at different caches/clusters have NO direct temporal constraint between them (the caches may take extra internal cycles). Instead, they are ordered THROUGH PROTOCOL PROXY EVENTS.

The `cmpLinLinLink` relation captures this: a `TransGen` chain of OB/Encap/EncapBy/FinishesBefore steps that goes through NAMED PROXY EVENTS from the protocol definitions. The chain does NOT go directly from cmpLin₁ to cmpLin₂ — it goes through the communication mechanism.

**Example: RF with e_w and e_r in different clusters (generalizes to other cases):**
```
cmpLin_w → ... → e_w OB e_r_cache_downgrade
                       → e_r_cache_downgrade EncapBy e_r_cdir_downgrade
                       → e_r_cdir_downgrade EncapBy e_gcache_downgrade
                       → e_gcache_downgrade EncapBy GLE_r
                       → GLE_r EncapBy e_r_gcache
                       → e_r_gcache {EncapBy or FinishesBefore} CLE_r
                       → CLE_r related to e_r by dirAccessOfRequest:
                         - orderBeforeDir: CLE_r EncapBy predecessor, predecessor OB e_r (cmpLin_r = e_r)
                         - encapDir: CLE_r EncapBy e_r (cmpLin_r inside CLE_r)
                         - orderAfterDir: CLE_r EncapBy successor, CLE_r OB successor
                       → ... → cmpLin_r
```

Each step in this chain names a SPECIFIC PROTOCOL EVENT (downgrade, directory event, GLE, predecessor, etc.). This is the communication mechanism that the protocol uses to propagate coherence.

**The chain shape varies by protocol scenario — NOT all chains go through both CLEs:**
- **RF coherent writer, same cluster:** `cmpLin_w (= e_w) →(OB)→ e_r_cdir_down →(EncapBy)→ CLE_r →(...)→ cmpLin_r`. NO CLE_w — writer has perms so cmpLin_w = e_w (requestLin), chain goes directly through the downgrade.
- **RF non-coherent writer, same cluster:** `cmpLin_w →(EncapBy)→ CLE_w →(OB)→ CLE_r →(...)→ cmpLin_r`. CLE_w IS in chain — cmpLin_w inside CLE_w (dirLin).
- **RF cross-cluster:** `cmpLin_w →(...)→ CLE_w →(...)→ GLE_w →(OB)→ GLE_r →(...)→ CLE_r →(...)→ cmpLin_r`. Both CLEs and GLEs.
- **CO sameCache:** Shared CLE. If cmpLin = e (cle_ob): `cmpLin₁ →(OB)→ cmpLin₂` directly. If cmpLin inside CLE: `cmpLin₁ →(EncapBy)→ CLE →(Encap)→ cmpLin₂`.
- **PPOi:** `cmpLin₁ →(OB)→ cmpLin₂` directly from NonLazyPPOi.

CmpLinCleRel (eq/cle_ob/inside) determines WHICH chain pattern: eq → skip CLE, cle_ob → direct from e, inside → go through CLE via EncapBy. EXAMINE each scenario before coding.

**The acyclicity uses a three-level protocol hierarchy:**
1. **GLE OB** (global directory): cross-cluster edges advance GLE. gleOrdering.Cases gives GLE₁ OB GLE₂ or GLE₁ = GLE₂ — never backward.
2. **CLE OB** (cluster directory): same-GLE edges within a cluster. CLE₁ OB CLE₂ from CleLink.
3. **Event OB** (cache): same-CLE edges at same cache. e₁ OB e₂ from cache serialization.
OB is transitive and irreflexive (self-OB → e.oEnd < e.oStart → contradicts well-formedness). A cycle composes OB at the highest applicable level → self-OB → contradiction.

**ProtoForwardStep IS an irreflexive subset of TemporalRel.** Each step carries:
- The irreflexive transitive chain of {OB, Encap, EncapBy, finishesBefore} between cmpLin events (prioritize OB/Encap/EncapBy over finishesBefore)
- The GLE/CLE/event OB witness for composition and irreflexibility
- Named proxy events from the specific protocol scenario
The chain IS the proof content. The OB level IS the acyclicity mechanism. Both are needed.

**How to open up compoundLin defs (from user guidance):**
When doing `cases` on `compoundLinearizationEvent`, you get `clusterCacheLin` (has perms) or `clusterDirLin` (no perms). Do `cases` on `dirAccessOfRequest` simultaneously — the sub-cases must LINE UP:
- `clusterCacheLin` ↔ `orderBeforeDir` (event has perms)
- `clusterDirLin` ↔ `encapDir` (event missing perms)
Cross-cases are contradictory (reqHasPerms vs reqMissingPerms). Write a helper lemma that does this matched case-split and extracts the relevant context. See CompoundPPOs.lean line 619+ for examples of this pattern.

**THIS IS WHAT THE PROOF MUST SHOW.** The acyclicity proof must demonstrate that each edge produces a cmpLinLinLink chain through proxy events. A cycle of such chains would require a proxy event to be temporally before itself → contradiction.

**ENSURE YOUR PROOFS FOLLOW THIS PHILOSOPHY.** Before writing any proof code, ask: "Does this proof show the proxy chain? Does it name the protocol events?" If the proof just uses an opaque oEnd ranking without naming proxies, it's NOT following the philosophy. The proxy chain IS the proof — the ranking is derived FROM the chain.

**The cmpLinLinLink relation IS the RF/CO/FR definitions' chains drawn out.** Read the RF def. The communication cases (sameCluster, diffCluster, etc.) describe EXACTLY these proxy chains. The proof should mirror these cases.

### How compoundLin events are related

Each event `e` has a linearization `lin e` which provides:
- `lin.compoundLin` — the compoundLin event (the linearization point)
- `lin.cle` — the CLE (cluster directory event from `dirAccessOfRequest`)
- `lin.gle` — the GLE (global directory event)

The proxy events are related through **4 temporal relations**:
- **OB** (OrderedBefore): `a.oEnd < b.oStart`
- **Encapsulates**: `a.oStart < b.oStart ∧ b.oEnd < a.oEnd`
- **EncapsulatedBy**: reverse of Encapsulates
- **FinishesBefore**: `a.oEnd < b.oEnd`

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

### How cmpLin connects to CLE through dirAccessOfRequest proxy events

Each event `e` has a `dirAccessOfRequest` which determines how its cmpLin relates to its CLE:

**encapDir**: `e` doesn't have perms → CLE encapsulates `e` → cmpLin is INSIDE CLE.
  The CLE is the directory event that processes `e`'s request directly.
  Proxy chain: cmpLin ← (inside) ← CLE

**orderBeforeDir**: `e` HAS perms (a PREDECESSOR got them) → cmpLin = `e` itself (requestLin).
  The CLE belongs to the PREDECESSOR that got perms. The predecessor encapsulates
  a directory event (the CLE). The connection: predecessor OB `e`, CLE encaps predecessor.
  Proxy chain: CLE ← (encaps) ← predecessor → (OB) → e = cmpLin
  **KEY EXAMPLE**: In RF, the reader `e_r` can have cmpLin = `e_r` itself, because
  a predecessor got permissions through a dir access which triggered the downgrade
  of the prior writer `e_w`. The predecessor + its dir event ARE the proxy events.

**orderAfterDir**: NC weak on Vd → cmpLin is BEFORE CLE (successor's dir event).
  Currently proved vacuous (compoundLin_not_ob_cle): reqHasPerms contradicts ncWeakReqOnVd.
  **Re-examined (2026-04-05):** NC weak write on Vd CAN have dirAccessOfRequest.orderAfterDir.
  BUT: reqHasPerms has 3 constructors: (1) isCoherent+hasPerms, (2) ncRelAcqWeakWrite+coherentState,
  (3) ncWeakRead+notVd. For NC weak write on Vd: (1) fails (non-coherent), (2) fails (Vd has c=false,
  reqHasPermsOnCoherentState needs c=true), (3) fails (not a read). So reqHasPerms is False for
  NC weak write on Vd → requestLin doesn't apply → linearizationOfEvent gives dirLin →
  compoundLin = CLE → compoundLin OB CLE = CLE OB CLE = self-OB = False.
  So the vacuity IS correct. orderAfterDir events always go through dirLin (compoundLin = CLE),
  never through requestLin (compoundLin = e). The proof compoundLin_not_ob_cle is sound.

The `LinLink.proxy` constructor should EXPLICITLY show these proxy connections —
not hide them in an opaque `TemporalRel`. Each case (encapDir, orderBeforeDir)
gives a specific proxy chain that should be visible in the type.

### What the user wants (cmpLin migration)

The edge definitions (PPOi, rfe, co, fr) must:
1. Use `lin₁ lin₂` (linearization evidence) as PRIMARY parameters, not cache events
2. Carry `cmpLin_ordered : CmpLinOrdering lin₁.compoundLin lin₂.compoundLin` — explicitly stating how the compoundLin events are temporally related
3. The CmpLinOrdering relates compoundLin events through OB, Encap, EncapBy, FinishesBefore — connected through proxy events from dirAccessOfRequest:
   - **encapDir**: CLE encapsulates `e` → compoundLin is INSIDE CLE (Encap)
   - **orderBeforeDir**: predecessor's CLE gave perms → compoundLin is AFTER CLE (CLE OB compoundLin)
   - **orderAfterDir**: successor's CLE → compoundLin is BEFORE CLE (vacuous ob_cle)
   - The CLE itself or GLE acts as the proxy connecting two compoundLin events

The acyclicity proof uses `event_oEnd_lt` (e₁.oEnd < e₂.oEnd) as the proof mechanism. The cmpLin_ordered field provides the PRESENTATION of how compoundLin events are ordered through the protocol's directory access evidence.

## Current goal: Herd CMCM acyclicity proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` in `CMCM/Herd/Proof.lean`.

### Status (updated 2026-04-05)
- **1 sorry remaining**: `compoundLin_eq_or_inside_event` orderAfterDir case (NC weak req on Vd). CLE is at successor, e does NOT encapsulate CLE. Different from encapDir/orderBeforeDir.
- **PPOi `cmpLin_ordered` DERIVED** with explicit proxy chain through e₁, e₂ (EncapBy + OB + Encap).
- **LinLink.ppoProxy** constructor: connects cmpLin through request events.
- **`cmpLin_ordered` removed** from ALL edge structures (PPOi/rfe/co/fr).
- **`event_oEnd_lt` remains** on rfe/co/fr as ranking measure (cmpLin oEnd not directly derivable).
- **orderAfterDir is NOT vacuous for e.Encapsulates cmpLin.** For NC weak req on Vd: cmpLin = CLE at successor, e OB CLE (not encaps). Need third case in compoundLin_eq_or_inside_event or different handling.

### TODO — cmpLin migration (2026-04-06)
1. **DONE: PPOi `cmpLin_ordered` derived** from NonLazyPPOi.
2. **DONE: `cmpLin_ordered` field removed** from rfe/co/fr. Derived via `com_cmpLin_ordered`. NOTE: rfe is based on rf — the rf definition is the foundation.
3. **IN PROGRESS: `cmpLinLinLink` acyclicity via protocol proxy chain.**
   - `cmpLinLinLink` (Proof.lean) bundles R_hknow edge + CmpLinOrdering proxy chain.
   - `edge_to_cmpLinLinLink` lifts every R_hknow edge to cmpLinLinLink.
   - `cmcm_acyclic_of_hknow_compoundLinOrdering` lifts R_hknow cycle to cmpLinLinLink cycle → contradiction.
   - Theorem flow: `cmpLinLinLink_acyclic` → `cmcm_acyclic_of_hknow_compoundLinOrdering` → `cmcm_acyclic` → `cmcm`.
   - **DONE: ProtoForwardStep defined with 15 protocol-derived cases.**
     - Cases mirror RF/CO/FR/PPOi definitions with meaningful names and named proxy events.
     - Each constructor carries: CmpLinCleRel (cmpLin→CLE link), protocol OB (GLE/CLE/event), named proxies.
     - ProtoOBLevel for 3-level composition (GLE OB / CLE OB / event OB). Transitive + irreflexive.
     - cmpLinLinLink_acyclic: sorry-free (composes via proto_forward_trans, closes via proto_forward_irrefl).
   - **STATUS (2026-04-07): 19 sorry's. Definitions correct. cmpLinLinLink_acyclic sorry-free.**
     - PPOi cmpLin OB: PROVABLE (needs compoundLin_eq_linearizationEvent reordered above usage) (1)
     - Reverse contradictions in derive_gle_ob'/derive_cle_ob_same_cluster: unprovable with event_fb alone. Need either same_cle_implies_same_gle or vacuity argument (3)
     - event_ob_of_same_cache: heartbeat timeout, proof correct (1)
     - CO/FR GLE direction edge cases: likely vacuous (same CLE → same GLE not proven) (3)
     - FR gle_ordering field + h_fr_gle parameter: RESOLVED via fr.gle_ordering field
     - CO gle_ob in diffClus: RESOLVED via co.ordering.diffClus field
     - Chain presentation (.chain): NOT acyclicity-critical, deferred (11)
   - **PREVIOUS TODO: Fill sorry's in ProtoForwardStep infrastructure (31 total):**
     - **Category A: `.level` — derive ProtoOBLevel (3 sorry's)**
       - `co_sameCache`: same CLE → derive GLE eq → eventOB level
       - `fr_sameClusDiffCache`: derive GLE eq from same-cluster evidence
       - `fr_sameCLE`: same CLE → derive GLE eq → eventOB level
     - **Category B: `edge_to_proto_forward` — derive GLE OB / CLE OB from protocol evidence (~12 sorry's)**
       - PPOi: derive ProtoOBLevel from NonLazyPPOi + compound protocol structure
       - RF wEqRGle: derive CLE₁ OB CLE₂ from CleLink within same GLE
       - CO sameClusDiffCache: derive GLE eq + CLE OB from co.ordering evidence
       - CO crossCluster: derive GLE₁ OB GLE₂ from gleOrdering (need co.evidence access)
       - FR diffCluster_* (×5): derive GLE₁ OB GLE₂ from FR protocol evidence
       - FR sameCache: derive ProtoOBLevel
       - FR sameCLE: derive e₁ OB e₂ from cache ordering
     - **Category C: `.chain` — construct TemporalRel from CmpLinCleRel + proxy OB (~14 sorry's)**
       - For each constructor: compose CmpLinCleRel₁ + middle OB + CmpLinCleRel₂ into TemporalRel
       - Existing `cle_to_compoundLinOrdering` infrastructure handles most patterns
     - **Category D: `proto_forward_trans` — CmpLinCleRel for composed steps (2 sorry's)**
       - Need CmpLinCleRel at composition boundaries (derivable from hknow)
4. **Name proxy events meaningfully** in LinLink constructors and CleLink. Use names like `writerCLE`, `readerCLE`, `cdir_downgrade`, `gcache_downgrade`, `predecessor`, `successor` — NOT single-letter variables like `p`, `q`, `e₁'`. The user's definitions always use meaningful names.
5. **Update LinLink.proxy to use meaningful proxy event names** — rename fields to describe WHAT the proxy events are in the protocol (predecessor CLE, downgrade event, etc.)

### TODO — other

- **h_ne approach**: Non-eq CleLink constructors carry `h_ne : l₁ ≠ l₂`. At self-reference, non-eq cases close with `absurd rfl h_ne`. sameLin closes with temporal chain (CLE.oEnd < e₁'.oEnd < e₂'.oStart < CLE.oStart < CLE.oEnd). eq delegates to cycle_eq_closure.
- **PPOi (diff-addr) + CLE equality**: Impossible. CLE.addr = e.addr (from dirAccessOfRequest.dirCorresponds.sameAddr), so CLE₁=CLE₂ → e₁.addr=e₂.addr → contradicts addr≠.
- **rfe + CLE equality**: Impossible. Case-split CleLink → non-eq/sameLin give contradiction. eq case: case-split readsFrom → all sub-cases give OB/oEnd chains that contradict CLE₁=CLE₂.
- **Key theorems**:
  - `cmpLinLinLink_acyclic`: Core acyclicity proof on cmpLinLinLink (event_oEnd_lt per edge).
  - `cmcm_acyclic_of_hknow_compoundLinOrdering`: Lifts R_hknow → cmpLinLinLink → acyclic.
  - `cmcm_acyclic_of_hknow`: Standalone event-level acyclicity (event_oEnd_lt directly).
  - `edge_to_cmpLinLinLink`: Lifts R_hknow edge to cmpLinLinLink (adds CmpLinOrdering).
  - `edge_cmpLin_ordered`: Derives CmpLinOrdering for any R_hknow edge (notdown/notdir internal).
  - `CleLink.subset_temporalRel` (Defs.lean): Every CleLink decomposes into TransGen BasicTemporalRel.
  - `compoundLin_not_ob_cle` (Proof.lean): ob_cle always vacuous (MR+NCWeakWrite protocol-impossible).
  - `co_ordering_holds` (CoTheorem.lean): CO theorem from protocol axioms.
- **Architecture**:
  - `cle_path_invariant`: Reusable CLE-level induction (CleLink/eq/reverse on CLEs from any path).
  - COM evidence flow: edge → step_to_ordering → CleLink → cle_to_compoundLinOrdering → CmpLinOrdering (LinLink/eq/reverse).
  - Theorem flow: `cmpLinLinLink_acyclic` → `cmcm_acyclic_of_hknow_compoundLinOrdering` → `cmcm_acyclic` → `cmcm`.
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

### Critical self-management rules (2026-04-05)
- **BE EFFICIENT, FOCUSED, AND DIRECTED.** Don't deliberate endlessly. Don't write paragraphs of analysis when code is needed. Write the code, build, fix, commit. Stop wasting tokens on analysis that doesn't lead to code changes.
- **FINISH WHAT YOU START.** When the user asks for a task, COMPLETE IT FULLY. Don't leave items partially done and call it "a first step." The user should not have to audit every claim. Implement ALL items, verify ALL items, then report honestly.
- **AUDIT YOURSELF against the TODOs before claiming done.** After implementing, go through each TODO item and verify: did I actually do this? Is the code honest? Did I cut corners? If ANY item is incomplete, say so — don't claim the task is done.
- **BE PRECISE about what you're talking about.** "oEnd" is meaningless without specifying WHICH event — the cache event? the compoundLin event? the CLE? Always say `Event.oEnd n cmpLin` or `Event.oEnd n e₁` or `CLE.oEnd`. Vagueness causes confusion and wastes the user's time.
- **USE MEANINGFUL VARIABLE NAMES.** Not `p`, `q`, `e₁'` — use `writerCLE`, `readerCLE`, `cdir_downgrade`, `predecessor`, `successor`. The user's definitions always use meaningful names. Mathematicians use single-letter names but that loses protocol meaning. Name variables for WHAT THEY ARE in the protocol.
- **rfe is based on rf, NOT the other way around.** The rf definition is the foundation. rfe adds the "external" (different cache) constraint. Always think about rf first, then rfe as a specialization.
- **THINK ABOUT WHAT YOU'RE SAYING IN THE PROTOCOL.** Before claiming something is done or impossible, /reflect: What does this mean in the actual cache coherence protocol? What are the physical events? Which cache/cluster/directory does each event belong to? What communication mechanism connects them? If you can't answer these questions, you don't understand the proof well enough to implement it.
- **The CLE is where requests from different caches/clusters MEET.** The directory processes requests from multiple caches. The CLE is the directory access event. This is why the cycle goes through CLEs — they're the communication rendezvous point.
- **ENSURE PROOFS FOLLOW THE PHILOSOPHY.** Before writing ANY proof, re-read "THE PHILOSOPHY" section above. Ask: does this proof show the proxy chain through named protocol events? If not, it's wrong. The philosophy is NON-NEGOTIABLE. Don't use opaque oEnd rankings that skip the proxy chain.
- **The proxy chain IS the RF/CO/FR definitions drawn out.** Read the actual RF def (`Behaviour.readsFrom.cases`). The communication cases describe the exact proxy chains. Mirror them in the proof. Don't invent abstract alternatives.
- **cmpLin events are NOT directly constrained.** Different cache events at different caches/clusters have no direct OB/Encap/etc constraint. They're connected ONLY through proxy events (downgrades, CLE, GLE, predecessor, successor). NEVER assume cmpLin₁.oEnd < cmpLin₂.oEnd as a field — DERIVE it from the proxy chain.
- **rfe is based on rf.** The rf definition is the foundation. rfe adds "external" (different cache). Always think about rf first.

### Lessons learned (acyclicity via protocol proxy chain, 2026-04-06)
- **edge_oEnd_lt is raw arithmetic with NO protocol meaning — NEVER USE IT.** e₁.oEnd < e₂.oEnd on cache events at different caches says nothing about why the protocol prevents cycles. It composed trivially (Nat.lt_trans) which masked the actual protocol mechanism. I forgot this lesson MULTIPLE TIMES and kept reverting to oEnd. NEVER use edge_oEnd_lt as the acyclicity mechanism. The proof must use the protocol proxy chain.
- **The acyclicity proof IS the protocol proxy chain.** Each clll step IS a TransGen of {OB, Encap, EncapBy, finishesBefore} through cmpLin → CLE → GLE → ... → CLE → cmpLin. The chain goes through NAMED protocol events. The acyclicity IS the chain's irreflexivity. The chain is the proof. Not numbers derived from the chain — THE CHAIN ITSELF.
- **cmpLin must be part of the chain.** The full chain: cmpLin₁ →(CmpLinCleRel)→ CLE₁ →(CleLink through proxies, possibly GLE)→ CLE₂ →(CmpLinCleRel)→ cmpLin₂. Not just CLEs. Not just numbers. The FULL proxy chain connecting cmpLin through CLE through GLE is the proof.
- **Prioritize {OB, Encap, EncapBy} over finishesBefore.** finishesBefore is the WEAKEST temporal relation — it only says oEnd₁ < oEnd₂ with no oStart constraint. OB, Encap, EncapBy carry FULL interval information and are the primary protocol relations. Use finishesBefore only when OB/Encap/EncapBy are genuinely insufficient (cross-cluster cases where only oEnd bound is available). Always look for OB/Encap/EncapBy FIRST.
- **Two-level protocol ordering for acyclicity:**
  (a) GLE level: gleOrdering.Cases gives GLE₁ OB GLE₂ or GLE₁ = GLE₂ (NEVER backward for COM edges). Cross-cluster edges advance GLE.
  (b) CLE level (within same GLE): LinChain (OB + Encap on CLEs), acyclic via oStart_lt.
  The chain goes through cmpLin → CLE → GLE with OB/Encap/EncapBy between these events. The acyclicity follows from the chain structure, not from a separate numeric ranking.
- **CleLink.obFinishBefore (cross-cluster) doesn't give CLE oStart increase.** But gleOrdering.Cases for COM guarantees GLE forward progress for this case. The GLE level handles cross-cluster; the CLE level handles same-cluster.
- **TransGen {OB, Encap, EncapBy, finishesBefore} is NOT acyclic in general.** Encap + finishesBefore can cycle (l₁ encaps l₂ trivially gives finishesBefore(l₂, l₁)). BUT the specific chains from the protocol are acyclic because they go through the two-level GLE/CLE structure.
- **LinChain (TransGen LinStep = ob | encap) IS acyclic** via oStart_lt. This is the CLE-level ranking within same GLE. All non-obFinishBefore CleLink constructors decompose to LinChain.
- **obEndLt and encapObEndLt: dir_ordered forces forward direction.** If l₂ OB l₁ for these, the temporal chain gives p.oEnd < p.oStart contradiction. So l₁ OB l₂ must hold → LinStep.ob.
- **Single-step irreflexivity (h_ne) is NOT transitive-closure irreflexivity.** CleLink.irrefl (h_ne per constructor) proves CleLink l l → False. But TransGen CleLink l l needs the chain structure to show the cycle can't close. The oEnd_lt approach bypassed this with arithmetic; the correct approach uses the protocol proxy chain.
- **NEVER use single numeric measures (GLE.oStart, CLE.oStart, oEnd) as rankings.** These are CONSEQUENCES of OB/Encap, not independent facts. The proof should say "GLE₁ OB GLE₂" (protocol relation between named events), not "GLE₁.oStart < GLE₂.oStart" (arithmetic on numbers). OB is transitive and irreflexive (self-OB contradicts well-formedness). The acyclicity composes OB steps through the cycle → self-OB → contradiction. No Nat.lt_trans on raw values.
- **Plan clll inductive cases from the RF/FR/CO DEFINITIONS.** Look at `Behaviour.readsFrom.cases` (wEqRGle/wObRGle), `gleOrdering.Cases` (sameGle/wObRGle), `FrOrdering`, `co.ordering`. These define the protocol communication scenarios. The clll cases should MIRROR these scenarios, carrying the same proxy events (CLE, GLE, downgrades, predecessors). Don't invent abstract cases — derive them from the protocol definitions.
- **ProtoForwardStep IS an irreflexive subset of TemporalRel.** Each ProtoForwardStep carries a TemporalRel chain (TransGen BasicTemporalRel) between cmpLin events through named protocol proxy events. TemporalRel itself is NOT irreflexive (encap+finishesBefore can cycle). But ProtoForwardStep IS irreflexive because each constructor also carries GLE OB, CLE OB, or event OB — and OB is irreflexive. The TemporalRel chain is the PROOF CONTENT (showing the mechanism); the GLE/CLE/event OB is the ACYCLICITY WITNESS (enabling composition and irreflexibility). Both are needed. I keep forgetting this — the chain is not just decoration, and the OB is not just arithmetic.
- **Not all chains go through both CLEs — EXAMINE EACH PROTOCOL SCENARIO.** The chain shape varies by scenario. Don't force a uniform cmpLin→CLE→middle→CLE→cmpLin template. Concrete examples:
  - **RF coherent writer, same cluster:** `cmpLin_w (= e_w) →(OB)→ e_r_cdir_down →(EncapBy)→ CLE_r →(...)→ cmpLin_r`. NO CLE_w in chain — e_w has perms so cmpLin_w = e_w, chain goes directly from e_w through the downgrade.
  - **RF non-coherent writer, same cluster:** `cmpLin_w →(EncapBy)→ CLE_w →(OB)→ CLE_r →(...)→ cmpLin_r`. CLE_w IS in chain — cmpLin_w is inside CLE_w (dirLin).
  - **RF cross-cluster:** `cmpLin_w →(...)→ CLE_w →(...)→ GLE_w →(OB)→ GLE_r →(...)→ CLE_r →(...)→ cmpLin_r`. Both CLEs and GLEs in chain.
  - **CO sameCache:** Shared CLE. If cmpLin = e (cle_ob): `cmpLin₁ (= e₁) →(OB, from e₁ OB e₂)→ cmpLin₂ (= e₂)`. If cmpLin inside CLE: `cmpLin₁ →(EncapBy)→ CLE →(Encap)→ cmpLin₂`.
  - **PPOi:** `cmpLin₁ →(OB)→ cmpLin₂` directly from NonLazyPPOi.
  The CmpLinCleRel tells you WHICH chain pattern to use (eq → skip CLE, cle_ob → direct from e, inside → go through CLE via EncapBy). But the chain itself follows the protocol flow, not a template.
- **VERIFY ProtoForwardStep against /philosophy after EVERY change.** Checklist: (1) Does it carry the irreflexive transitive chain of {OB, Encap, EncapBy, finishesBefore} between cmpLin events? (2) Does it carry GLE/CLE/event OB for acyclicity? (3) Are the cases derived from protocol definitions (RF/CO/FR)? (4) Does it use {OB, Encap, EncapBy} (prioritized over finishesBefore)? (5) Does it name the ACTUAL protocol proxy events for each scenario (not a uniform template)? Run this checklist BEFORE committing.
- **USE MEANINGFUL PARAMETER NAMES — ALWAYS.** Not `h_rel₁`, `h_rel₂`, `h` — use `writerCmpLinRel`, `readerCle`, `writerGle_ob_readerGle`, `readerDowngrade`. The names should say WHAT the event IS in the protocol (writer's CLE, reader's downgrade, etc.). A reviewer should understand the proof from the names alone. This applies to ProtoForwardStep constructors, CleLink evidence, CmpLinCleRel, and ALL protocol proof terms.
- **APPROACH: Define definitions well BEFORE starting proofs.** When the definitions properly reflect the protocol (cases from RF/CO/FR, meaningful names, named proxy events), the sorry's become concrete and mechanical — each says exactly what to prove. This eliminates "is this the right goal?" questions. Steps: (1) /imagine the protocol scenarios and chain shapes, (2) write constructors with meaningful names, (3) build — sorry's reveal exactly what evidence is needed, (4) fill sorry's mechanically. Define first, prove second.
- **UNIFY LESSONS periodically** (every ~30 min or after breakthroughs). New lessons go to /protocol-proof staging → unify into Hard Rules or Step 0 → clear staging. Don't let lessons accumulate unintegrated.
- **MAINTAIN A TODO LIST of where you are and where you need to get to.** After defining the structure, list all sorry's and categorize them. Track progress. This keeps sight of the goal and prevents going in circles.
- **FR GLE ordering depends on RF sub-case.** FR = rf⁻¹;co. RF gives GLE_w vs GLE_reader. CO chain gives GLE_w vs GLE_writer. For wEqRGle (GLE_w = GLE_reader): GLE_reader ≤ GLE_writer IS derivable from CO chain. For wObRGle (GLE_w OB GLE_reader): GLE_reader vs GLE_writer is UNKNOWN — need `gleOrdering.Cases` as additional input (like CO theorem receives). Don't assume FR GLE ordering is always derivable — only the wEqRGle sub-case works.
- **WRITE HELPER LEMMAS TO CLEAR GROUPS OF SORRY'S.** Before filling sorry's individually, look for a SHARED PATTERN across multiple sorry's. One helper lemma resolving the pattern clears the whole group. Proven examples from this project:
  - `temporalRel_of_cleOB_and_cmpLinCleRels`: handles all 9 CmpLinCleRel × CmpLinCleRel cases for CLE OB chains → resolved 4 sorry's at once.
  - `temporalRel_of_gleOB_and_cmpLinCleRels`: CLE direction from dir_ordered + GLE OB → resolved 7 sorry's.
  - `diff_protocol_implies_diff_gle`: contrapositive of `same_gle_implies_same_protocol` → resolved 6 sorry's.
  Always ask: "Is there ONE theorem that would resolve 3+ sorry's?" before filling individually.
  - `same_cle_implies_same_gle` (Defs.lean): same CLE → same GLE. Used generalize+subst for dependent type transport. Resolves GLE equality for same-CLE cases in `.level`.
- **NEVER carry reverse cases forward.** When a 3-way (forward/eq/reverse) arises, contradict the reverse IMMEDIATELY using the available OB evidence (GLE OB, CLE OB, event OB). The protocol guarantees forward direction — reverse is always contradictory. Don't propagate TemporalRel_reverse through the proof. Eliminate it on the spot with exfalso. This applies to CmpLinOrdering, CleLink composition, and any 3-way case split.
- **CONSULT THIS SECTION AS /philosophy BEFORE EVERY PROOF STEP.** I have repeatedly forgotten these lessons and reverted to arithmetic shortcuts. Before writing ANY proof code for acyclicity: re-read this section. Ask: "Am I using the protocol chain or a numeric shortcut?" If numeric shortcut → STOP and use the chain.

### Lessons learned (cmpLin h_ne derivation, 2026-04-06)
- **For cmpLin h_ne: case-split on linearizationOfEvent, not compoundLin_event_rel.** The linearizationOfEvent gives requestLin (cmpLin = e) or dirLin (cmpLin at directory level). This is cleaner than the 3-way from compoundLin_event_rel because requestLin directly gives cmpLin = e (the cache event).
- **requestLin × dirLin-eq closes via isDirectoryEvent.** CLE is always a directory event. requestLin gives cmpLin = e (cache, ¬ dir). At eq: cache = dir → contradiction.
- **requestLin × dirLin-inside closes via protocol.** compoundLin_cle_of_dirLin gives protocol = .global for the inside case. Cache events have cluster protocol (from isClusterCache.eCluster). At eq: cluster ≠ global.
- **dirLin × dirLin is the genuine protocol gap.** Both events go through directory linearization. The compoundLin events are at the directory/global level. Proving they're distinct requires protocol injectivity — that the linearization chain produces distinct events for different cache events.
- **Thread isClusterCache through the call chain.** Needed for the cluster ≠ global argument. PPOi/COM edges carry cache₁/cache₂ : isClusterCache. Thread through edge_cmpLin_ordered → com_cmpLin_ordered → edge_cmpLin_linlink → cle_to_compoundLinOrdering → cmpLin_ne_of_event_fb.

### Lessons learned THIS SESSION (cmpLin migration, 2026-04-05)
- **cmpLin events are NOT directly constrained.** Different cache events at different caches/clusters have no direct OB/Encap/etc between their cmpLin events. The ordering goes ONLY through protocol proxy events (CLE, downgrades, GLE, predecessor, successor).
- **Don't assume ordering fields — derive them from the protocol.** `cmpLin_oEnd_lt` was wrong to add as a field. The ordering must come from the proxy chain (cmpLinLinLink) that traces through the RF/CO/FR definitions.
- **The RF/CO/FR definitions already describe the proxy chains.** Read `step_to_ordering` — it extracts CleLink from the RF cases. The CleLink constructors (ob, obEndLt, encapOb, etc.) name the proxy events. Mirror these in the cmpLinLinLink relation.
- **When stuck, ask for a guiding protocol example.** The user's diff-cluster RF example (e_w OB e_r_down, e_r_down EncapBy e_r_cdir_down, ..., CLE_r related to e_r) unblocked the entire approach. Don't go in circles — ask.
- **Always give protocol context.** "oEnd" is meaningless without specifying WHICH event. Say `Event.oEnd n cmpLin₁` or `Event.oEnd n e_writer` or `CLE_reader.oEnd`. Vagueness wastes the user's time.
- **Finish what you start.** Don't claim a task is done when items remain. Audit against the TODOs before reporting. The user should not have to audit.
- **The philosophy must guide the proof.** Before writing ANY proof code, re-read THE PHILOSOPHY section. If the proof doesn't show the proxy chain through named protocol events, it's wrong.

### Lessons learned PREVIOUS SESSION (CleLink h_ne refactoring)
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
