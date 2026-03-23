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

## Current goal: Herd CMCM acyclicity proof

Prove `acyclic(PPOi ∪ rfe ∪ fr ∪ co)` in `CMCM/Herd/Proof.lean`.

### Status
- **rfe**: DONE (`rfe_hierarchicallyOrdered` — uses `wObRGle` for GLE ordering)
- **co**: DONE (carries `hierarchicallyOrdered` directly in structure)
- **fr**: DONE (carries `hierarchicallyOrdered` directly in structure)
- **PPOi same-addr**: PARTIAL — `ppoi_hierarchicallyOrdered_same_addr`
  - CLE₁ = CLE₂ case: DONE (level 3 via `hierarchicallyOrdered_of_same_cle`)
  - CLE₁ OB CLE₂ + GLE₁ OB GLE₂: DONE (level 1)
  - CLE₁ OB CLE₂ + GLE₂ OB GLE₁: sorry (CLE→GLE propagation for same-addr)
  - CLE₂ OB CLE₁: sorry (predecessor elimination)
- **PPOi diff-addr**: PARTIAL — `ppoi_hierarchicallyOrdered_diff_addr`
  - GLE₁ OB GLE₂: DONE (level 1)
  - GLE₂ OB GLE₁: sorry (need framework 2→1 bridge using CompoundLinearizationOrder)
- **Main theorem**: DONE (`cmcm_acyclic`) — complete modulo PPOi sorry lemmas
- **Irrefl/trans/canonicalization**: DONE

### Strategy: PPOi hierarchical linearization points + linking def/lemma to Com edges

**KEY INSIGHT (from Anqi):** PPOi events have **hierarchical linearization points**. For example, a coherent SC write linearizes at cache if it has coherent write permissions. The communication edges (rfe/fr/co) then pick up from those linearization points. The RF theorem covers the bridge: an SC write with/that got coherent perms gets a downgrade when a read from another cluster occurs after it in GLE (or CLE after from same cluster, different cache).

**Approach:**
1. Use **CompoundMCM** PPOi definition and **RF/FR/CO linearization orderings** as building blocks
2. Define a **linking/bridging definition** that connects WHERE a PPOi event linearizes (its hierarchical linearization point) to WHERE the next com edge (rfe/fr/co) communicates
3. Prove the linking def is satisfiable (the def "makes sense")
4. The acyclicity proof composes: PPOi linearization → linking def → com edge ordering → contradiction

**The linking def bridges between:**
- PPOi's `CompoundLinearizationOrder` (compound linearization events — cache or directory level)
- Com's linearization orderings (rfe uses `gleOrdering.Cases`, co/fr carry `hierarchicallyOrdered`)

The key: communication is **implicit** beyond the linearization point. The RF theorem already handles this — if the SC write has or got permissions, a subsequent read from another cluster sends a downgrade to the write's cache, establishing GLE ordering.

**DEAD ENDS (don't repeat):**
1. Trying to prove each PPOi edge independently produces `hierarchicallyOrdered` is the WRONG APPROACH. PPOi doesn't need to produce GLE/CLE ordering — it produces linearization event ordering (PPOi_lin). GLE/CLE are only relevant for rfe/co/fr.
2. Temporal chaining of GLE/CLE for PPOi is a rabbit hole. The `previousGlobalCacheGotPerms` case decouples GLEs from CLE ordering for different addresses. Don't re-derive this.
3. The current per-edge `com_step_hierarchicallyOrdered` proof structure is wrong for PPOi. The proof needs a compositional argument that composes PPOi_lin + linking def + com ordering.
4. **`hierarchicallyOrdered` is PROVABLY FALSE for same-addr PPOi** in the CLE₂ OB CLE₁ case (2026-03-22 analysis): When e₂ has perms from predecessor E_pred BEFORE e₁, `orderBeforeDir` gives CLE₂ inside E_pred (before e₁), while `encapDir` gives CLE₁ inside e₁. So CLE₂ OB CLE₁. And via `encapGlobalCache` chain: GCR₂ OB GCR₁ → GLE₂ OB GLE₁. This makes `hierarchicallyOrdered(e₁_lin, e₂_lin)` false (would need GLE₁ OB GLE₂). Sorry #2 at line 212 is **unprovable** — the scenario it tries to rule out actually exists. The three sorry's are not missing sub-lemmas; they reflect a fundamentally wrong proof architecture.
5. **No single simple ranking function works for ALL four edge types:**
   - GLE.oEnd: works for rfe/co/fr, fails for PPOi (diff-addr GLE unconstrained, same-addr GLE can decrease)
   - compound_lin.oEnd: works for PPOi, uncertain for rfe/co/fr (compound_lin often CONTAINS GLE, so GLE ordering ≠ compound_lin ordering)
   - e.oEnd (cache event): works for PPOi (e₁ OB e₂), fails for rfe (cross-cluster events not temporally ordered)
   - The encapsulation goes the WRONG way: compound_lin ⊂ cache event, GLE ⊂ CLE ⊂ cache event. So bigger events (cache) have BIGGER oEnd, not smaller.

**KEY CONCEPTUAL CORRECTION (2026-03-22): PPOi does NOT need to produce `hierarchicallyOrdered`**

The current proof architecture (each edge → `hierarchicallyOrdered` independently) is WRONG for PPOi. The correct approach:

**PPOi_lin** (the PPOi linearization ordering) is about LOCAL ordering of linearization events, NOT about GLE/CLE ordering. GLE and CLE are structural artifacts of `globalLinearizationEventOfRequest` — they are relevant for rfe/co/fr, but NOT for PPOi.

**Three distinct concepts (don't conflate!):**
1. **GLE** — a PRIMITIVE protocol event (global directory event from `globalLinearizationEventOfRequest.hreq's_global_lin`). Just a building block.
2. **CLE** — a PRIMITIVE protocol event (cluster directory event from `globalLinearizationEventOfRequest.hreq's_dir_access`). Just a building block.
3. **system-lin** — a HIGHER-LEVEL DERIVED concept: the point at which a request's effect globally linearizes across the system. This is what `CompoundLinearizationOrder` establishes ordering on. It is NOT the same as GLE, though it's related. system-lin indicates when other requests WILL BE ABLE TO SEE this request's effect, via the protocol mechanisms (CLE, GLE, RF, CO).

**How system-lin works (PPOi_lin ordering):**
- CompoundLinearizationOrder gives `system_lin₁ OB system_lin₂` — the system linearization events are ordered
- WHERE a request's system-lin is depends on its type:
  - SC coherent writes with permissions → system-lin at cache. Multiple such writes sharing the same CLE are ordered by local OrderedBefore.
  - Weak nc writes (possibly with weak nc reads) → share a CLE, ordered locally. system-lin carries forward to when they write back (or coherent release gets perms for the line).
  - Requests without permissions → system-lin at directory or beyond.

**How other requests OBSERVE the system-lin ordering (linking def):**
- Other requests see system-lin ordering by using their own CLEs, GLEs, and the RF/CO protocol mechanisms
- **rfe example**: SC coherent write e₂ has system-lin at cache. An external read from another cluster triggers a **downgrade** to e₂'s cache → the downgrade mechanism (via GLE ordering from RF theorem) lets the reader observe e₂'s write
- **nc rel write example**: nc rel write e₂ has system-lin at directory. External read accesses e₂'s directory → directory access establishes ordering
- The protocol GUARANTEES: if system_lin_A is before system_lin_B, then any observer using RF/CO will see them in that order

**NO EXTRA LINKING DEFINITION NEEDED**: The existing PPOi and rfe/co/fr definitions ALREADY carry the relationships:
- PPOi: system_lin(e1) OB system_lin(e2) (from CompoundLinearizationOrder)
- rfe(e2, e3): the downgrade to e2's cache (triggered by e3's read) is AFTER e2's system-lin (because e2's write must be committed before data can be sent)
- co/fr: carry hierarchicallyOrdered by definition

**Acyclicity contradiction**: In a cycle, following from e3 back to e2 gives "e3's effects are before e2's system-lin." But rfe says the downgrade (e3's effect on e2) is AFTER e2's system-lin. Downgrade can't be both before and after e2's system-lin → contradiction.

**The proof should COMPOSE the existing edge definitions directly**, not convert each to `hierarchicallyOrdered`.

**Proof architecture needs to change:**
- Current: `com_step_hierarchicallyOrdered` (each edge → same ranking) → transitivity → irreflexivity
- Correct: compose PPOi_lin ordering + linking def + com ordering around the cycle → contradiction
- The sorry's at lines 207, 212, 265 are symptoms of the wrong architecture, NOT missing sub-lemmas

**Bigger picture (Herd equivalence):**
- Forward direction (protocol → Herd acyclicity): `cmcm_acyclic` — needs architectural rework
- Reverse direction (Herd acyclicity → protocol guarantees): separate later goal
- The linking def should be designed to potentially support both directions

**PROMISING DIRECTION: compound_lin.oEnd via rfe downgrade chain (2026-03-22)**

For rfe(e_w, e_r) with `cleEncap` case:
1. compound_lin(e_w).oEnd < e_w.oEnd (e_w encapsulates compound_lin)
2. e_w.oEnd < e_r_down.oStart (`existsRDownAtW`: write OB downgrade at its cache)
3. e_r_cdir_down is inside CLE(e_r) (`cleEncap`: CLE encapsulates dir downgrade)
4. IF e_r_cdir_down encapsulates e_r_down (dir triggers cache downgrade): e_r_down.oEnd < e_r_cdir_down.oEnd
5. Then: compound_lin(e_w).oEnd < e_w.oEnd < e_r_down.oStart < e_r_down.oEnd < e_r_cdir_down.oEnd < CLE(e_r).oEnd
6. For `clusterCacheLin`/`previousGotPerms` on reader: compound_lin(e_r).oEnd ≥ CLE(e_r).oEnd
7. Chain gives: compound_lin(e_w).oEnd < compound_lin(e_r).oEnd ✓

**KEY GAP**: Step 4 — need `e_r_cdir_down.Encapsulates n e_r_down` (dir downgrade encapsulates cache downgrade). NOT stated in `encapProxyAndDirAndCDown` — the two existentials are independent with no formal link. TODO comment at Rf.lean:730 acknowledges this is not yet formalized. `rccOStyleDowngrade.dirEncapDowngrade` has the relationship but in a different context.

**GOOD NEWS**: Step 3 works in BOTH encapDirRelation cases:
- `cleEncap`: CLE encapsulates e_r_cdir_down → e_r_cdir_down.oEnd < CLE.oEnd ✓
- `gcacheEncap`: explicit `cdownEndBeforeCle : e_r_cdir_down.oEnd < CLE.oEnd` ✓
So IF we can connect e_r_down to e_r_cdir_down, we get compound_lin(w).oEnd < CLE(r).oEnd.

**Also check**: `getGlobalCachePerms` case on reader — compound_lin is INSIDE CLE (compound_lin.oEnd < CLE.oEnd), but we only showed compound_lin(w).oEnd < CLE(r).oEnd, so compound_lin(w).oEnd < CLE(r).oEnd but compound_lin(r).oEnd < CLE(r).oEnd too — can't conclude compound_lin(w).oEnd < compound_lin(r).oEnd.

**Possible resolution**: The chain might NOT go through compound_lin at all. Instead, the ranking function might be something like `max(compound_lin.oEnd, CLE.oEnd)` or the cache event's oEnd. Or a completely different proof structure may be needed.

**TODO:**
- [x] Verify: rfe carries "downgrade after system-lin" — YES, via `encapProxyAndDirAndCDown.existsRDownAtW` (e_w OB e_r_down)
- [ ] **CRITICAL**: Find/verify that dir downgrade encapsulates cache downgrade in the rfe chain (or that e_r_down.oEnd < CLE(e_r).oEnd directly)
- [ ] Verify the chain works for `getGlobalCachePerms` case on the reader
- [ ] Handle co/fr: show hierarchy ordering implies compound_lin ordering for same-address events
- [ ] Formalize compound_lin.oEnd as ranking function if above checks pass
- [ ] Restructure Proof.lean accordingly

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
- **`/learn`** after discovering patterns, user corrections, dead ends
- **`/reflect`** every ~20-30 min: am I correct? efficient? going in circles?
- **`/philosophy`** before major proof decisions, when stuck, when something feels architecturally wrong
- **Always save key insights to CLAUDE.md** (not just memory files) — this file is loaded every session
- **Track all TODOs in CLAUDE.md** — sessions crash! Progress must survive.
- **Git commit after implementing** — after completing any code change, commit immediately to avoid losing progress on crash. Don't wait to batch commits.

## Common commands

- `lake clean` — remove all build artifacts (preferred over manually deleting `.olean`/`.ilean` files)
- `lake build` — build the entire project
- `lake build <module>` — build a specific module and its dependencies (e.g., `lake build CMCM.Herd.Proof`). Faster than full `lake build` for iterating on one file.
- `lake env lean <file.lean>` — compile a single file (doesn't rebuild dependencies — can use stale cache!)
- `lake env lean <file.lean> 2>&1 | tail -20` — compile and check for errors/warnings
