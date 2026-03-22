# Compositional Protocol Proof — Lean 4 Formal Verification

## Project

Formal verification of compositional cache coherence protocols in Lean 4. The codebase proves properties about compound memory consistency models (CMCM), including PPO enforcement (`CompoundLinearizationOrder`), the RF theorem (`readsFrom`), and the Herd CMCM (`acyclic(PPOi ∪ rfe ∪ fr ∪ co)`).

## Rules

### Before writing any proof code

1. **Understand first, prove second.** Lay out: (a) the precise statement, (b) the proof approach, (c) required definitions and sub-lemmas, (d) open questions. Do a "thought experiment" — walk through the proof in text before formalizing. This surfaces structural gaps cheaply.

2. **Analyze tradeoffs of lemma formulations.** When there are multiple ways to state a lemma, lay out 2–3 candidates with their hypotheses, conclusions, and how they compose with the rest of the proof. Choose the formulation that minimizes proof obligations.

### When reasoning about definitions and claims

3. **Read the actual definition.** Before claiming "X always does Y," grep for and read the source definition. Cross-reference with related definitions. The RF linearization definition (`globalLinearizationEventOfRequest`) is structurally different from the PPO compound linearization (`ClusterRequestLinearizationEvent`). Never assume they're the same — verify.

4. **Verify claims independently.** Do not ask the user to confirm something that can be checked by reading code. Navigate to the source, trace the data flow, and verify structurally. Flag specific uncertainties rather than asking for blanket confirmation.

5. **Consider all cases and the contrapositive.** Before confirming or denying a claim: try to construct a counterexample, consider the contrapositive, examine all cases (not just the obvious ones), and distinguish formal/structural claims from semantic/protocol-level claims.

### When investigating open questions

6. **Search the codebase first.** Before flagging something as an "open question," search existing proofs, axioms, and lemmas — especially the RF theorem proof, protocol axioms, and `CompoundPPOs.lean`. Patterns like `wEqRGle`/`wObRGle`, synchronization contradictions, and `dirAccessOfRequest` case splits often directly answer the question.

7. **Remember key definitions with multiple cases.** `dirAccessOfRequest` has three cases (`encapDir`, `orderBeforeDir`, `orderAfterDir`). `linearizationEventOfRequest` has two cases (`requestLin`, `dirLin`). `clusterDirectoryLinearizationEvent` has two cases (`previousGlobalCacheGotPerms`, `getGlobalCachePerms`). Always consider all cases.

### When writing proofs

8. **Never add new axioms.** The existing protocol "axioms" are definitions validated by Murphi model checking. The goal is a self-supporting proof framework. Always prove theorems from existing protocol definitions — case-split on existing inductive types (`dirAccessOfRequest`, `linearizationEventOfRequest`, `clusterDirectoryLinearizationEvent`) and use existing transitivity/encapsulation lemmas (`encap_by_order_trans`, `order_encap_trans`, etc.) rather than introducing new axioms or fields.

9. **Ensure definitions are not vacuous.** When writing a definition or lemma, verify it's meaningful — check that the hypotheses are satisfiable and the conclusion is nontrivial. A proof of `False → P` is vacuously true but useless.

10. **Read comments and docstrings.** The codebase has important annotations (e.g., Rf.lean:82-83 warns that GLE terms differ from PPO linearization events). Read them — they often flag exactly the subtlety you'd otherwise miss.

11. **Test carefully.** When a proof compiles, check that it actually proves what was intended. Verify the statement matches the goal, the hypotheses are what you expect, and the proof isn't going through a vacuous or unintended path.

## Key architecture

- **PPOi ordering**: `CompoundLinearizationOrder` in `CompoundPPOs.lean` — gives ordering on compound linearization events (CLE level)
- **RF theorem**: `readsFrom.cases` in `Rf.lean` / `RfTheorem.lean` — gives GLE ordering for cross-cluster reads-from
- **4-level hierarchical order**: The global order is a 4-level lexicographic hierarchy (from highest to lowest):
  1. **GLE** (global directory order): `hreq's_global_lin.choose`
  2. **Global cache order**: `cDir'sGReq.wrapper` — the global cache request corresponding to the CLE
  3. **CLE** (cluster directory order): `hreq's_dir_access.choose`
  4. **Cache event order**: the request event itself (`e₁.OrderedBefore e₂`)

  Two events are ordered by the highest level at which they differ. When GLE, global cache, and CLE are all equal (e.g., two events sharing the same predecessor in `orderBeforeDir`, or a nc.Weak write sharing its successor's CLE in `orderAfterDir`), the cache event ordering (e₁ OB e₂) breaks the tie. The RF definition demonstrates the GLE/CLE split with `wEqRGle` (same GLE → use CLE) vs `wObRGle` (different GLEs → use GLE).
- **Lazy case**: `lazyCompoundLinearizationOrder` arises only for (nc.weak → c.release) PPO pairs in the `orderAfterDir` subcase. Gives `finishesBefore` (weaker than `OrderedBefore`). No cumulativity across transitive PPOi chains.
