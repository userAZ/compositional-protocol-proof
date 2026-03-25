---
name: simplify-proof
description: Review Lean 4 proof code for elegance, readability, and simplification opportunities. Use after writing or modifying proofs.
user-invocable: true
allowed-tools: Read, Grep, Glob, Edit, Bash
effort: high
argument-hint: [file-path or lean-module]
---

## Lean 4 Proof Simplification

Review the proof code in $ARGUMENTS (file path or module name) for elegance, clarity, and simplicity.

### Philosophy

The goal is **elegant, simple, and very clear** proofs — like any good document. This is NOT tactic golf. A proof that reads clearly to a human mathematician is better than a proof that is shorter but opaque. When in doubt, prefer clarity over brevity.

**Be careful not to over-simplify.** Removing intermediate `have` steps can obscure the logical flow. A named intermediate result like `have hgle_eq := cle_eq_implies_gle_eq hcle` is clearer than inlining it, even if the inlined version saves a line. Preserve the proof's narrative structure.

### What to look for

1. **Dead code**: `have` bindings that are never used, redundant hypotheses
2. **Redundant tactics**: `simp` followed by `exact` where `simp` alone suffices, unnecessary `unfold` when `simp [defn]` works
3. **Structural clarity**: Use `show` to make goals explicit, `suffices` to state the key step up front, `calc` for chains of equalities/inequalities
4. **Naming**: Variables and hypotheses should have meaningful names that reflect what they represent (e.g., `hgle_ob` not `h7`)
5. **Section organization**: Long proofs benefit from `/-! ## Section -/` comments marking logical phases
6. **Case split readability**: Pattern matching with named constructors is often clearer than deeply nested `rcases`
7. **Repeated patterns**: If the same tactic sequence appears multiple times, consider whether a helper lemma would make the structure clearer (but only if the lemma has a natural mathematical meaning — don't abstract just to DRY)

### What NOT to do

- Do NOT compress proofs at the cost of readability
- Do NOT remove `have` steps that serve as logical signposts
- Do NOT replace clear tactic sequences with opaque `decide` or `omega` unless the statement is genuinely trivial
- Do NOT refactor proof structure without asking — a 3-case split may reflect the mathematical structure even if 2 cases could be merged

### Process

1. Read the target file(s)
2. Identify simplification opportunities — list them with line numbers
3. For each opportunity, explain the tradeoff (clarity vs brevity)
4. Apply changes only after confirming the tradeoff is worthwhile (ask before large refactors)
5. Run `lake build <module>` to verify the simplified proof still compiles

### Constraints

- NEVER change the theorem statement (only the proof body)
- NEVER add new axioms or `sorry`
- Preserve all existing comments that explain non-obvious reasoning
- If a tactic sequence is deliberately verbose for clarity, note it but don't change it without asking
