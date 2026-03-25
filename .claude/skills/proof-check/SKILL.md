---
name: proof-check
description: Build and check a Lean 4 module for errors, warnings, and remaining sorry's. Use to verify proof progress.
user-invocable: true
allowed-tools: Bash, Read, Grep
effort: medium
argument-hint: [module-name, e.g., CMCM.Herd.Proof]
---

## Lean 4 Proof Check

Build and analyze the proof state for module $ARGUMENTS.

### Steps

1. Run `lake build $ARGUMENTS 2>&1` and capture output
2. Parse for:
   - **Errors**: Type mismatches, unknown identifiers, tactic failures
   - **Warnings**: Unused variables, sorry's
   - **Sorry count**: How many sorry's remain
3. If errors exist, read the relevant file lines and diagnose the issue
4. Report a concise summary:
   - Build status (success/failure)
   - Number and location of sorry's
   - Any warnings worth addressing
   - Suggested next steps

### Output format

```
## Build: ✓/✗ [module]
- Errors: N
- Warnings: N
- Sorry's: N (list locations)
- Next: [suggested action]
```
