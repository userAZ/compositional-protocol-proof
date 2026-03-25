# Copilot Instructions

## Project Overview

This is a **Lean 4** formalization proving that hierarchical cache coherence protocols (MSI/RCC-family) compose correctly. The proof shows that cluster-level protocols connected by a global protocol via translation shims maintain memory consistency guarantees.

## Build

Uses [Lake](https://github.com/leanprover/lean4/tree/master/src/lake), the Lean 4 build system. Lean toolchain version is pinned in `lean-toolchain`.

```bash
# Build the full project (two default targets: CompositionalProtocolProof, CMCM)
lake build

# Build a single library
lake build CompositionalProtocolProof
lake build CMCM
lake build Herd

# Build/check a single file
lake env lean CompositionalProtocolProof/States.lean

# Blueprint documentation (requires nix shell: nix develop)
leanblueprint web
```

There is no test suite—correctness is verified by the Lean type checker.

## Architecture

The project has three Lean libraries (`lakefile.toml`):

### `CompositionalProtocolProof/` — Core formalization

Defines the compositional protocol model and proves compound consistency. Files should be read in dependency order (documented in `CompositionalProtocolProof/README.md`):

1. **Foundation**: `States.lean` (permission model: WR/R, cache states Vc/Vd/I) → `Requests.lean` → `ProtocolInterface.lean` → `Structures.lean` → `Events.lean` (cache/directory events with timing via `Occurrence`) → `EventRelations.lean`
2. **Behavior layer**: `Behaviours.lean` (`Behaviour` structure: finite event sets + ordering axioms) → `BehaviourRelationDefs.lean` / `BehaviourRelationProofs.lean` → `BehaviourHelpers.lean`
3. **Protocol axioms**: `RequestAxioms.lean` (14 coherence axioms) → `Protocol.lean` (`Protocol` structure bundling instance + interface + axioms + linearization) → `SWMR.lean`
4. **Composition**: `CompoundProtocol.lean` (three-protocol composition: `global` + `cluster1` + `cluster2` + `shimAxioms`) → `CompoundPPOs.lean` (main PPO enforcement theorem)
5. **Proof cases**: `CompositionalProof/` subfolder with `Lemma4.lean` through `Lemma8.lean` and `CompoundLinearization.lean`

### `CMCM/` — Coherent Memory Consistency Model

Proves the read-from (RF) theorem: reads return correct values respecting global/cluster linearization. Main result is in `RfTheorem.lean`. Proof status is tracked in `PROOF_STATUS.md` and `PROOF_PROGRESS.md`.

### `Herd/` — Herd memory model definitions

Defines consistency models (sc, weak, rel, acq) and communication relations (com, PPOi, rfe, fr, co).

## Key Conventions

- **Mathlib dependency**: The project uses mathlib v4.29.0-rc3. Use mathlib idioms and tactics (e.g., `simp`, `omega`, `aesop`, `exact?`, `apply?`).
- **Helper lemmas**: `BehaviourHelpers.lean` and `BehaviourRelationProofs.lean` contain reusable proof helpers. Check `CMCM/PROOF_HELPER_LEMMAS.md` for a reference guide of common patterns (induction, eliminating directory state, cache event reasoning).
- **Blueprint**: LaTeX blueprint in `blueprint/src/` is kept in sync with the Lean formalization. `checkdecls` verifies that declared lemmas exist in the Lean code.
- **Model checking**: `model-check-axioms/` contains protocol-specific axiom encodings for CXL and RCCO protocols, separate from the main formalization.
