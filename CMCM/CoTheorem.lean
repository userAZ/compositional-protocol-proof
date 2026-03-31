import CMCM.Rf
import CMCM.RfProofDefs
import CMCM.RfProofHelpers
import CMCM.Herd.Defs

variable {n : ℕ}

/-! # CO Theorem: Coherence Order from Protocol Axioms

Prove that `co.ordering` holds for any two writes to the same address,
given SWMR protocol axioms + directory serialization.

Unlike the RF theorem (which proves `readsFrom.cases` for a write+read pair),
this proves `co.ordering` (sameCache / sameClusDiffCache / diffClus) for a
write+write pair.

**Status**: TODO. The `co.ordering` is currently assumed in the `co` structure's
`comm` field. This theorem should derive it from protocol axioms, similar to how
`RfTheorem` derives `readsFrom.cases`.

**Key difference from RF**: Both events are writes, so `NoInterveningWrites`
and `readsFrom.cases` (which require isRead for the second event) cannot be
reused directly. The directory serialization of writes at the same address
provides the ordering evidence.
-/

-- TODO: Implement co_holds theorem
-- The theorem should take:
--   - Two writes e_w1, e_w2 with same address
--   - Their linearization events
--   - GLE/CLE ordering constraints (from gleOrdering.Cases)
--   - Directory serialization evidence
-- And produce: co.ordering w₁_lin w₂_lin
