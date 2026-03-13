import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol

import CompositionalProtocolProof.CompositionalProof.Lemma6GlobalWriteDowngrade
import CompositionalProtocolProof.CompositionalProof.Lemma7GlobalReadDowngrade

variable (n : Nat)

/- Global Coherent Request Event in Compound SWMR Initial/Current state enforces Compound SWMR.
For any SC Write/Read Global Cache Request Event `e_gcache`, show the compound protocol is left in Compound SWMR.
-/

/-- Lemma 5 (core): any global downgrade event enforces Compound SWMR.
    This is the top-level consequence proved from Lemmas 6 and 7. -/
lemma CompoundProtocol.global_request_enforces_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown : Event n) (he_gdown_in_b : e_gdown ∈ b)
  (he_gdown : e_gdown.isGlobalDowngrade)
  : CompoundSWMR n b init e_gdown := by
  exact CompoundProtocol.globalDowngrade.satisfies_compound_swmr n cmp b init e_gdown he_gdown_in_b he_gdown

/-- SC-write specialization of Lemma 5. -/
lemma CompoundProtocol.global_sc_write_request_enforces_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown : Event n) (he_gdown_in_b : e_gdown ∈ b)
  (he_sc_write : Event.isSCWriteGlobalDowngrade n e_gdown)
  (he_down : e_gdown.down)
  : CompoundSWMR n b init e_gdown := by
  have he_global_down : e_gdown.isGlobalDowngrade := ⟨he_sc_write.isGlobalDown, he_down⟩
  exact CompoundProtocol.global_request_enforces_compound_swmr n cmp b init e_gdown he_gdown_in_b he_global_down

/-- SC-read specialization of Lemma 5. -/
lemma CompoundProtocol.global_sc_read_request_enforces_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown : Event n) (he_gdown_in_b : e_gdown ∈ b)
  (he_sc_read : Event.isSCReadGlobalDowngrade n e_gdown)
  (he_down : e_gdown.down)
  : CompoundSWMR n b init e_gdown := by
  have he_global_down : e_gdown.isGlobalDowngrade := ⟨he_sc_read.isGlobalDown, he_down⟩
  exact CompoundProtocol.global_request_enforces_compound_swmr n cmp b init e_gdown he_gdown_in_b he_global_down
