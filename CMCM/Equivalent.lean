import Herd.Defs
import Herd.Relations
import Mathlib

import CompositionalProtocolProof.CompoundProtocol

import CompositionalProtocolProof.CompoundPPOs

open Herd

/- Define a mapping between:
  this compound protocol abstraction's linearization event abstraction and
  herd's ops.
  Specifically, herd's ops map to this abstraction's linearization event of a request event.
  This abstraction's request event's linearization events map to a herd op.
-/
-- Define mapping using "compoundLinearizationEvent" from CompoundProtocol

def CompoundProtocol.OpToLinearizationEvent (cmp : CompoundProtocol n)  {b init}
  (op : Op) (e : Event n) :=
  cmp.compoundLinearizationEvent cmp.shimAxioms b init e (cmp.linearizationOfEvent b init e) |>.linearizationEvent
  -- cmp.linearizationOfEvent

  -- sorry
-- def CompoundProtocol.linearizationEventToOp


/- Define a mapping between:
  Herd's com relation and
  what it means for this compound protocol abstraction's events to be ordered before.
  1. For PPOi relations, let's restrict PPOi to only different addresses.
    For different addresses, Herd com of (op1, op2) match the
    CompoundProtocol.CompoundLinearizationOrder definition.
    For most cases, op1 maps to e_lin1, and op2 maps to e_lin2.
    e_lin1 linearizes before e_lin2.
    For the ordering between a weak write and coherent release write (RCC-O),
    we use the CompoundProtocol.lazyCompoundLinearizationOrder.
  2. For same addresses (rfe, fr, co), and different threads (caches),
    we check if the clusters between op1 and op2 are the same,
    and if their equivalent e_lin1 and e_lin2 linearize at the same level.
    If both requests are from the same cluster:
      If they linearize at the cluster directory or beyond (global cache or dir):
        then their equivalent e_lin1 is ordered before e_lin2
      If they linearize at the cluster cache:
        This is ok, but there must exist another request that obtains
        permissions for the second request.
        -- Proof for later: both e1 and e2 must have a past request event that
        -- obtained permissions for them. These are ordered. e2's past request event
        -- must have sent an invalidation to e1.
      If they linearize at different levels:
        Their linearization events may overlap (no strict ordered before relation).
        e1 may be at the directory, and e2 at the cache:
          Then similar to the above case, e2 has a previous request event
          that requested permissions for e2.
        e1 may be at the cache, and e2 at the directory:

-/
-- Just define a mapping for item 1. for now:



/-
Prove the theorem, that if we have 2 ops in PPOi, and equivalent mapped
events (and linearization events as per CompoundProtocol), then

acyclic(ValidOp.com) ↔ CompoundProtocol.CompoundLinearizationOrder e₁ e₂
-/

theorem CMCM.herd_cmcm_equivalent_to_event_based_cmcm {cmp b init}
(op₁ op₂ : ValidOp) (e₁ e₂ : Event n)
(hop_ppo : op₁.PPOiPair op₂) (he_ppo : e₁.isPPOPair n e₂)
: (∀ x, ¬(Relation.TransGen ValidOp.com x op₁ ∧
        Relation.TransGen ValidOp.com op₂ x))
  -- acyclic ValidOp.com
  ↔ CompoundProtocol.CompoundLinearizationOrder n cmp b init e₁ e₂ :=  by
  apply Iff.intro
  . case mp =>
    intro hacyclic
    sorry
  . case mpr =>
    intro he₁_e₂_lin_order
    by_contra hcyclic
    simp[acyclic] at hcyclic
    have hop₁_cycle := hcyclic.choose
    sorry
