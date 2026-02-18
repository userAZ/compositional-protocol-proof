
namespace Herd

/- Let us define a Herd model for the MCMs that our
proof captures. Then we can prove equivalence between
Herd's axiomatic representation of a CMCM and
our proof's axiomatic representation. -/

/-- Consistency "label" for a Herd Op.
Model a subset for SC, and RC.
We'll use these for showing our axiomatic
representation is equivalent to CMCM's axiomatic representation.  -/
inductive Consistency
| sc : Consistency
| weak : Consistency
| rel : Consistency
| acq : Consistency

/-- A Read / Write Op. -/
inductive RW
| r : RW
| w : RW

/-- A Herd Op, for a cache coherence protocol -/
structure Op where
  op : RW
  consistency : Consistency

-- define props that disallow certain combinations of Herd Ops
def Op.NoReleaseRead (h : Op) : Prop := ¬ (h.op = .r ∧ h.consistency = .rel)
def Op.NoAcquireWrite (h : Op) : Prop := ¬ (h.op = .w ∧ h.consistency = .acq)

-- Also add thread id and address to Op

-- define a structure : Prop of a valid Herd Op
structure Op.Valid (h : Op) : Prop where
  no_release_read : Op.NoReleaseRead h
  no_acquire_write : Op.NoAcquireWrite h

/-- A valid Herd Op type. -/
def ValidOp := {h : Op // Op.Valid h}

/- A list of valid PPO Op Orderings -/
def ValidOp.isPPOPair (op₁ op₂ : ValidOp) : Prop :=
  match op₁.val, op₂.val with
  -- Rel, acq, weak op orderings
  | ⟨_, .weak⟩, ⟨.w, .rel⟩ => True
  | ⟨.r, .acq⟩, ⟨_, .weak⟩ => True
  | ⟨.r, .acq⟩, ⟨.w, .rel⟩ => True
  | ⟨.w, .rel⟩, ⟨.r, .acq⟩ => True
  -- SC op orderings
  | ⟨_, .sc⟩, ⟨_, .sc⟩ => True
  -- Other orderings are not required
  | _, _ => False

/- Now define other Relations between Ops in the CMCM def: acyclic(PPOi ∪ rfe ∪ fr ∪ co)
Relations between ValidOp `op₁` and `op₂`, and restrictions on `op₁` and `op₂`:
- PPOi:
  `op₁` and `op₂` satisfy ValidOp.isPPOPair.
  `op₁` and `op₂` are from the same thread
- rfe:
  `op₁` is a write, `op₂` is a read.
  `op₁` and `op₂`'s addresses are the same
  `op₁` and `op₂` are from different threads
- fr: from-read
  `op₁` is a read, `op₂` is a write.
  `op₁` and `op₂`'s addresses are the same
  `op₁` and `op₂` are from different threads
- co: coherence order
  `op₁` is a write, `op₂` is a write.
  `op₁` and `op₂`'s addresses are the same
-/

end Herd
