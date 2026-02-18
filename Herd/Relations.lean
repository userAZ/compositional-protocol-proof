import Herd.Defs
import Mathlib

open Herd

-- Define com = PPOi ∪ rfe ∪ fr ∪ co

inductive ValidOp.com (op₁ op₂ : ValidOp) : Prop where
| ppoi : (hppoi : op₁.PPOiPair op₂) → ValidOp.com op₁ op₂
| rfe : (hrfe : op₁.rfe op₂) → ValidOp.com op₁ op₂
| fr : (hfr : op₁.fr op₂) → ValidOp.com op₁ op₂
| co : (hco : op₁.co op₂) → ValidOp.com op₁ op₂

-- Build up to defining acyclic( `rel` )

-- Define a set of ops

-- Define a transitive chain of relations from `rel` (`rel`+)

instance : IsTrans ValidOp (Relation.TransGen ValidOp.com) where
  trans := fun _ _ _ hab hbc => Relation.TransGen.trans hab hbc

-- Define cyclic(`rel`) : taking the transitive
def cyclic (rel : α → α → Prop) : Prop :=
  ∃ x, Relation.TransGen rel x x

def acyclic (rel : α → α → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen rel x x

theorem cyclic_eq_neg_acyclic {α : Type} {rel : α → α → Prop}
  : cyclic rel = ¬ acyclic rel := by simp[cyclic, acyclic]
