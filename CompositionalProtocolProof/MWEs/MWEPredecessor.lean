import Mathlib

namespace MWE

inductive Nats
| order : Nat → Nat → Nats
| map : Nat → Nat → Nats

abbrev SetNats := Set Nats

def Nats.before : Nats → Nat → Prop
| ns, n =>
  match ns with
  | order _ n₂ => n = n₂
  | map _ _ => false

def SetNats.before (x : SetNats) (n : Nat) : SetNats := {nats ∈ x | nats.before n}

lemma SetNats.mem_before (x : SetNats) (n : Nat) : ∀ m ∈ x.before n, m ∈ x ∧ m.before n := by
  simp [SetNats.before]

def Nats.natIsPred : Nats → Nat → Nat → Prop
| nats, n_pred, n_succ => match nats with
  | .order n₁ n₂ => n₁ = n_pred ∧ n₂ = n_succ
  | .map _ _ => false

def Nats.pred : Nats → Nat → Nat
| nats, n => match nats with
  | .order n₁ n₂ =>
    if n₂ = n then n₁
    /- Is using `panic!` the best approach here? Or is there a better approach to getting predecessors? -/
    else panic! "Expected n to be the successor of n₁."
  | .map _ _ => panic! "Expected nats to be an order."

def SetNats.predecessor (x : SetNats) (n : Nat) : Set Nat :=
  let ordered := x.before n
  ordered.image (·.pred n)

def SetNats.natIsPred (x : SetNats) (n_pred n_succ : Nat) : Prop :=
  ∃ nats ∈ x, nats.natIsPred n_pred n_succ

lemma SetNats.mem_predecessor (x : SetNats) (n : Nat) : ∀ m ∈ x.predecessor n, x.natIsPred m n := by
  simp [SetNats.predecessor]
  simp [SetNats.before]
  simp [Nats.before]

  simp [SetNats.natIsPred]
  simp [Nats.natIsPred]
  simp [Nats.pred]
  intro m hm_in_x hm_has_succ_n

  -- after some guidance from aesop...
  /- Can this be simpler? -/
  apply Exists.intro
  apply And.intro
  . exact hm_in_x
  . split
    next nats m n₂ =>
      subst hm_has_succ_n -- What does subst do in general?
      simp
    next nats n₁ n₂ =>
      simp [hm_in_x, hm_has_succ_n]

-- def SetNats.predecessor' (x : SetNats) (n : Nat) : Set Nat := {y ∈ Set Nat | ∃ nats, nats ∈ x ∧ nats.natIsPred y n}

-- Cover defining a predecessor by Transitivity and Encapsulation later.
