import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Subsingleton

abbrev SetNat := Set Nat

def SetNat.intermediatePredecessor : SetNat → Nat → Nat → SetNat
| sn, n, n_pred => {n_intermediate ∈ sn | n_pred < n_intermediate ∧ n_intermediate < n}

def SetNat.noIntermediatePredecessor : SetNat → Nat → Nat → Prop
| sn, n, n_pred => sn.intermediatePredecessor n n_pred = ∅

def Nat.predecessor (n_pred n : Nat) : Prop := n_pred < n

def SetNat.predecessors : SetNat → Nat → SetNat
| sn, n => {n_pred ∈ sn | n_pred.predecessor n}

def SetNat.immediatePredecessors : SetNat → Nat → SetNat
| sn, n => let predecessors := sn.predecessors n
  {n_pred ∈ predecessors | predecessors.noIntermediatePredecessor n n_pred}

def SetNat.predecessorsSubSingleton (sn : SetNat) (n : Nat) : Prop := (sn.immediatePredecessors n).Subsingleton

structure SetNat.predSubSingleton where
  subs : ∀ sn : SetNat, ∀ n : Nat, SetNat.predecessorsSubSingleton sn n

noncomputable def SetNat.pred (sn : SetNat) (n : Nat) (hsn_sub : SetNat.predSubSingleton) : Option Nat :=
  let preds := sn.immediatePredecessors n
  open scoped Classical in
  if h : preds = ∅ then
    none
  else
    have hsubsingle := hsn_sub.subs sn n
    have hempty_or_single := hsubsingle.eq_empty_or_singleton
    some (hempty_or_single.resolve_left h).choose

def Nat.irrelevantRelation (n₁ n₂ : Nat) : Nat := n₁/n₂ + n₂/n₁

/- How do I show lean this terminates? -/
noncomputable def SetNat.predPred (sn : SetNat) (n : Nat) (hsn_sub : SetNat.predSubSingleton) : Option Nat :=
  let pred? := sn.pred n hsn_sub
  match h : pred? with
  | .none => none
  | .some n_pred =>
    have n_pred_of_n : n_pred < n := by
      simp_all [SetNat.pred] -- can't unfold `pred?`, that specifies `n_pred < n` in it's `predecessor` def.
      sorry
    let pred_pred? := sn.predPred n_pred hsn_sub
    match pred_pred? with
    | .none => n_pred
    | .some n_pred_pred => n_pred.irrelevantRelation n_pred_pred
-- termination_by sizeOf (sn.predecessors n)

/- Is it easier to convert SetNat to a list where each element is ordered by SetNat.pred?
Is there a way to convert a Set to a List given an ordering `Prop` such as Nat.predecessor or something like SetNat.immediatePredecessors? -/
def SetNat.toList (sn : SetNat) : List Nat :=
  sorry
