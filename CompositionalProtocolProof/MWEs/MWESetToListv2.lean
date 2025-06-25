import Mathlib.Data.Set.Defs
import Mathlib.Data.Finset.Defs
import Mathlib

structure NatBool where
  n : Nat
  b : Bool

def NatBool.lt (nb₁ nb₂ : NatBool) : Prop := nb₁.n < nb₂.n

instance NatBool.instLT : LT NatBool := {lt := NatBool.lt}

instance NatBool.instLT.instanceDeciableRel : DecidableRel NatBool.lt := by
  unfold NatBool.lt
  infer_instance

abbrev SetNatBool := Set NatBool

/- Get NatBools with field `b` = true -/
def SetNatBool.projectTrue (snb : SetNatBool) : SetNatBool := {ns ∈ snb | ns.b}

def NatBool.bothTrue (nb₁ nb₂ : NatBool) : Prop := nb₁.b ∧ nb₂.b
def NatBool.Ordered (nb₁ nb₂ : NatBool) : Prop := nb₁ < nb₂ ∨ nb₂ < nb₁
structure NatBool.trueOrder : Prop where
  bothT : ∀ nb₁ nb₂ : NatBool, nb₁.bothTrue nb₂
  ordered : ∀ nb₁ nb₂ : NatBool, nb₁.Ordered nb₂

/- Assume all NatBools are totally ordered -/
structure NatBool.truesTotalOrdered : Prop where
  trueOrdered : NatBool.trueOrder

/- NatBools with field `b` = true are totally ordered -/
lemma SetNatBool.trues_total_order (snb : SetNatBool) (htotal_order : NatBool.truesTotalOrdered) :
  let trueSnb := snb.projectTrue
  ∀ nb₁ ∈ trueSnb, ∀ nb₂ ∈ trueSnb, nb₁.Ordered nb₂ := by
  intro trueSnb nb₁ hnb₁ nb₂ hnb₂
  exact htotal_order.trueOrdered.ordered nb₁ nb₂

def SetNatBool.finite (snb : SetNatBool) : Prop := Set.Finite snb
structure SetNatBool.fin : Prop where
  snbFinite : ∀ snb : SetNatBool, snb.finite

/- Assume SetNatBool is a Finset -/
noncomputable def SetNatBool.toFinset (snb : SetNatBool) (hsnb_fin : SetNatBool.fin) : Finset NatBool :=
  Set.Finite.toFinset <| hsnb_fin.snbFinite snb

/- List is sorted, and totally ordered. -/
def List.isOrdered {α} (l : List α) (r : α → α → Prop) : Prop :=
  ∀ i : Fin (l.length), ∀ j : Fin (l.length), i < j ↔ r l[i] l[j]

/- show that the list is totally ordered -/
lemma SetNatBool.toFinset_trues_total_ordered (snb : SetNatBool) (hsnb_fin : SetNatBool.fin) (htotal_order : NatBool.truesTotalOrdered) :
  let set_true_snbs  := snb.projectTrue
  let list_true_snbs := set_true_snbs.toFinset hsnb_fin |>.toList
  let sorted_list := list_true_snbs.insertionSort NatBool.lt
  sorted_list.isOrdered NatBool.lt := by
  intro set_true_snbs list_true_snbs sorted_list
  unfold List.isOrdered
  intro i j
  apply Iff.intro
  . case mp =>
    intro hi_lt_j
    unfold NatBool.lt
    /- What is the best way to handle `sorted_list` here? -/
    simp[sorted_list]
    simp[list_true_snbs]
    simp[SetNatBool.toFinset]
    simp[Set.Finite.toFinset]
    simp[Finset.toList]
    simp[Set.toFinset]
    simp[Multiset.map]
    simp[Quot.liftOn]
    sorry
  . case mpr =>
    sorry
