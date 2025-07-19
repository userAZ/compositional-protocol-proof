import Mathlib

variable (n : Nat)

inductive Example
| fin : Fin n → Example
| finTwo : Fin 2 → Example
deriving DecidableEq

instance Example.isFinite' : Fintype (Example n) where
  elems := by
    constructor
    case val => exact (List.finRange n).map (Example.fin ·) ++ (List.finRange 2).map (Example.finTwo ·) |>.toFinset.val
    case nodup =>
    simp[List.nodup_dedup]
  complete := by
    intro e
    induction e with
    | fin f => simp
    | finTwo f2 => simp

def Example.mkFin (fin : Fin n) : Example n := Example.fin fin

instance Example.mkFin_inj : Function.Injective (Example.mkFin n) := by
  simp[Function.Injective]
  simp[Example.mkFin]

def Example.mkFinTwo (fin : Fin 2) : Example n := Example.finTwo fin

instance Example.mkFinTwo_inj : Function.Injective (Example.mkFinTwo n) := by
  simp[Function.Injective]
  simp[Example.mkFinTwo]

instance Example.isFinite'' : Fintype (Example n) where
  elems := by
    constructor
    case val => exact (List.finRange n).map (Example.mkFin n ·) ++ (List.finRange 2).map (Example.mkFinTwo n ·)
    case nodup =>
      simp[List.nodup_append]
      apply And.rotate
      apply And.intro
      . case a.left =>
        intro fin fin_two
        simp[mkFin,mkFinTwo]
      . case a.right =>
        apply And.intro
        all_goals rw[List.nodup_map_iff]
        all_goals try simp[List.nodup_finRange]
        all_goals try simp[Example.mkFin_inj, Example.mkFinTwo_inj]
  complete := by
    intro e
    induction e with
    | fin f =>
      simp
      cases f
      . case fin.mk m hm_lt_n  =>
        apply Or.intro_left
        apply Exists.intro
        · rfl
    | finTwo f2 =>
      simp
      cases f2
      . case finTwo.mk m hm_lt_2 =>
        apply Or.intro_right
        apply Exists.intro
        . case h.h =>
          rfl

example : {e : Example n | True}.Finite := by
  simp[Set.Finite]
  simp[Set.Elem]
  simp[Subtype.finite]

def Example.isFinCase : Example n → Prop
| .fin _ => True
| .finTwo _ => False

example : {e : Example n | e.isFinCase}.Finite := by
  simp[Set.Finite]
  simp[Example.isFinCase]
  simp[Subtype.finite]
