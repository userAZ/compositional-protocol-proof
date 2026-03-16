import Mathlib

open scoped Classical in
noncomputable def Set.toOption {α} (s : Set α) : Option α :=
  by classical exact
  if h : Nonempty s then some h.some
  else none

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

lemma Set.toOption_singleton {α} (s : Set α) (hsingleton : s.IsSingleton) : ∃ e, s = {e} → s.toOption = some e := by
  use hsingleton.choose
  intro hs_singleton
  simp only [toOption, Option.dite_none_right_eq_some,]
  have hs_nonempty' : Nonempty s := by
    simp []
    use hsingleton.choose
    simp[Set.eq_singleton_iff_unique_mem] at hs_singleton
    obtain ⟨hsingle_in_s, helem_of_s⟩ := hs_singleton
    simp[hsingle_in_s]
  use hs_nonempty'
  obtain ⟨_,hxs_eq_singleton⟩ := Set.eq_singleton_iff_unique_mem.mp hs_singleton
  simp
  apply hxs_eq_singleton
  . case h.intro.a =>
    apply Nonempty.some_mem
    . case h =>
      use hsingleton.choose

open scoped Classical in
noncomputable def Set.toOption' {α} (s : Set α) : Option α :=
  by classical exact
  if h : Singleton s then some h.some
  else none

def Set.countProp {α : Type} (s : Set α) (p : α → Prop) : Nat := sorry

def Set.countProp {α : Type} (s : Set α) (p : α → Prop) : Nat := sorry
