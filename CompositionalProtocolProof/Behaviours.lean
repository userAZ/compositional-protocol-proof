import CompositionalProtocolProof.EventRelations
import Canonical

structure EventState where
  e : Event
  s : State ⊕ DirectoryState
  sWellFormed : match e with
    | .cacheEvent _ => match s with | .inl _ => true | .inr _ => false
    | .directoryEvent _ => match s with | .inl _ => false | .inr _ => true

structure Behaviour where
  es : Set EventState

def EventState.OrderedBefore : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.OrderedBefore e₂

structure EventState.OrderedBetween (e e_pred e_succ : EventState) where
  pred : e_pred.OrderedBefore e := by simp
  succ : e.OrderedBefore e_succ := by simp

def Behaviour.OrderedBetween : Behaviour → EventState → EventState → Set EventState
| b, e_pred, e_succ => {e ∈ b.es | e.OrderedBetween e_pred e_succ}

def Behaviour.NoIntermediateEvent (b : Behaviour) (e_pred e_succ : EventState) : Prop :=
  b.OrderedBetween e_pred e_succ = ∅

def EventState.Predecessor : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.Predecessor e₂
def EventState.SameAddress : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.SameAddress e₂
def EventState.SameStructure : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.SameStructure e₂

structure Behaviour.ImmediatePredecessorConstraint (b : Behaviour) (e_pred e_succ : EventState) where
  isPred : e_pred.Predecessor e_succ
  noIntermediate : b.NoIntermediateEvent e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

def EventState.Encapsulates : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.Encapsulates e₂

abbrev Behaviour.IsNotEncapByEvent (b : Behaviour) (e : EventState) : Prop := {e' ∈ b.es | e'.Encapsulates e} = ∅

def Behaviour.IsBottomEvent (b : Behaviour) (e : EventState) : Prop := b.IsNotEncapByEvent e

structure Behaviour.IsImmediateBottomPred (b : Behaviour) (e_pred e_succ : EventState) where
  isImmPred : b.ImmediatePredecessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_pred

-- TODO: also write a version with a constraint φ on e_pred.
/-- Define what is an event that's the immediate predecessor of another event. -/
def Behaviour.ImmediateBottomPredecessor : Behaviour → EventState → EventState → Prop
| b, e_pred, e_succ => b.IsImmediateBottomPred e_pred e_succ

def Behaviour.ImmBottomPredecessors : Behaviour → EventState → Set EventState
| b, e_succ => {e_pred ∈ b.es | b.ImmediateBottomPredecessor e_pred e_succ}

def Set.IsSingleton {α : Type} (s : Set α) : Prop := ∃ e, {e} = s

structure OrderedAddressEvents where
  dir_ordered : ∀ (e₁ e₂ : DirectoryEvent), OrderedDirectoryEvents e₁ e₂
  cache_ordered : ∀ (e₁ e₂ : CacheEvent), ∀ (s₁ s₂ : State), OrderedCacheEvents e₁ e₂ s₁ s₂

lemma Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction {es_pred₁ es_pred₂ es_succ : EventState} {b : Behaviour}
(he₁_b : b.IsImmediateBottomPred es_pred₁ es_succ) (he₂_b : b.IsImmediateBottomPred es_pred₂ es_succ)
(hes₁_ordered_es₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmPred.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₁_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₁_no_intermediate_to_e_suc
    simp at he₁_no_intermediate_to_e_suc
    have e₁_o_e_succ := he₁_b.isImmPred.isPred
    unfold Event.Predecessor at e₁_o_e_succ
    unfold EventState.Predecessor at e₁_o_e_succ
    simp at e₁_o_e_succ

    apply he₁_no_intermediate_to_e_suc
    apply he₂_b.isImmPred.predInB
    constructor
    unfold autoParam
    . case a.pred =>
      exact es₁_ordered_es₂
    . case a.succ =>
      unfold autoParam

      have e₂_o_e_succ := he₂_b.isImmPred.isPred
      unfold Event.Predecessor at e₂_o_e_succ
      exact e₂_o_e_succ
  . case inr es₂_ordered_es₁ =>
    have he₂_no_intermediate_to_e_suc := he₂_b.isImmPred.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he₂_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₂_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₂_no_intermediate_to_e_suc
    simp at he₂_no_intermediate_to_e_suc
    have e₂_o_e_succ := he₂_b.isImmPred.isPred
    unfold Event.Predecessor at e₂_o_e_succ
    unfold EventState.Predecessor at e₂_o_e_succ
    simp at e₂_o_e_succ

    apply he₂_no_intermediate_to_e_suc
    apply he₁_b.isImmPred.predInB
    constructor
    unfold autoParam
    . case a.pred =>
      exact es₂_ordered_es₁
    . case a.succ =>
      unfold autoParam

      have e₁_o_e_succ := he₁_b.isImmPred.isPred
      unfold Event.Predecessor at e₁_o_e_succ
      exact e₁_o_e_succ

-- NOTE: Remember to use OrderedCacheEvents and OrderedDirectoryEvents at some point.
lemma Behaviour.immediate_bottom_predecessor_unique (b : Behaviour) (es_succ : EventState)
  (es_pred₁ es_pred₂ : EventState) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomPred es_pred₁ es_succ) (he₂_b : b.IsImmediateBottomPred es_pred₂ es_succ) :
  es_pred₁ = es_pred₂ := by
    -- this is the "multiple" case in Lemma 1.
    /- By Ordered Cache Events and Ordered Directory Events,
    if e_pred₁ and e_pred₂ are different events, then they are ordered, and contradict he₁_b or he₂_b.
    By contradiction, e_pred₁ and e_pred₂ are the same event. -/
    by_contra h_e_pred_diff
    match h_pred₁ : es_pred₁.e, h_pred₂ : es_pred₂.e with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      -- Use OrderedDirectoryEvents to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      have e₁_same_addr_e_succ := he₁_b.isImmPred.sameAddress
      have e₂_same_addr_e_succ := he₂_b.isImmPred.sameAddress
      have es₁_same_addr_es₂ := Event.same_address_reflexive e₁_same_addr_e_succ e₂_same_addr_e_succ
      rw [h_pred₁, h_pred₂] at es₁_same_addr_es₂
      have de₁_de₂_ordered := de₁_de₂_ordered_prop es₁_same_addr_es₂

      have es_pred₁_ordered_es_pred₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁ := by
        unfold EventState.OrderedBefore; simp
        simp[h_pred₁, h_pred₂]
        simp[Event.OrderedBefore, Event.oEnd, Event.oStart]
        simp[DirectoryEvent.OrderedBefore] at de₁_de₂_ordered
        exact de₁_de₂_ordered

      apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b es_pred₁_ordered_es_pred₂
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      /- Part 1. Use OrderedCacheEvents to show that ce₁ and ce₂ (which are bottom predecessors to e_succ)
      are always ordered. Part 2. This is a contradiction with ImmediateBottomPred's NoIntermediatePred. -/
      -- Part 1. ce₁ and ce₂ are OrderedCacheEvents
      match he₁_s : es_pred₁.s with
      | .inl s₁ =>
        match he₂_s : es_pred₂.s with
        | .inl s₂ =>
          have hce₁_o_ce₂ := haddress_ordered.cache_ordered ce₁ ce₂ s₁ s₂  -- need state s₁ s₂ that ce₁ and ce₂ are made on.
          -- Same cid, e_pred₁ e_pred₂
          have hce₁_cid_csucc := he₁_b.isImmPred.sameStructure
          have hce₂_cid_csucc := he₂_b.isImmPred.sameStructure
          have es₁_same_structure_es₂ := Event.same_structure_reflexive hce₁_cid_csucc hce₂_cid_csucc
          unfold EventState.SameStructure at es₁_same_structure_es₂
          unfold Event.SameStructure at es₁_same_structure_es₂
          rw [h_pred₁] at es₁_same_structure_es₂
          unfold CacheEvent.SameCache at es₁_same_structure_es₂
          unfold DirectoryEvent.SameStructure at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          unfold Event.SameStructureRelation at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          -- Same Address, e_pred₁ e_pred₂
          have hce₁_a_csucc := he₁_b.isImmPred.sameAddress
          have hce₂_a_csucc := he₂_b.isImmPred.sameAddress
          have es₁_same_addr_es₂ := Event.same_address_reflexive hce₁_a_csucc hce₂_a_csucc
          unfold EventState.SameAddress at es₁_same_addr_es₂
          unfold Event.SameAddress at es₁_same_addr_es₂
          rw [h_pred₁] at es₁_same_addr_es₂
          unfold CacheEvent.SameAddress at es₁_same_addr_es₂
          unfold DirectoryEvent.SameAddress at es₁_same_addr_es₂
          unfold Event.SameStructureRelation at es₁_same_addr_es₂
          simp at es₁_same_addr_es₂

          rw [h_pred₂] at es₁_same_structure_es₂ es₁_same_addr_es₂
          simp at es₁_same_structure_es₂ es₁_same_addr_es₂

          -- have the big if then else from OrderedCacheEvents:
          have ordered_ite := hce₁_o_ce₂ es₁_same_structure_es₂ es₁_same_addr_es₂

          /- Show for all cases of ce₁ ce₂ s₁ s₂, ce₁ and ce₂ are either:
            1. ordered (contradiction with NoIntermediatePred)
            2. one encapsulates another (contradiction with isBottom)
          -/
          by_cases (ce₁.NoEncapSameAddressDowngrade s₁ ∧ ce₂.NoEncapSameAddressDowngrade s₂) = true
          . case pos ce₁₂_no_encap =>
            simp [ce₁₂_no_encap] at ordered_ite

            have es_pred₁_ordered_es_pred₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁ := by
              unfold EventState.OrderedBefore
              simp
              simp [h_pred₁, h_pred₂]
              simp [Event.OrderedBefore, ordered_ite]
              simp [Event.oEnd, Event.oStart]
              simp [CacheEvent.OrderedBefore] at ordered_ite
              exact ordered_ite

            apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b es_pred₁_ordered_es_pred₂
          . case neg ce₁₂_encap =>
            have ce₁₂_no_encap_false : (ce₁.NoEncapSameAddressDowngrade s₁ ∧ ce₂.NoEncapSameAddressDowngrade s₂) = false := by
              simp at ce₁₂_encap
              simp [ce₁₂_encap]
              exact ce₁₂_encap
            simp [ce₁₂_no_encap_false] at ordered_ite
            by_cases (ce₁.WithoutCoherentPermissions s₁ ∧ ce₂.External) = true
            . case pos ce₁_encap_ext =>
              simp [ce₁_encap_ext] at ordered_ite

              have h_encap_ordered : ce₁.Encapsulates ce₂ ∨ ce₁.OrderedBefore ce₂ ∨ ce₂.OrderedBefore ce₁ := by
                apply Or.rotate
                apply Or.rotate
                exact ordered_ite

              cases h_encap_ordered
              . case inl ce₁_encap_ce₂ =>
                have es₁_encap_es₂ : es_pred₁.Encapsulates es_pred₂ := by
                  unfold EventState.Encapsulates; simp
                  unfold Event.Encapsulates
                  simp [h_pred₁, h_pred₂]
                  simp [Event.oStart, Event.oEnd]
                  unfold CacheEvent.Encapsulates at ce₁_encap_ce₂
                  exact ce₁_encap_ce₂

                have es₂_no_encap := he₂_b.isBottom
                unfold Behaviour.IsBottomEvent at es₂_no_encap
                unfold Behaviour.IsNotEncapByEvent at es₂_no_encap
                simp at es₂_no_encap

                apply es₂_no_encap
                apply he₁_b.isImmPred.predInB
                exact es₁_encap_es₂
              . case inr ce₁_ordered_ce₂ =>
                have es₁_ordered_es₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁ := by
                  unfold EventState.OrderedBefore; simp
                  simp[h_pred₁, h_pred₂]
                  unfold Event.OrderedBefore
                  simp [Event.oEnd, Event.oStart]
                  simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ce₁_ordered_ce₂
                  exact ce₁_ordered_ce₂

                apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b es₁_ordered_es₂
            . case neg ce₁_no_encap_ext =>
              have ce₁₂_encap_ext_false : (ce₁.WithoutCoherentPermissions s₁ ∧ ce₂.External) = false := by
                simp at ce₁_no_encap_ext
                simp [ce₁_no_encap_ext]
                exact ce₁_no_encap_ext
              simp[ce₁₂_encap_ext_false] at ordered_ite

              by_cases (ce₁.External ∧ ce₂.WithoutCoherentPermissions s₂) = true
              . case pos ce₂_encap_ext =>
                simp[ce₂_encap_ext] at ordered_ite
                have h_encap_ordered : ce₂.Encapsulates ce₁ ∨ ce₁.OrderedBefore ce₂ ∨ ce₂.OrderedBefore ce₁ := by
                  apply Or.rotate
                  apply Or.rotate
                  exact ordered_ite

                cases h_encap_ordered
                . case inl ce₂_encap_ce₁ =>

                  have es₂_encap_es₁ : es_pred₂.Encapsulates es_pred₁ := by
                    unfold EventState.Encapsulates; simp
                    unfold Event.Encapsulates
                    simp [h_pred₁, h_pred₂]
                    simp [Event.oStart, Event.oEnd]
                    unfold CacheEvent.Encapsulates at ce₂_encap_ce₁
                    exact ce₂_encap_ce₁

                  have es₁_no_encap := he₁_b.isBottom
                  unfold Behaviour.IsBottomEvent at es₁_no_encap
                  unfold Behaviour.IsNotEncapByEvent at es₁_no_encap
                  simp at es₁_no_encap

                  apply es₁_no_encap
                  apply he₂_b.isImmPred.predInB
                  exact es₂_encap_es₁
                . case inr ce₁_ordered_ce₂ =>
                  have es₁_ordered_es₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁ := by
                    unfold EventState.OrderedBefore; simp
                    simp[h_pred₁, h_pred₂]
                    unfold Event.OrderedBefore
                    simp [Event.oEnd, Event.oStart]
                    simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ce₁_ordered_ce₂
                    exact ce₁_ordered_ce₂

                  apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b es₁_ordered_es₂
              . case neg ce₂_no_encap_ext =>
                have ce₂₁_encap_ext_false : (ce₁.External ∧ ce₂.WithoutCoherentPermissions s₂) = false := by
                  simp at ce₂_no_encap_ext
                  simp [ce₂_no_encap_ext]
                  exact ce₂_no_encap_ext
                simp[ce₂₁_encap_ext_false] at ordered_ite

                have es₁_ordered_es₂ : es_pred₁.OrderedBefore es_pred₂ ∨ es_pred₂.OrderedBefore es_pred₁ := by
                  unfold EventState.OrderedBefore; simp
                  simp[h_pred₁, h_pred₂]
                  unfold Event.OrderedBefore
                  simp [Event.oEnd, Event.oStart]
                  simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ordered_ite
                  exact ordered_ite

                apply Behaviour.es₁_ordered_es₂_imm_bottom_pred_contradiction he₁_b he₂_b es₁_ordered_es₂
        | .inr _ =>
          have e₂_well_formed := es_pred₂.sWellFormed
          simp[h_pred₂, he₂_s] at e₂_well_formed
      | .inr _ =>
        have e₁_well_formed := es_pred₁.sWellFormed
        simp[h_pred₁, he₁_s] at e₁_well_formed
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmPred.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_pred₂] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_pred₁] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmPred.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmPred.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_succ.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_pred₁] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_pred₂] at h_e_succ_is_dir
        simp at h_e_succ_is_dir

lemma Set.nonempty_unique_is_singleton {α} (s : Set α) (h_nonempty : Nonempty s)
  (h_unique : ∀ (a b : α),  a ∈ s → b ∈ s → a = b) : s.IsSingleton := by
  have ⟨a, ha⟩ := h_nonempty
  exists a
  apply Set.ext
  intro x
  constructor
  · case mp =>
    intro hxa
    exact -- canonical
      Eq.rec (motive := fun a_1 t ↦ s a_1)
        (Nonempty.rec (motive := fun t ↦ s a) (fun val ↦ ha) h_nonempty)
        (Eq.rec (motive := fun a t ↦ a = x) (Eq.refl x) hxa)
  · case mpr =>
    intro hxs
    exact h_unique x a hxs ha

/-- Lemma 1 from the Doc.
The set of Immediate Bottom Predecessors is Empty or Unique. (without the φ on the predecessor yet.)
-/
lemma Behaviour.immediate_bottom_predecessor_empty_or_unique (b : Behaviour) (es_succ : EventState)
  (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_preds := b.ImmBottomPredecessors es_succ; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : EventState), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_unique b es_succ e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Add constraint `p` on predecessor -/

def Event.PropOnEvent (e : Event) (p : Event → Prop) : Prop := p e
def EventState.PropOnEvent (es : EventState) (p : Event → Prop) : Prop := p es.e

structure Behaviour.IsImmediateBottomPredSatisfyingProp (b : Behaviour) (e_pred e_succ : EventState) (p : Event → Prop) where
  isImmBottomPred : b.IsImmediateBottomPred e_pred e_succ
  satisfyP : e_pred.PropOnEvent p

def Behaviour.ImmediateBottomPredSatisfyingProp : Behaviour → EventState → EventState → (Event → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomPredSatisfyingProp e_pred e_succ p

def Behaviour.ImmBottomPredecessorsSatisfyingP : Behaviour → EventState → (Event → Prop) → Set EventState
| b, e_succ, p => {e_pred ∈ b.es | b.ImmediateBottomPredSatisfyingProp e_pred e_succ p}

lemma Behaviour.immediate_bottom_predecessor_satisfying_p_unique (b : Behaviour) (es_succ : EventState)
  (es_pred₁ es_pred₂ : EventState) (p : Event → Prop) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomPredSatisfyingProp es_pred₁ es_succ p) (he₂_b : b.IsImmediateBottomPredSatisfyingProp es_pred₂ es_succ p) :
  es_pred₁ = es_pred₂ := by
    have he₁_b' : b.IsImmediateBottomPred es_pred₁ es_succ := by
      constructor
      exact he₁_b.isImmBottomPred.isImmPred
      exact he₁_b.isImmBottomPred.isBottom
    have he₂_b' : b.IsImmediateBottomPred es_pred₂ es_succ := by
      constructor
      exact he₂_b.isImmBottomPred.isImmPred
      exact he₂_b.isImmBottomPred.isBottom

    apply Behaviour.immediate_bottom_predecessor_unique b es_succ es_pred₁ es_pred₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 1, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_predecessor_satisfying_p_empty_or_unique (b : Behaviour) (es_succ : EventState) (p : Event → Prop)
  (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_preds := b.ImmBottomPredecessorsSatisfyingP es_succ p; imm_bottom_preds = ∅ ∨ imm_bottom_preds.IsSingleton := by
  intro imm_bottom_preds
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_preds = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : EventState), e₁ ∈ imm_bottom_preds → e₂ ∈ imm_bottom_preds → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_predecessor_satisfying_p_unique b es_succ e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_preds h_nonempty' h_unique)

/- Now define the immediate bottom successor. -/

def EventState.Successor : EventState → EventState → Prop
| ⟨e₁, _, _⟩, ⟨e₂, _, _⟩ => e₁.Successor e₂

structure Behaviour.ImmediateSuccessorConstraint (b : Behaviour) (e_pred e_succ : EventState) where
  isSucc : e_pred.Successor e_succ
  noIntermediate : b.NoIntermediateEvent e_pred e_succ
  sameAddress : e_pred.SameAddress e_succ
  sameStructure : e_pred.SameStructure e_succ
  predInB : e_pred ∈ b.es
  succInB : e_succ ∈ b.es

structure Behaviour.IsImmediateBottomSucc (b : Behaviour) (e_pred e_succ : EventState) where
  isImmSucc : b.ImmediateSuccessorConstraint e_pred e_succ
  isBottom : b.IsBottomEvent e_succ

def Behaviour.ImmediateBottomSuccessor : Behaviour → EventState → EventState → Prop
| b, e_pred, e_succ => b.IsImmediateBottomSucc e_pred e_succ

def Behaviour.ImmBottomSuccessors : Behaviour → EventState → Set EventState
| b, e_pred => {e_succ ∈ b.es | b.ImmediateBottomSuccessor e_pred e_succ}

lemma Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction {es_pred es_succ₁ es_succ₂ : EventState} {b : Behaviour}
(he₁_b : b.IsImmediateBottomSucc es_pred es_succ₁) (he₂_b : b.IsImmediateBottomSucc es_pred es_succ₂)
(hes₁_ordered_es₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁)
: False := by
  /- Show contradiction from ce₁ and ce₂ ordered -/
  cases hes₁_ordered_es₂
  . case inl es₁_ordered_es₂ =>
    have he_no_intermediate_to_e_suc₂ := he₂_b.isImmSucc.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he_no_intermediate_to_e_suc₂
    unfold Behaviour.NoIntermediateEvent at he_no_intermediate_to_e_suc₂
    unfold Behaviour.OrderedBetween at he_no_intermediate_to_e_suc₂
    simp at he_no_intermediate_to_e_suc₂
    have e_pred_o_e_succ₁ := he₁_b.isImmSucc.isSucc
    unfold Event.Predecessor at e_pred_o_e_succ₁
    unfold EventState.Successor at e_pred_o_e_succ₁
    simp at e_pred_o_e_succ₁

    apply he_no_intermediate_to_e_suc₂
    apply he₁_b.isImmSucc.succInB
    constructor
    unfold autoParam
    . case a.pred =>
      unfold Event.Successor at e_pred_o_e_succ₁
      unfold Event.Predecessor at e_pred_o_e_succ₁
      simp at e_pred_o_e_succ₁
      unfold EventState.OrderedBefore
      simp
      exact e_pred_o_e_succ₁
    . case a.succ =>
      unfold autoParam
      exact es₁_ordered_es₂
  . case inr es₂_ordered_es₁ =>
    have he₁_no_intermediate_to_e_suc := he₁_b.isImmSucc.noIntermediate
    unfold Behaviour.ImmediatePredecessorConstraint at he₁_no_intermediate_to_e_suc
    unfold Behaviour.NoIntermediateEvent at he₁_no_intermediate_to_e_suc
    unfold Behaviour.OrderedBetween at he₁_no_intermediate_to_e_suc
    simp at he₁_no_intermediate_to_e_suc
    have e_pred_o_e_succ₂ := he₂_b.isImmSucc.isSucc
    unfold Event.Successor at e_pred_o_e_succ₂
    unfold EventState.Successor at e_pred_o_e_succ₂
    simp at e_pred_o_e_succ₂

    apply he₁_no_intermediate_to_e_suc
    apply he₂_b.isImmSucc.succInB
    constructor
    unfold autoParam
    . case a.pred =>
      unfold Event.Successor at e_pred_o_e_succ₂
      unfold Event.Predecessor at e_pred_o_e_succ₂
      simp at e_pred_o_e_succ₂
      unfold EventState.OrderedBefore
      simp
      exact e_pred_o_e_succ₂
    . case a.succ =>
      unfold autoParam
      exact es₂_ordered_es₁

lemma Behaviour.immediate_bottom_successor_unique (b : Behaviour) (es_pred : EventState)
  (es_succ₁ es_succ₂ : EventState) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomSucc es_pred es_succ₁) (he₂_b : b.IsImmediateBottomSucc es_pred es_succ₂) :
  es_succ₁ = es_succ₂ := by
    by_contra h_e_pred_diff
    match h_succ₁ : es_succ₁.e, h_succ₂ : es_succ₂.e with
    | .directoryEvent de₁, .directoryEvent de₂ =>
      -- Use OrderedDirectoryEvents to show de₁ and de₂ are ordered → Contradiction.
      have de₁_de₂_ordered_prop := haddress_ordered.dir_ordered de₁ de₂
      have hepred_sa_succ₁ := he₁_b.isImmSucc.sameAddress
      have hepred_sa_succ₂ := he₂_b.isImmSucc.sameAddress
      have es₁_same_addr_es₂ := Event.same_address_reflexive' he₁_b.isImmSucc.sameAddress he₂_b.isImmSucc.sameAddress
      rw [h_succ₁, h_succ₂] at es₁_same_addr_es₂
      have de₁_de₂_ordered := de₁_de₂_ordered_prop es₁_same_addr_es₂

      have es_succ₁_ordered_es_succ₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁ := by
        unfold EventState.OrderedBefore; simp
        simp[h_succ₁, h_succ₂]
        simp[Event.OrderedBefore, Event.oEnd, Event.oStart]
        simp[DirectoryEvent.OrderedBefore] at de₁_de₂_ordered
        exact de₁_de₂_ordered

      apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b es_succ₁_ordered_es_succ₂
    | .cacheEvent ce₁, .cacheEvent ce₂ =>
      /- Part 1. Use OrderedCacheEvents to show that ce₁ and ce₂ (which are bottom predecessors to e_succ)
      are always ordered. Part 2. This is a contradiction with ImmediateBottomPred's NoIntermediatePred. -/
      -- Part 1. ce₁ and ce₂ are OrderedCacheEvents
      match he₁_s : es_succ₁.s with
      | .inl s₁ =>
        match he₂_s : es_succ₂.s with
        | .inl s₂ =>
          have hce₁_o_ce₂ := haddress_ordered.cache_ordered ce₁ ce₂ s₁ s₂  -- need state s₁ s₂ that ce₁ and ce₂ are made on.
          -- Same cid, e_pred₁ e_pred₂
          have hce₁_cid_csucc := he₁_b.isImmSucc.sameStructure
          have hce₂_cid_csucc := he₂_b.isImmSucc.sameStructure
          have es₁_same_structure_es₂ := Event.same_structure_reflexive' hce₁_cid_csucc hce₂_cid_csucc
          unfold EventState.SameStructure at es₁_same_structure_es₂
          unfold Event.SameStructure at es₁_same_structure_es₂
          rw [h_succ₁] at es₁_same_structure_es₂
          unfold CacheEvent.SameCache at es₁_same_structure_es₂
          unfold DirectoryEvent.SameStructure at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          unfold Event.SameStructureRelation at es₁_same_structure_es₂
          simp at es₁_same_structure_es₂
          -- Same Address, e_pred₁ e_pred₂
          have hce₁_a_csucc := he₁_b.isImmSucc.sameAddress
          have hce₂_a_csucc := he₂_b.isImmSucc.sameAddress
          have es₁_same_addr_es₂ := Event.same_address_reflexive' hce₁_a_csucc hce₂_a_csucc
          unfold EventState.SameAddress at es₁_same_addr_es₂
          unfold Event.SameAddress at es₁_same_addr_es₂
          rw [h_succ₁] at es₁_same_addr_es₂
          unfold CacheEvent.SameAddress at es₁_same_addr_es₂
          unfold DirectoryEvent.SameAddress at es₁_same_addr_es₂
          unfold Event.SameStructureRelation at es₁_same_addr_es₂
          simp at es₁_same_addr_es₂

          rw [h_succ₂] at es₁_same_structure_es₂ es₁_same_addr_es₂
          simp at es₁_same_structure_es₂ es₁_same_addr_es₂

          -- have the big if then else from OrderedCacheEvents:
          have ordered_ite := hce₁_o_ce₂ es₁_same_structure_es₂ es₁_same_addr_es₂

          /- Show for all cases of ce₁ ce₂ s₁ s₂, ce₁ and ce₂ are either:
            1. ordered (contradiction with NoIntermediatePred)
            2. one encapsulates another (contradiction with isBottom)
          -/
          by_cases (ce₁.NoEncapSameAddressDowngrade s₁ ∧ ce₂.NoEncapSameAddressDowngrade s₂) = true
          . case pos ce₁₂_no_encap =>
            simp [ce₁₂_no_encap] at ordered_ite

            have es_succ₁_ordered_es_succ₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁ := by
              unfold EventState.OrderedBefore
              simp
              simp [h_succ₁, h_succ₂]
              simp [Event.OrderedBefore, ordered_ite]
              simp [Event.oEnd, Event.oStart]
              simp [CacheEvent.OrderedBefore] at ordered_ite
              exact ordered_ite

            apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b es_succ₁_ordered_es_succ₂
          . case neg ce₁₂_encap =>
            have ce₁₂_no_encap_false : (ce₁.NoEncapSameAddressDowngrade s₁ ∧ ce₂.NoEncapSameAddressDowngrade s₂) = false := by
              simp at ce₁₂_encap
              simp [ce₁₂_encap]
              exact ce₁₂_encap
            simp [ce₁₂_no_encap_false] at ordered_ite
            by_cases (ce₁.WithoutCoherentPermissions s₁ ∧ ce₂.External) = true
            . case pos ce₁_encap_ext =>
              simp [ce₁_encap_ext] at ordered_ite

              have h_encap_ordered : ce₁.Encapsulates ce₂ ∨ ce₁.OrderedBefore ce₂ ∨ ce₂.OrderedBefore ce₁ := by
                apply Or.rotate
                apply Or.rotate
                exact ordered_ite

              cases h_encap_ordered
              . case inl ce₁_encap_ce₂ =>
                have es₁_encap_es₂ : es_succ₁.Encapsulates es_succ₂ := by
                  unfold EventState.Encapsulates; simp
                  unfold Event.Encapsulates
                  simp [h_succ₁, h_succ₂]
                  simp [Event.oStart, Event.oEnd]
                  unfold CacheEvent.Encapsulates at ce₁_encap_ce₂
                  exact ce₁_encap_ce₂

                have es₂_no_encap := he₂_b.isBottom
                unfold Behaviour.IsBottomEvent at es₂_no_encap
                unfold Behaviour.IsNotEncapByEvent at es₂_no_encap
                simp at es₂_no_encap

                apply es₂_no_encap
                apply he₁_b.isImmSucc.succInB
                exact es₁_encap_es₂
              . case inr ce₁_ordered_ce₂ =>
                have es₁_ordered_es₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁ := by
                  unfold EventState.OrderedBefore; simp
                  simp[h_succ₁, h_succ₂]
                  unfold Event.OrderedBefore
                  simp [Event.oEnd, Event.oStart]
                  simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ce₁_ordered_ce₂
                  exact ce₁_ordered_ce₂

                apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b es₁_ordered_es₂
            . case neg ce₁_no_encap_ext =>
              have ce₁₂_encap_ext_false : (ce₁.WithoutCoherentPermissions s₁ ∧ ce₂.External) = false := by
                simp at ce₁_no_encap_ext
                simp [ce₁_no_encap_ext]
                exact ce₁_no_encap_ext
              simp[ce₁₂_encap_ext_false] at ordered_ite

              by_cases (ce₁.External ∧ ce₂.WithoutCoherentPermissions s₂) = true
              . case pos ce₂_encap_ext =>
                simp[ce₂_encap_ext] at ordered_ite
                have h_encap_ordered : ce₂.Encapsulates ce₁ ∨ ce₁.OrderedBefore ce₂ ∨ ce₂.OrderedBefore ce₁ := by
                  apply Or.rotate
                  apply Or.rotate
                  exact ordered_ite

                cases h_encap_ordered
                . case inl ce₂_encap_ce₁ =>

                  have es₂_encap_es₁ : es_succ₂.Encapsulates es_succ₁ := by
                    unfold EventState.Encapsulates; simp
                    unfold Event.Encapsulates
                    simp [h_succ₁, h_succ₂]
                    simp [Event.oStart, Event.oEnd]
                    unfold CacheEvent.Encapsulates at ce₂_encap_ce₁
                    exact ce₂_encap_ce₁

                  have es₁_no_encap := he₁_b.isBottom
                  unfold Behaviour.IsBottomEvent at es₁_no_encap
                  unfold Behaviour.IsNotEncapByEvent at es₁_no_encap
                  simp at es₁_no_encap

                  apply es₁_no_encap
                  apply he₂_b.isImmSucc.succInB
                  exact es₂_encap_es₁
                . case inr ce₁_ordered_ce₂ =>
                  have es₁_ordered_es₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁ := by
                    unfold EventState.OrderedBefore; simp
                    simp[h_succ₁, h_succ₂]
                    unfold Event.OrderedBefore
                    simp [Event.oEnd, Event.oStart]
                    simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ce₁_ordered_ce₂
                    exact ce₁_ordered_ce₂

                  apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b es₁_ordered_es₂
              . case neg ce₂_no_encap_ext =>
                have ce₂₁_encap_ext_false : (ce₁.External ∧ ce₂.WithoutCoherentPermissions s₂) = false := by
                  simp at ce₂_no_encap_ext
                  simp [ce₂_no_encap_ext]
                  exact ce₂_no_encap_ext
                simp[ce₂₁_encap_ext_false] at ordered_ite

                have es₁_ordered_es₂ : es_succ₁.OrderedBefore es_succ₂ ∨ es_succ₂.OrderedBefore es_succ₁ := by
                  unfold EventState.OrderedBefore; simp
                  simp[h_succ₁, h_succ₂]
                  unfold Event.OrderedBefore
                  simp [Event.oEnd, Event.oStart]
                  simp [CacheEvent.OrderedBefore, Event.oEnd, Event.oStart] at ordered_ite
                  exact ordered_ite

                apply Behaviour.es₁_ordered_es₂_imm_bottom_succ_contradiction he₁_b he₂_b es₁_ordered_es₂
        | .inr _ =>
          have e₂_well_formed := es_succ₂.sWellFormed
          simp[h_succ₂, he₂_s] at e₂_well_formed
      | .inr _ =>
        have e₁_well_formed := es_succ₁.sWellFormed
        simp[h_succ₁, he₁_s] at e₁_well_formed
    | .directoryEvent de, .cacheEvent ce =>
      have h_e_succ_is_dir   := he₁_b.isImmSucc.sameStructure
      have h_e_succ_is_cache := he₂_b.isImmSucc.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_pred.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_succ₂] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_succ₁] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
    | .cacheEvent ce, .directoryEvent de =>
      have h_e_succ_is_cache := he₁_b.isImmSucc.sameStructure
      have h_e_succ_is_dir   := he₂_b.isImmSucc.sameStructure

      unfold EventState.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructure at h_e_succ_is_dir h_e_succ_is_cache
      unfold Event.SameStructureRelation at h_e_succ_is_dir h_e_succ_is_cache
      simp at h_e_succ_is_dir h_e_succ_is_cache
      unfold CacheEvent.SameCache at h_e_succ_is_cache

      match hsucc : es_pred.e with
      | .directoryEvent de_succ =>
        rw [hsucc] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
        rw [h_succ₁] at h_e_succ_is_cache
        simp at h_e_succ_is_cache
      | .cacheEvent ce_succ =>
        rw [hsucc] at h_e_succ_is_dir
        simp at h_e_succ_is_dir
        rw [h_succ₂] at h_e_succ_is_dir
        simp at h_e_succ_is_dir

lemma Behaviour.immediate_bottom_successor_empty_or_unique (b : Behaviour) (es_pred : EventState)
  (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_succs := b.ImmBottomSuccessors es_pred; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : EventState), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_unique b es_pred e₁ e₂
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Verision of Immediate Bottom Successor that also satisfies Prop `p`. -/

structure Behaviour.IsImmediateBottomSuccSatisfyingProp (b : Behaviour) (e_pred e_succ : EventState) (p : Event → Prop) where
  isImmBottomSucc : b.IsImmediateBottomSucc e_pred e_succ
  satisfyP : e_succ.PropOnEvent p

def Behaviour.ImmediateBottomSuccSatisfyingProp : Behaviour → EventState → EventState → (Event → Prop) → Prop
| b, e_pred, e_succ, p => b.IsImmediateBottomSuccSatisfyingProp e_pred e_succ p

def Behaviour.ImmBottomSuccessorsSatisfyingP : Behaviour → EventState → (Event → Prop) → Set EventState
| b, e_pred, p => {e_succ ∈ b.es | b.ImmediateBottomSuccSatisfyingProp e_pred e_succ p}

lemma Behaviour.immediate_bottom_successor_satisfying_p_unique (b : Behaviour) (es_pred : EventState)
  (es_succ₁ es_succ₂ : EventState) (p : Event → Prop) (haddress_ordered : OrderedAddressEvents)
  (he₁_b : b.IsImmediateBottomSuccSatisfyingProp es_pred es_succ₁ p) (he₂_b : b.IsImmediateBottomSuccSatisfyingProp es_pred es_succ₂ p) :
  es_succ₁ = es_succ₂ := by
    have he₁_b' : b.IsImmediateBottomSucc es_pred es_succ₁ := by
      constructor
      exact he₁_b.isImmBottomSucc.isImmSucc
      exact he₁_b.isImmBottomSucc.isBottom
    have he₂_b' : b.IsImmediateBottomSucc es_pred es_succ₂ := by
      constructor
      exact he₂_b.isImmBottomSucc.isImmSucc
      exact he₂_b.isImmBottomSucc.isBottom

    apply Behaviour.immediate_bottom_successor_unique b es_pred es_succ₁ es_succ₂ haddress_ordered he₁_b' he₂_b'

/-- Lemma 2, with a Prop `p` on predecessors. -/
lemma Behaviour.immediate_bottom_successor (b : Behaviour) (es_pred : EventState) (p : Event → Prop)
  (haddress_ordered : OrderedAddressEvents) :
  let imm_bottom_succs := b.ImmBottomSuccessorsSatisfyingP es_pred p; imm_bottom_succs = ∅ ∨ imm_bottom_succs.IsSingleton := by
  intro imm_bottom_succs
  -- unfold ImmBottomPredecessors at imm_bottom_preds
  by_cases (imm_bottom_succs = ∅)
  · case pos h_empty => exact Or.inl h_empty
  · case neg h_nonempty =>
    have h_nonempty' := Set.nonempty_iff_ne_empty'.mpr h_nonempty
    have h_unique : ∀ (e₁ e₂ : EventState), e₁ ∈ imm_bottom_succs → e₂ ∈ imm_bottom_succs → e₁ = e₂ := by
      intro e₁ e₂ he₁ he₂
      apply Behaviour.immediate_bottom_successor_satisfying_p_unique b es_pred e₁ e₂ p
      exact haddress_ordered
      exact And.right he₁
      exact And.right he₂
    exact Or.inr (Set.nonempty_unique_is_singleton imm_bottom_succs h_nonempty' h_unique)

/- Def 2.32 Behaviour.PreviousEvent -/
open scoped Classical in
noncomputable def Behaviour.PreviousEvent (b : Behaviour) (e : EventState) (haddress_ordered : OrderedAddressEvents) : Option EventState :=
  by classical exact
  -- Not clear how to open up `preds_empty_or_singleton` and use the `empty or singleton` statement inside?
  let preds_empty_or_singleton := b.ImmBottomPredecessors e -- haddress_ordered
  have h_empty_or_unique := b.immediate_bottom_predecessor_empty_or_unique e haddress_ordered
  if he : preds_empty_or_singleton = ∅ then -- Can't synthesize?
    none
  else
    (h_empty_or_unique.resolve_left he).choose

def EventState.r : EventState → ValidRequest
| ⟨e, _, _⟩ => e.r
def EventState.SucceedingState : EventState → (EntryState → EntryState)
| ⟨e, _, _⟩ => e.SucceedingState

def EventState.a : EventState → Addr
| ⟨e, _, _⟩ => e.a
def EventState.atCid : EventState → CacheId → Prop
| ⟨e, _, _⟩, cid => e.atCid cid

def Behaviour.eventsAtCacheEntry (b : Behaviour) (a : Addr) (cid : CacheId) (haddress_ordered : OrderedAddressEvents) : List EventState :=
  let e_at_centry := {e ∈ b.es | e.a = a ∧ e.atCid cid}
  /- Don't know how to use e_at_centry and produce an ordered list? -/
  sorry

/- Def 2.33 Behaviour.StateBefore -/
noncomputable def Behaviour.StateBefore (b : Behaviour) (e : EventState) (haddress_ordered : OrderedAddressEvents) (s_i : EntryState)
: EntryState :=
  let e_pred? := b.PreviousEvent e haddress_ordered
  match e_pred? with
  | .none => s_i
  | .some e_pred =>
    let entry_state_pred_pred := b.StateBefore e_pred haddress_ordered s_i
    e_pred.SucceedingState entry_state_pred_pred
termination_by sizeOf (b.ImmBottomPredecessors e)
-- decreasing_by sizeOf (b.ImmBottomPredecessors e)
