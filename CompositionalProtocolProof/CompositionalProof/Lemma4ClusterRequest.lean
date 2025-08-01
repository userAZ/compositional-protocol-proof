import CompositionalProtocolProof.CompoundSWMR
import CompositionalProtocolProof.CompoundProtocol
import CompositionalProtocolProof.BehaviourHelpers
import CompositionalProtocolProof.BehaviourRelationDefs
import CompositionalProtocolProof.CompositionalProof.ProofBasic
import CompositionalProtocolProof.CompositionalProof.ProofBasicHelperLemmas

import CompositionalProtocolProof.CompositionalProof.Lemma5GlobalRequest

variable (n : Nat)

lemma Behaviour.satisfies_compound_swmr_of_cluster_directory_with_no_global_perms_gets_global_perms
  (b : Behaviour n) (init : InitialSystemState n)
  (e_cdir : Event n) (hcdir_in_b : e_gdown ∈ b)
  (hcdir_cluster_dir : e_cdir.isClusterDir)
  (hcdir_not_down : ¬ e_cdir.down)
  (hno_global_perms : Behaviour.clusterDirNoPermsInGlobalCache n b init e_cdir)
  (htranslation : Behaviour.existsGlobalCacheAccessOfDirEvent n b e_cdir)
  : Behaviour.dirEventStateLeGlobalCacheState n b init e_cdir := by
  simp[dirEventStateLeGlobalCacheState]
  sorry

/-- Lemma 4: A global downgrade `e_gdown` leaves it's corresponding cluster directory
in state `s` ≤ `e_gdown.MRS` -/
lemma CompoundProtocol.clusterDirectoryEvent.satisfies_compound_swmr
  (cmp : CompoundProtocol n)
  (b : Behaviour n) (init : InitialSystemState n)
  (e_cdir : Event n) (hcdir_in_b : e_gdown ∈ b)
  (hcdir_cluster_dir : e_cdir.isClusterDir)
  (hcdir_not_down : ¬ e_cdir.down)
  : CompoundSWMR n b init e_cdir := by
  apply CompoundSWMR.cDir
  . case cdir_satisfies_cmp_swmr =>
    simp [Behaviour.clusterDirEvent.satisfiesCompoundSWMR]
    intro haux_is_gcache
    constructor
    exact haux_is_gcache
    . case stateAfterLeGlobalCache =>
      -- simp[Behaviour.dirEventStateLeGlobalCacheState']
      /- Strategy: Show the latest event is the one corresponding to
      lower state to I (for fwd SW) or going to S (for fwd MR).-/
      /- NOTE: must know the state before this `e_gdown` satisfies Compound SWMR;
      how should I transfer the def of events before `e_creq` satisfiy Compound SWMR to `e_gdown`.
      Maybe not needed. Let's try the proof first. -/
      -- show the latest directory event `e_cdir_down` before `e_gdown` always produces state ≤ state after `e_gdown`
      have hcluster_translation_to_global_cache := cmp.shimAxioms.clusterToGlobal b init e_cdir (hcdir_cluster_dir.dirAtDir)

      -- Get the corresponding cluster to the global cache;
      -- cases hgdown_translation_to_cluster
      cases hcluster_translation_to_global_cache
      . case encapGlobalCache hno_global_perms htranslation =>
        sorry
      . case noGlobalCache hhas_global_perms hno_encap =>
        sorry

/-
/-- Lemma 4 : A Cluster Request Event leaves a protocol in Compound SWMR. -/
lemma Behaviour.cluster_request_enforces_compound_swmr
  (b : Behaviour n) (init : InitialSystemState n)
  (cmp : CompoundProtocol n)
  (e : Event n) (he_in_b : e ∈ b)
  -- Initial or Current state just before Event `e` in Compound SWMR
  (hpred_cdir_cmp_swmr : ∀ e_cdir ∈ b, e_cdir.isClusterDir → b.clusterDirFinishBeforeUnrelated n init e e_cdir → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache n b init e_cdir)
  (hpred_gcache_cmp_swmr : ∀ e_gcache ∈ b, e_gcache.isGlobalCache → b.globalCacheFinishBeforeUnrelated n init e e_gcache → CompoundSWMR.stateAfterClusterDirEventLeGlobalCache' n b init e_gcache)
  : b.allClusterEventCorrespondingDirEventSatisfyCompoundSWMR n init e := by
  sorry
-/
