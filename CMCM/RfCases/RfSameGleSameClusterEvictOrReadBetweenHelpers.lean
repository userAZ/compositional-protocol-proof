/-
  Helper lemmas specifically for the `rf.sameGle.evictOrReadBetweenWAndRCleSameCluster` case
  (same GLE, same cluster, with evicts/reads between write's and read's CLEs).

  These lemmas handle the diffCache subcase for the evictOrReadBetween CLE relationship.
  The sameCache subcase uses the general `no_dir_write_between_same_cache` from RfProofHelpers.

  General helpers (same_gle_implies_same_protocol, diffCache_coherent_globalDowngrade,
  globalToCluster_extract_proxy_and_dir, diffCache_coherent_encapProxyAndDir,
  no_dir_write_between_same_cache) are in RfProofHelpers.lean for reuse across cases.
-/
import CMCM.RfProofHelpers

variable {n : ℕ}

/-- Helper: When e_w's CLE has evicts/reads between it and e_r's CLE,
    e_r's CLE is ordered after e_w's CLE (rCleAfterWCle).
    Extracted directly from the evictOrReadBetween.wObR field. -/
lemma evictOrReadBtn_diffCache_rCleAfterWCle
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  : WriteRead.wObRCle.diffCache.rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin :=
  hevict_or_read_between.wObR

/-- Helper: No cache-level evict-SW between e_w and the cache-level downgrade e_r_down.

    With evictOrReadBetween, all intermediate events between w_cle and r_cle are reads/evicts
    (not write-downgrades). An evict-SW at the same cache between e_w and e_r_down would
    need to have a CLE between e_w_cle and e_r_cle — but such an evict is permitted by
    the evictOrReadBetween hypothesis (it could be a dir-read/evict). The key argument is
    that any such evict must not be a cache-level evict-SW that changes the ownership state,
    which the interDirEvictOrRead condition constrains. -/
lemma evictOrReadBtn_diffCache_noEvictBetween_noEvict
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noEvict b e_w hencapPDC.existsRDownAtW.choose := by
  sorry

/-- Helper: Every intervening write between e_w and e_r_down falls into one of the three
    excludeOtherWrites cases. With evictOrReadBetween, intermediate directory events are
    reads/evicts, so any write's CLE (a dir-write) between the CLE boundaries would
    contradict the interDirEvictOrRead condition. -/
lemma evictOrReadBtn_diffCache_noEvictBetween_noWrite
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noWrite b init e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapDir.existsRClusterDirDown.choose := by
  -- noWrite quantifies over all cluster cache writes (not down).
  -- For each e_inter, case-split on same cache / diff cache same cluster / diff cluster.
  -- In same cache and diff-cache-same-cluster cases, pick e_w_cle as the existential
  -- witness for interCleNotBetween. The antecedent requires e_w_cle.OrderedBetween
  -- e_w_cle e_r_cdir_down, whose first component e_w_cle < e_w_cle is reflexive → contradiction.
  have hr_down_struct := hencapPDC.existsRDownAtW.choose_spec.right.left
  have he_w_cle_in_b := hw_c_and_g_lin.hreq's_dir_access.choose_spec.left
  intro e_inter _hinter_in_b _hinter_cluster _hinter_write hinter_not_down
  by_cases h_same_cache : e_inter.struct = e_w.struct
  · -- Same cache → otherWSameCache
    have hsame_w : e_inter.sameStructure n e_w := by unfold Event.sameStructure; exact h_same_cache
    have hsame_r : e_inter.sameStructure n hencapPDC.existsRDownAtW.choose := by
      unfold Event.sameStructure; exact h_same_cache.trans hr_down_struct.symm
    exact .otherWSameCache {
      notDown := hinter_not_down
      sameProtocol := ⟨sameStructure_implies_sameProtocol hsame_w,
                       sameStructure_implies_sameProtocol hsame_r⟩
      sameCache := ⟨hsame_w, hsame_r⟩
      interCleNotBetween := ⟨hw_c_and_g_lin.hreq's_dir_access.choose, he_w_cle_in_b,
        fun _ => fun ⟨_, hcle_ob⟩ => Event.contradiction_of_reflexive_ordered_before n hcle_ob.pred⟩
    }
  · by_cases h_same_proto : e_inter.protocol = e_w.protocol
    · -- Different cache, same cluster → otherWDiffCacheSameCluster
      have hr_down_proto : hencapPDC.existsRDownAtW.choose.protocol = e_w.protocol :=
        sameStructure_implies_sameProtocol (by unfold Event.sameStructure; exact hr_down_struct)
      exact .otherWDiffCacheSameCluster {
        sameProtocol := ⟨by unfold Event.sameProtocol; exact h_same_proto,
                         by unfold Event.sameProtocol; exact h_same_proto.trans hr_down_proto.symm⟩
        diffCache := ⟨by unfold Event.diffStructure; exact h_same_cache,
                      by unfold Event.diffStructure; intro heq; exact h_same_cache (heq.trans hr_down_struct)⟩
        interCleNotBetween := ⟨hw_c_and_g_lin.hreq's_dir_access.choose, he_w_cle_in_b,
          fun _ => fun hob => Event.contradiction_of_reflexive_ordered_before n hob.pred⟩
      }
    · -- Different cluster → otherWDiffCluster
      exact .otherWDiffCluster {
        interCleNotBetween := by
          sorry
      }

/-- Construct the noEvictBetween.cond for the evictOrReadBetween case.
    Fields:
    - wObRDown: from hencapPDC.existsRDownAtW
    - noEvictBtn: from evictOrReadBtn_diffCache_noEvictBetween_noEvict
    - noWriteBtn: from evictOrReadBtn_diffCache_noEvictBetween_noWrite -/
lemma evictOrReadBtn_diffCache_noEvictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : WriteRead.noEvictBetween.cond b init
      e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapDir.existsRClusterDirDown.choose := {
    wObRDown := hencapPDC.existsRDownAtW.choose_spec.right.right.right
    noEvictBtn := evictOrReadBtn_diffCache_noEvictBetween_noEvict hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
    noWriteBtn := evictOrReadBtn_diffCache_noEvictBetween_noWrite hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
  }

/-- No directory-level write between e_w_cle and e_r_cdir_down.
    With evictOrReadBetween, intermediate events are reads/evicts, so no directory write
    from a same-cluster or diff-cluster write can be between the boundaries. -/
lemma evictOrReadBtn_diffCache_evictBetween_noWriteBtn
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Event.Between.noDirWrite cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := by
  unfold Event.Between.noDirWrite
  intro h
  cases h with
  | diffCluster e_w_inter hdiff =>
    -- existsClusterDirDown gives e_cdir_down: a dir-write between e_w_cle and e_r_cdir_down
    -- Use dir_ordered on e_cdir_down vs e_r_cle (both directory events)
    -- Case 1: e_cdir_down < e_r_cle → interDirEvictOrRead gives isDirRead, contradicting isDirWrite
    -- Case 2: e_r_cle < e_cdir_down → timing contradiction via encapDirRelation
    obtain ⟨e_cdir_down, hcdir_mem, hcdir_dir, hcdir_proto, hcdir_isDirWrite, _, _, hcdir_between⟩ :=
      hdiff.existsClusterDirDown
    -- Extract DirectoryEvent from e_cdir_down
    have ⟨de_cdir, hev_cdir⟩ : ∃ de, e_cdir_down = .directoryEvent de := by
      match h : e_cdir_down with
      | .directoryEvent de => exact ⟨de, rfl⟩
      | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hcdir_dir
    -- Extract DirectoryEvent from e_r_cle
    have hr_cle_dir_event : hr_c_and_g_lin.hreq's_dir_access.choose.isDirectoryEvent :=
      hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
    have ⟨de_r_cle, hev_r_cle⟩ : ∃ de, hr_c_and_g_lin.hreq's_dir_access.choose = .directoryEvent de := by
      match h : hr_c_and_g_lin.hreq's_dir_access.choose with
      | .directoryEvent de => exact ⟨de, rfl⟩
      | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hr_cle_dir_event
    -- Use dir_ordered: e_cdir_down and e_r_cle are both directory events
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_cdir de_r_cle |>.ordered
    simp [DirectoryEvent.Ordered] at hdir_ordered
    cases hdir_ordered with
    | inl hcdir_ob_r_cle =>
      -- Case 1: e_cdir_down < e_r_cle → interDirEvictOrRead gives isDirRead
      have h_proto : e_cdir_down.sameProtocol n hw_c_and_g_lin.hreq's_dir_access.choose := by
        unfold Event.sameProtocol
        exact hcdir_proto
      have h_struct : e_cdir_down.sameStructure n hw_c_and_g_lin.hreq's_dir_access.choose := by
        have hw_cle_dir : hw_c_and_g_lin.hreq's_dir_access.choose.isDirectoryEvent :=
          hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
        have ⟨de_w_cle, hev_w_cle⟩ : ∃ de, hw_c_and_g_lin.hreq's_dir_access.choose = .directoryEvent de := by
          match h : hw_c_and_g_lin.hreq's_dir_access.choose with
          | .directoryEvent de => exact ⟨de, rfl⟩
          | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hw_cle_dir
        unfold Event.sameStructure Event.struct
        rw [hev_cdir, hev_w_cle]
        simp
        unfold Event.sameProtocol Event.protocol at h_proto
        rw [hev_cdir, hev_w_cle] at h_proto
        simp at h_proto
        exact h_proto
      have hsucc : e_cdir_down.OrderedBefore n hr_c_and_g_lin.hreq's_dir_access.choose := by
        have h_ob := @DirectoryEvent.ordered_events n de_cdir de_r_cle
          (.directoryEvent de_cdir) (.directoryEvent de_r_cle)
          rfl rfl hcdir_ob_r_cle
        rwa [← hev_cdir, ← hev_r_cle] at h_ob
      have hbetween : e_cdir_down.OrderedBetween n
          hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose := {
        pred := hcdir_between.pred
        succ := hsucc
      }
      have hdir_read : e_cdir_down.isDirReadOrEvict :=
        hevict_or_read_between.interDirEvictOrRead _ hcdir_mem ⟨h_proto, h_struct, hbetween⟩
      -- isDirRead contradicts isDirWrite
      rw [hev_cdir] at hdir_read hcdir_isDirWrite
      simp [Event.isDirReadOrEvict, Event.isDirRead] at hdir_read
      simp [Event.isDirWrite] at hcdir_isDirWrite
      simp [Request.isRead] at hdir_read
      simp [Request.isWrite] at hcdir_isDirWrite
      rw [hcdir_isDirWrite] at hdir_read
      exact absurd hdir_read (by decide)
    | inr hr_cle_ob_cdir =>
      -- Case 2: e_r_cle < e_cdir_down → timing contradiction
      have h1 : hr_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n e_cdir_down := by
        have h_ob := @DirectoryEvent.ordered_events n de_r_cle de_cdir
          (.directoryEvent de_r_cle) (.directoryEvent de_cdir)
          rfl rfl hr_cle_ob_cdir
        rwa [← hev_r_cle, ← hev_cdir] at h_ob
      have h2 := hcdir_between.succ
      -- e_r_cdir_down.oEnd < e_r_cle.oEnd from encapDirRelation
      have hrel := hencapPD.existsRClusterDirDown.choose_spec.right.right.right
      have h3 : hencapPD.existsRClusterDirDown.choose.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd := by
        match hrel with
        | .cleEncap h => exact h.2
        | .gcacheEncap _ cdownEndBeforeCle => exact cdownEndBeforeCle
      -- Chain: e_cdir.oEnd < e_r_cle.oEnd < e_cdir_down.oStart < e_cdir_down.oEnd < e_r_cdir.oStart
      -- with e_r_cdir.oEnd < e_r_cle.oEnd gives e_r_cdir.oEnd < e_r_cdir.oStart
      unfold Event.OrderedBefore at h1 h2
      rw [hev_r_cle, hev_cdir] at h1
      simp [Event.oStart, Event.oEnd] at h1
      rw [hev_cdir] at h2
      simp [Event.oStart, Event.oEnd] at h2
      rw [hev_r_cle] at h3
      simp [Event.oEnd] at h3
      have hwf_cdir := de_cdir.oWellFormed
      have hwf_rcd := hencapPD.existsRClusterDirDown.choose.oWellFormed
      exact absurd (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans h3 h1) hwf_cdir) h2) hwf_rcd) (Nat.lt_irrefl _)
  | sameCluster e_w_inter hsame =>
    -- CLE(inter) is a dir-write between e_w_cle and e_r_cdir_down.
    -- Use dir_ordered to compare CLE(inter) vs e_r_cle (both directory events).
    -- Case 1: CLE(inter) < e_r_cle → interDirEvictOrRead gives isDirRead, contradicting isDirWrite
    -- Case 2: e_r_cle < CLE(inter) → timing contradiction via encapDirRelation
    -- Extract DirectoryEvent from CLE(inter) (isDirWrite implies it's a directory event)
    have hinter_cle_dir_event : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirectoryEvent :=
      (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose_spec.right.isDirEvent
    have hinter_cle_dir_write : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirWrite :=
      hsame.cleDirWrite
    -- Extract DirectoryEvent from e_r_cle (dirAccessOfRequest.isDirEvent)
    have hr_cle_dir_event : hr_c_and_g_lin.hreq's_dir_access.choose.isDirectoryEvent :=
      hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
    -- Get the actual DirectoryEvents
    have ⟨de_inter, hev_inter⟩ : ∃ de, (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose = .directoryEvent de := by
      match h : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose with
      | .directoryEvent de => exact ⟨de, rfl⟩
      | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hinter_cle_dir_event
    have ⟨de_r_cle, hev_r_cle⟩ : ∃ de, hr_c_and_g_lin.hreq's_dir_access.choose = .directoryEvent de := by
      match h : hr_c_and_g_lin.hreq's_dir_access.choose with
      | .directoryEvent de => exact ⟨de, rfl⟩
      | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hr_cle_dir_event
    -- Use dir_ordered: CLE(inter) and e_r_cle are both directory events, so they're ordered
    have hdir_ordered := b.orderedAtEntry.dir_ordered de_inter de_r_cle |>.ordered
    simp [DirectoryEvent.Ordered] at hdir_ordered
    cases hdir_ordered with
    | inl hinter_ob_r_cle =>
      -- Case 1: CLE(inter) < e_r_cle
      -- Build IntermediateDirEvictOrRead to apply interDirEvictOrRead
      have hinter_cle_proto :=
        write_cle_protocol_eq_write_protocol (hknow_dir_access cmp b init e_w_inter)
      -- CLE(inter).protocol = e_w_inter.protocol = e_w_cle.protocol
      have h_proto : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.sameProtocol n
          hw_c_and_g_lin.hreq's_dir_access.choose := by
        unfold Event.sameProtocol
        exact hinter_cle_proto.trans hsame.sameProtocol
      have h_struct : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.sameStructure n
          hw_c_and_g_lin.hreq's_dir_access.choose := by
        have hw_cle_dir : hw_c_and_g_lin.hreq's_dir_access.choose.isDirectoryEvent :=
          hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
        have ⟨de_w_cle, hev_w_cle⟩ : ∃ de, hw_c_and_g_lin.hreq's_dir_access.choose = .directoryEvent de := by
          match h : hw_c_and_g_lin.hreq's_dir_access.choose with
          | .directoryEvent de => exact ⟨de, rfl⟩
          | .cacheEvent _ => simp [Event.isDirectoryEvent, h] at hw_cle_dir
        unfold Event.sameStructure Event.struct
        rw [hev_inter, hev_w_cle]
        simp
        unfold Event.sameProtocol Event.protocol at h_proto
        rw [hev_inter, hev_w_cle] at h_proto
        simp at h_proto
        exact h_proto
      -- succ: CLE(inter) ordered before e_r_cle
      have hsucc : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.OrderedBefore n
          hr_c_and_g_lin.hreq's_dir_access.choose := by
        have h_ob := @DirectoryEvent.ordered_events n de_inter de_r_cle
          (.directoryEvent de_inter) (.directoryEvent de_r_cle)
          rfl rfl hinter_ob_r_cle
        rwa [← hev_inter, ← hev_r_cle] at h_ob
      -- CLE(inter) is between e_w_cle and e_r_cle
      have hbetween : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.OrderedBetween n
          hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose := {
        pred := hsame.cleBetween.pred
        succ := hsucc
      }
      -- Apply interDirEvictOrRead: CLE(inter) must be isDirReadOrEvict = isDirRead
      have hinter_in_b := (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose_spec.left
      have hdir_read : (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose.isDirReadOrEvict :=
        hevict_or_read_between.interDirEvictOrRead _ hinter_in_b ⟨h_proto, h_struct, hbetween⟩
      -- isDirReadOrEvict = isDirRead. But we have isDirWrite. These contradict.
      rw [hev_inter] at hdir_read hinter_cle_dir_write
      simp [Event.isDirReadOrEvict, Event.isDirRead] at hdir_read
      simp [Event.isDirWrite] at hinter_cle_dir_write
      -- hdir_read : de_inter.req.val.rw = ReadWrite.r
      -- hinter_cle_dir_write : de_inter.req.val.rw = ReadWrite.w
      simp [Request.isRead] at hdir_read
      simp [Request.isWrite] at hinter_cle_dir_write
      rw [hinter_cle_dir_write] at hdir_read
      exact absurd hdir_read (by decide)
    | inr hr_cle_ob_inter =>
      -- Case 2: e_r_cle < CLE(inter) → timing contradiction
      -- Chain: e_r_cdir_down.oEnd < e_r_cle.oEnd < CLE(inter).oStart < CLE(inter).oEnd < e_r_cdir_down.oStart
      -- This gives e_r_cdir_down.oEnd < e_r_cdir_down.oStart, contradicting well-formedness
      have h1 : hr_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
          (hknow_dir_access cmp b init e_w_inter).hreq's_dir_access.choose := by
        have h_ob := @DirectoryEvent.ordered_events n de_r_cle de_inter
          (.directoryEvent de_r_cle) (.directoryEvent de_inter)
          rfl rfl hr_cle_ob_inter
        rwa [← hev_r_cle, ← hev_inter] at h_ob
      have h2 := hsame.cleBetween.succ
      -- Get e_r_cdir_down.oEnd < e_r_cle.oEnd from encapDirRelation
      have hrel := hencapPD.existsRClusterDirDown.choose_spec.right.right.right
      have h3 : hencapPD.existsRClusterDirDown.choose.oEnd < hr_c_and_g_lin.hreq's_dir_access.choose.oEnd := by
        match hrel with
        | .cleEncap h => exact h.2
        | .gcacheEncap _ cdownEndBeforeCle => exact cdownEndBeforeCle
      -- Derive contradiction: e_r_cdir_down.oEnd < e_r_cle.oEnd < CLE_inter.oStart
      --                       < CLE_inter.oEnd < e_r_cdir_down.oStart
      -- h1 : e_r_cle.OB CLE_inter, h2: CLE_inter.OB e_cdir_down, h3: e_cdir_down.oEnd < e_r_cle.oEnd
      -- Need well-formedness to close the contradiction
      -- Extract concrete Nat inequalities
      unfold Event.OrderedBefore at h1 h2
      rw [hev_r_cle, hev_inter] at h1
      simp [Event.oStart, Event.oEnd] at h1
      -- h1 : de_r_cle.oEnd < de_inter.oStart
      rw [hev_inter] at h2
      simp [Event.oStart, Event.oEnd] at h2
      -- h2 : de_inter.oEnd < hencapPD...choose.oStart (but oStart is still Event.oStart for opaque)
      rw [hev_r_cle] at h3
      simp [Event.oEnd] at h3
      -- h3 : hencapPD...choose.oEnd < de_r_cle.oEnd (but oEnd is still Event.oEnd for opaque)
      have hwf_inter := de_inter.oWellFormed
      -- hwf_inter : de_inter.oStart < de_inter.oEnd
      have hwf_cdir := hencapPD.existsRClusterDirDown.choose.oWellFormed
      -- The contradiction chain: h3 gives e_cdir.oEnd < de_r_cle.oEnd,
      -- h1 gives de_r_cle.oEnd < de_inter.oStart,
      -- hwf_inter gives de_inter.oStart < de_inter.oEnd,
      -- h2 gives de_inter.oEnd < e_cdir.oStart,
      -- hwf_cdir gives e_cdir.oStart < e_cdir.oEnd
      -- So e_cdir.oEnd < e_cdir.oEnd, contradiction
      exact absurd (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans h3 h1) hwf_inter) h2) hwf_cdir) (Nat.lt_irrefl _)

/-- e_w_cle is ordered before e_r_cdir_down.
    With evictOrReadBetween, we have e_w_cle ordered before e_r_cle (from wObR).
    The downgrade chain from e_r's GLE produces e_r_cdir_down at e_w's cluster directory.
    The ordering e_w_cle < e_r_cdir_down follows from the protocol structure. -/
lemma evictOrReadBtn_diffCache_evictBetween_wObRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hencapPD : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
      hencapPD.existsRClusterDirDown.choose := by
  -- e_w_cle < e_r_cle (from evictOrReadBetween.wObR)
  have hpred := hevict_or_read_between.wObR
  -- Case-split on encapDirRelation
  have hrel : Behaviour.clusterDown.encapDirRelation hr_c_and_g_lin
      hencapPD.existsRClusterDirDown.choose :=
    hencapPD.existsRClusterDirDown.choose_spec.right.right.right
  match hrel with
  | .cleEncap h =>
    -- e_r_cle ≻ e_r_cdir_down → e_w_cle < e_r_cdir_down by Trans
    exact Trans.trans hpred h
  | .gcacheEncap _ _ =>
    sorry

/-- Construct the evictBetween.cond for the evictOrReadBetween case.
    Fields:
    - noWriteBtn: from evictOrReadBtn_diffCache_evictBetween_noWriteBtn
    - evictBtn: trivially satisfiable (pick e_w_cle, antecedent OrderedBetween → False)
    - wObRDown: from evictOrReadBtn_diffCache_evictBetween_wObRDown -/
lemma evictOrReadBtn_diffCache_evictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.clusterDown.encapDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_cdown : ¬ ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down)
  : WriteRead.evictBetween.cond cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := {
    noWriteBtn := evictOrReadBtn_diffCache_evictBetween_noWriteBtn hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent
      hencapPD hknow_dir_access
    evictBtn := ⟨hw_c_and_g_lin.hreq's_dir_access.choose,
      hw_c_and_g_lin.hreq's_dir_access.choose_spec.left,
      fun h => (Event.contradiction_of_reflexive_ordered_before n h.pred).elim⟩
    wObRDown := evictOrReadBtn_diffCache_evictBetween_wObRDown
      hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hencapPD
  }

/-- Coherent write at a different cache with evictOrReadBetween CLE relationship.
    Builds the wHasPermsAfter.case by constructing the downgrade chain from the read's GLE
    down to e_w's cache, then deciding between noEvictBetween and evictBetween. -/
lemma evictOrReadBtn_diffCache_coherent_wHasPermsAfter_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
      hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Step 1: Construct the global + cluster level downgrade chain (reuse general helper)
  have hencapPD := diffCache_coherent_encapProxyAndDir
    hw_c_and_g_lin hr_c_and_g_lin hw_in_b hw_cluster
  -- Step 2: noEvictBetween or evictBetween
  by_cases hcdown : ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  · -- noEvictBetween: downgrade reaches e_w's cache directly
    let hencapPDC : Behaviour.clusterDown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin :=
      { encapDir := hencapPD, existsRDownAtW := hcdown }
    exact .noEvictBetween {
      gdownEncapProxyAndDirAndCDown := hencapPDC
      noEvictBetween := evictOrReadBtn_diffCache_noEvictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hencapPDC
    }
  · -- evictBetween: cache was evicted, downgrade only reaches cluster directory level
    exact .evictBetween {
      encapProxyAndDir := hencapPD
      evictBetween := evictOrReadBtn_diffCache_evictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent
        hencapPD hknow_dir_access hcdown
    }

/-- diffCache case decision for evictOrReadBetween: coherent vs non-coherent write.
    - Coherent write → wHasPermsAfter
    - Non-coherent write → case split on dirAccessOfRequest:
      - encapDir → wNoPermsAfter
      - orderBeforeDir or orderAfterDir → wCleAfter -/
lemma evictOrReadBtn_diff_cache_choose_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hevict_or_read_between : CLE.WROrdering.evictOrReadBetween hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hw_in_b : e_w ∈ b) (hw_cluster : e_w.isClusterCache)
  (hw_not_down : ¬ e_w.down)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Extract rCleAfterWCle from evictOrReadBetween.wObR
  have hr_cle_after := evictOrReadBtn_diffCache_rCleAfterWCle hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter with notImmPred (evictOrReadBetween case)
    have hw_leaves_SW : b.reqLeavesStateAtLeast n e_w init SW :=
      coherent_write_leaves_at_least_SW hw_is_write hw_coherent hw_not_down hw_cluster.eAtCache
    exact .wHasPermsAfter hw_leaves_SW
      (.notImmPred (evictOrReadBtn_diffCache_coherent_wHasPermsAfter_case hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hevict_or_read_between hdiff_cache hw_coherent hknow_dir_access
        hw_in_b hw_cluster))
  · -- Non-coherent write: use rCleAfterWCle for the new constructors
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      exact .wNoPermsAfter hreq_missing_perms hw_nc hr_cle_after
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      exact .wCleAfter hr_cle_after
    | orderAfterDir _ _ _ _ =>
      exact .wCleAfter hr_cle_after
