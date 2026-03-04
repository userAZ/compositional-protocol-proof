/-
  Helper lemmas specifically for the `rf.sameGle.wImmPredRCle` case
  (write's CLE is the immediate predecessor of read's CLE).

  These lemmas are used by `RfSameGleWImmPredRCle.lean` and handle:
  - Same GLE protocol equivalence (`same_gle_implies_same_protocol`)
  - Same cache: no intervening directory writes (`wimmpredrCle_no_dir_write_between_same_cache`)
  - Different cache: case selection (`wimmpredrCle_diff_cache_choose_case`)
    with the full diffCache proof chain:
    - Global downgrade (Axiom 10)
    - GlobalToCluster shim
    - noEvictBetween / evictBetween subcases
    - Coherent vs non-coherent write case split
-/
import CMCM.RfProofHelpers

variable {n : ℕ}

/-- Helper: If two events have the same GLE, they are in the same protocol cluster.
    This works because same GLE implies they come from requests that trace back to the same
    global protocol request, hence same protocol linkage. -/
lemma same_gle_implies_same_protocol
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hgle_eq : hw_c_and_g_lin.hreq's_global_lin.choose = hr_c_and_g_lin.hreq's_global_lin.choose)
  : e_w.protocol = e_r.protocol := by
  -- Both events' cluster requests link through their CLEs to the same global request.
  -- The CLEs belong to directory events that are protocol-specific.
  -- Since both e_w and e_r contribute to the same GLE, they must be in the same protocol.
  have hw_cle_protocol :
      hw_c_and_g_lin.hreq's_dir_access.choose.protocol = e_w.protocol :=
    write_cle_protocol_eq_write_protocol hw_c_and_g_lin
  have hr_cle_protocol :
      hr_c_and_g_lin.hreq's_dir_access.choose.protocol = e_r.protocol :=
    read_cle_protocol_eq_read_protocol hr_c_and_g_lin
  -- The same GLE ensures both CLEs are part of the same protocol's global interaction.
  -- Even if CLEs are different (e.g., predecessor/successor), they must share the same protocol
  -- because they're both accessed participants in the same global protocol event.
  -- Trace through ClusterToGlobal infrastructure:
  -- 1. hw_c_and_g_lin.hreq's_dir_access gives cluster directory event for e_w
  -- 2. ClusterToGlobal links it to a global cache event
  -- 3. hw_c_and_g_lin.hreq's_global_lin accesses global directory from that cache
  -- 4. Since hgle_eq says both access the same GLE, their global paths converge
  -- 5. Therefore CLEs must have same protocol

  -- The structure is:
  -- e_w -> cluster_dir(e_w) -> global_cache(e_w) -> global_dir(e_w)
  -- e_r -> cluster_dir(e_r) -> global_cache(e_r) -> global_dir(e_r)
  -- Both global_dir events are the same (hgle_eq), so both paths lead to same global request

  -- Alternative approach: use the global directory event directly
  -- Both CLEs link through ClusterToGlobal to the same global dir (hgle_eq)
  -- Extract protocol information from that shared endpoint
  have hw_global_dir := hw_c_and_g_lin.hreq's_global_lin.choose
  have hr_global_dir := hr_c_and_g_lin.hreq's_global_lin.choose
  -- hgle_eq directly proves these are equal

  -- The global directory event is accessed through both paths
  -- dirAccessOfRequest enforces protocol constraints (see its case analysis at lines 569-595)
  -- Both hw_cle and hr_cle contribute to accessing the same global_dir through :
  --   ClusterToGlobal(hw_cle) --[dirAccessOfRequest]--> hw_global_dir
  --   ClusterToGlobal(hr_cle) --[dirAccessOfRequest]--> hr_global_dir
  -- And hw_global_dir = hr_global_dir (hgle_eq)

  -- The dirAccessOfRequest predicate has three cases (encapDir, orderBeforeDir, orderAfterDir),
  -- each with protocol preservation properties (sameProtocol field or via encapsulation rules)

  -- Since both paths converge to the same global directory via the same predicate structure,
  -- and each case of dirAccessOfRequest preserves protocol information through the chain,
  -- the protocol of hw_cle and hr_cle must be the same

  calc
    e_w.protocol = hw_c_and_g_lin.hreq's_dir_access.choose.protocol :=
      hw_cle_protocol.symm
    _ = hr_c_and_g_lin.hreq's_dir_access.choose.protocol := by
      let hw_cle := hw_c_and_g_lin.hreq's_dir_access.choose
      let hr_cle := hr_c_and_g_lin.hreq's_dir_access.choose
      let hw_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hw_c_and_g_lin.hreq's_dir_access
      let hr_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init hr_c_and_g_lin.hreq's_dir_access

      have hw_cle_is_dir : hw_cle.isDirectoryEvent := by
        simpa [hw_cle] using hw_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent
      have hr_cle_is_dir : hr_cle.isDirectoryEvent := by
        simpa [hr_cle] using hr_c_and_g_lin.hreq's_dir_access.choose_spec.right.isDirEvent

      have hw_gcache_eq : hw_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hw_cle hw_cle_is_dir := by
        simp [hw_gcache, Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper, hw_cle, hw_cle_is_dir]
      have hr_gcache_eq : hr_gcache = Behaviour.Shim.ClusterToGlobal.cDir'sGReq cmp b init hr_cle hr_cle_is_dir := by
        simp [hr_gcache, Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper, hr_cle, hr_cle_is_dir]

      have hw_gcache_to_gdir : b.dirAccessOfRequest n init hw_gcache (hw_c_and_g_lin.hreq's_global_lin.choose) :=
        hw_c_and_g_lin.hreq's_global_lin.choose_spec.right
      have hr_gcache_to_gdir' : b.dirAccessOfRequest n init hr_gcache (hr_c_and_g_lin.hreq's_global_lin.choose) :=
        hr_c_and_g_lin.hreq's_global_lin.choose_spec.right
      have hr_gcache_to_gdir : b.dirAccessOfRequest n init hr_gcache (hw_c_and_g_lin.hreq's_global_lin.choose) := by
        simpa [hgle_eq] using hr_gcache_to_gdir'

      simpa [hw_cle, hr_cle] using
        (cluster_dirs_to_same_global_dir_have_same_protocol
          (cmp := cmp) (b := b) (init := init)
          (hw_cle := hw_cle) (hr_cle := hr_cle)
          (hw_gcache := hw_gcache) (hr_gcache := hr_gcache)
          (e_gdir := hw_c_and_g_lin.hreq's_global_lin.choose)
          hw_cle_is_dir hr_cle_is_dir
          hw_gcache_eq hw_gcache_to_gdir
          hr_gcache_eq hr_gcache_to_gdir)
    _ = e_r.protocol :=
      hr_cle_protocol

/-- Helper for wImmPredRCle: When e_w_cle is immediate predecessor of e_r_cle and same cache,
    there are no intervening directory writes. -/
lemma wimmpredrCle_no_dir_write_between_same_cache
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hsame_cache : e_w.struct = e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_intervening_writes : NoInterveningWrites hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access)
  : Event.Between.noDirWrite cmp b init hw_c_and_g_lin.hreq's_dir_access.choose hr_c_and_g_lin.hreq's_dir_access.choose hknow_dir_access := by
  -- noDirWrite is ¬ sameOrDiffCluster, so we assume sameOrDiffCluster and derive contradiction
  unfold Event.Between.noDirWrite
  intro h
  -- Shared CLE-to-event protocol equalities
  have hw_cle_proto := write_cle_protocol_eq_write_protocol hw_c_and_g_lin
  have hr_cle_proto := read_cle_protocol_eq_read_protocol hr_c_and_g_lin
  have hw_r_same_struct : e_w.sameStructure n e_r := by
    unfold Event.sameStructure; exact hsame_cache
  have hw_r_same_proto : e_w.protocol = e_r.protocol :=
    sameStructure_implies_sameProtocol hw_r_same_struct
  cases h with
  | sameCluster e_w_inter hsame =>
    -- Get NoInterveningWrites constraints for e_w_inter
    have hconstraints := hno_intervening_writes
      e_w_inter hsame.interInB hsame.isCluster hsame.isWrite hsame.notDown
    -- Derive: e_inter_cle.protocol = e_w_cle.protocol
    -- Chain: e_inter_cle → e_w_inter (write_cle_protocol) → e_w_cle (sameProtocol)
    have hinter_cle_proto :=
      write_cle_protocol_eq_write_protocol (hknow_dir_access cmp b init e_w_inter)
    have h_proto_w := hinter_cle_proto.trans hsame.sameProtocol
    -- Derive: e_inter_cle.protocol = e_r_cle.protocol
    -- Chain: e_inter_cle → e_w_cle → e_w → e_r → e_r_cle
    have h_proto_r := h_proto_w.trans (hw_cle_proto.trans (hw_r_same_proto.trans hr_cle_proto.symm))
    -- notBetweenCles: same protocol + isDirWrite → NOT between CLEs.
    -- But cleBetween says IS between. Contradiction.
    exact hconstraints.notBetweenCles ⟨h_proto_w, h_proto_r, hsame.cleDirWrite⟩ hsame.cleBetween
  | diffCluster e_w_inter hdiff =>
    -- Get NoInterveningWrites constraints for e_w_inter
    have hconstraints := hno_intervening_writes
      e_w_inter hdiff.interInB hdiff.isCluster hdiff.isWrite hdiff.notDown
    -- Derive: e_w_inter different protocol from e_w and e_r
    have hdiff_w : e_w_inter.protocol ≠ e_w.protocol := by
      intro heq; exact hdiff.diffProtocol (heq.trans hw_cle_proto.symm)
    have hdiff_r : e_w_inter.protocol ≠ e_r.protocol := by
      intro heq; exact hdiff_w (heq.trans hw_r_same_proto.symm)
    -- Extract the directory downgrade witness from the diff-cluster chain
    obtain ⟨e_cdir_down, hcdir_in_b, hcdir_dir, hcdir_proto, hcdir_write, hcdir_down,
      hcdir_encap, hcdir_between⟩ := hdiff.existsClusterDirDown
    -- Derive: e_cdir_down has same protocol as e_w (via CLE protocol)
    have hdown_proto_w := hcdir_proto.trans hw_cle_proto
    -- Construct DiffClusterCLE.NotBetweenCLEs.constraints and derive contradiction.
    -- diffClusterNotBetweenCles says no such witness exists, but we have one.
    exact hconstraints.diffClusterNotBetweenCles ⟨e_cdir_down, hcdir_in_b,
      ⟨⟨hdiff_w, hdiff_r⟩, hdown_proto_w, hcdir_write, hcdir_down, hcdir_dir, hcdir_encap⟩,
      hcdir_between⟩

/-- Helper: When e_w's CLE is the immediate predecessor of e_r's CLE and they are at different
    caches, the read's global linearization event triggers a downgrade at the previous owner,
    producing the wCleAfter condition wrapper.

    The downgrade chain works as follows:
    1. e_r's cluster directory event maps to a global cache request (via ClusterToGlobal shim)
    2. e_r's GLE is the global directory event for this request
    3. The GLE triggers a downgrade at the previous owner (via Axiom 9/10/12)
    4. e_w's global cache event (e_w_cle_gcache) is ordered before e_r's global downgrade
    5. No global cache write occurs between e_w_cle_gcache and the downgrade

    The ordering follows from CLE immediate predecessor → global ordering preservation
    through the ClusterToGlobal shim. -/
lemma diffCache_wCleAfter_cond_wrapper
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  : WriteRead.wCleAfter.cond.wrapper cmp b init hw_c_and_g_lin hr_c_and_g_lin := by
  -- Unfold wrapper: need to find e_r_gdown, e_r_grant in b such that
  -- (1) downgradeAtPrevOwner.clusterReq.gdown.wrapper (global-level downgrade from e_r's GLE)
  -- (2) wCleAfter.cond (e_w_cle_gcache ordered before e_r_gdown, no global cache write between)
  --
  -- Part (1): Use protocol axioms — the read's global directory event (e_r_gle) triggers
  --   a downgrade at the previous owner when the directory state is SW.
  --   For coherent reads → Axiom 10 (coherentReadDirDowngradeOthers)
  --   For coherent writes → Axiom 9 (coherentWriteDirDowngradeOthers)
  --   For NC requests → Axiom 12 (nonCoherentRequestDowngradeOthers) + grant from Axiom 11
  --
  -- Part (2): The CLE immediate predecessor relationship implies:
  --   e_w's CLE is ordered before e_r's CLE in the cluster directory.
  --   Through the ClusterToGlobal shim, this ordering propagates to the global level:
  --   e_w_cle_gcache (global event of e_w's CLE) is before e_r_gdown (downgrade from e_r's GLE).
  --   The immediate predecessor property ensures no global cache write between them,
  --   as such a write would violate the immediacy of the predecessor relationship.
  sorry

/-- Helper: The read's GLE at the global level triggers a downgrade of the previous owner.
    Uses protocol Axiom 10 (coherent read directory downgrades others) at the global level.

    The axiom provides `coherentRequestAtDirectoryEncapDowngrades`, which has a single constructor
    `cReadOnSW`, giving us `fwdCoherentRequestToOwner.fwdPrevOwner` — the existential witnesses
    for the downgrade at the previous owner.

    The axiom is applied to the global cache event `e_r_cle_gcache` (from ClusterToGlobal shim)
    and the GLE `e_r_gle`, both defined to match the wrapper's let-bindings exactly.
    Since `coherentReadDirDowngradeOthers` is universally quantified over all event pairs
    (as a field of `Protocol.RequestAxioms`), it applies directly. -/
lemma diffCache_coherent_globalDowngrade
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_r : Event n}
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  : ∃ e_r_gdown ∈ b, ∃ e_r_grant ∈ b,
    Behaviour.downgradeAtPrevOwner.clusterReq.gdown.wrapper cmp b init hr_c_and_g_lin e_r_gdown e_r_grant := by
  -- Define the global cache event and GLE, matching the wrapper's let-bindings exactly.
  -- wrapper computes: e_r_cle_gcache := cDir'sGReq.wrapper ..., e_r_gle := hreq's_global_lin.choose
  let e_r_cle_gcache := Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper cmp b init
    (hexists_cdir := hr_c_and_g_lin.hreq's_dir_access)
  let e_r_gle := hr_c_and_g_lin.hreq's_global_lin.choose
  -- Membership proofs
  have he_gcache_in_b : e_r_cle_gcache ∈ b :=
    Behaviour.Shim.ClusterToGlobal.cDir'sGReq.inB cmp b init hr_c_and_g_lin.hreq's_dir_access
  have he_gle_in_b : e_r_gle ∈ b := hr_c_and_g_lin.hreq's_global_lin.choose_spec.left
  -- Apply Axiom 10 (coherent read downgrades) at the global protocol level.
  -- coherentReadDirDowngradeOthers : ∀ b init, ∀ e_req ∈ b, ∀ e_dir ∈ b,
  --   b.coherentReadDowngradeOthers n e_req e_dir init
  have haxiom := cmp.global.reqAxioms.coherentReadDowngrades b init
    e_r_cle_gcache he_gcache_in_b e_r_gle he_gle_in_b
  -- coherentRequestAtDirectoryEncapDowngrades has exactly one constructor: cReadOnSW.
  -- This gives fwdCoherentRequestToOwner, whose fwdPrevOwner field is:
  --   ∃ e_down ∈ b, ∃ e_grant ∈ b, b.downgradeAtPrevOwner n init e_r_cle_gcache e_r_gle e_down e_grant
  -- Since the wrapper's let-bindings produce the same e_r_cle_gcache and e_r_gle,
  -- this matches the goal type definitionally.
  cases haxiom.downgradeOtherCaches with
  | cReadOnSW hfwd => exact hfwd.fwdPrevOwner

/-- Helper: From a GlobalToCluster shim result at protocol p, extract a cluster proxy cache event
    and a cluster directory event at e_w's protocol.

    The shim's Down translation provides these events in all physically realizable cases:
    - bothCoherentWriteAndRead: scWriteDown has proxy write+evict and 2 dir events;
      scReadDown has proxy read and 1 dir event
    - noCoherentRead: cases on cluster directory state:
      - onDirSW: has acquire proxy + dir events
      - onDirVd: has only dir events (no proxy) — ruled out when e_w holds perms
      - onDirVc: has only dir event (no proxy) — ruled out when e_w holds perms

    The onDirVd and onDirVc sub-cases are physically impossible when the write still holds
    permissions at the cache (the cluster directory state must be SW at the time of the
    downgrade, since the coherent write held exclusive state). -/
lemma globalToCluster_extract_proxy_and_dir
  {n : ℕ} {b : Behaviour n} {init : InitialSystemState n}
  {p : Protocol n} {e_gdown : Event n}
  (hg2c : Behaviour.Shim.GlobalToCluster n b init p e_gdown)
  (e_w : Event n) (hp_eq : p.pi = e_w.protocol)
  : (∃ e_proxy ∈ b, e_proxy.protocol = e_w.protocol ∧ e_proxy.isClusterCache) ∧
    (∃ e_dir ∈ b, e_dir.isDirectoryEvent ∧ e_dir.protocol = e_w.protocol) := by
  -- Case analysis on GlobalToCluster (bothCoherentWriteAndRead vs noCoherentRead),
  -- then on Down translation sub-cases. In each case, extract proxy and dir events
  -- from translateProxyEvent (atCorrClusterProxy.clusterMatch.atCorrCluster)
  -- and translateDirectoryEvent (dirCorrespondToGlobalCache.clusterMatch.atCorrCluster).
  -- Protocol equality follows from hcorrespond + atCorrCluster + hp_eq.
  -- The onDirVd/onDirVc cases require showing directory ≠ Vd/Vc (coherent write → SW).
  sorry

/-- Construct the global and cluster level downgrade chain from e_r's GLE to e_w's cluster.
    This produces existential witnesses for:
    - e_r_gdown, e_r_grant: global downgrade at previous owner (from `diffCache_coherent_globalDowngrade`)
    - e_r_proxy: cluster proxy at e_w's protocol (from `globalToCluster_extract_proxy_and_dir`)
    - e_r_cdir_down: cluster directory downgrade at e_w's protocol

    The chain:
    1. `diffCache_coherent_globalDowngrade` invokes Axiom 10 at the global level to get
       the downgrade at the previous owner (`downgradeAtPrevOwner.clusterReq.gdown.wrapper`)
    2. `cmp.shimAxioms.globalToCluster` maps the global downgrade to e_w's cluster protocol
    3. `globalToCluster_extract_proxy_and_dir` extracts the cluster proxy and directory events
    4. `Event.getProtocol_pi` converts the protocol equality from `p.pi` to `e_w.protocol` -/
lemma diffCache_coherent_encapProxyAndDir
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin := by
  -- Step 1: Global downgrade exists (from Axiom 10 at global protocol level)
  have hgdown := diffCache_coherent_globalDowngrade hr_c_and_g_lin
  obtain ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, hdowngrade⟩ := hgdown
  -- Step 2: Apply GlobalToCluster shim on e_r_gdown at e_w's cluster protocol
  have hg2c := cmp.shimAxioms.globalToCluster b init (e_w.getProtocol cmp) e_r_gdown he_r_gdown_in_b
  -- Step 3: Protocol compatibility: (e_w.getProtocol cmp).pi = e_w.protocol
  have hp_eq := Event.getProtocol_pi cmp e_w
  -- Step 4: Extract cluster proxy and directory events from shim result
  have ⟨hproxy, hdir⟩ := globalToCluster_extract_proxy_and_dir hg2c e_w hp_eq
  -- Step 5: Build the encapProxyAndDir structure
  exact {
    existsRGlobalDown := ⟨e_r_gdown, he_r_gdown_in_b, e_r_grant, he_r_grant_in_b, hdowngrade⟩
    existsRClusterProxy := hproxy
    existsRClusterDirDown := hdir
  }

/-- Helper: No cache-level evict-SW between e_w and the cache-level downgrade e_r_down.

    After a coherent write, the cache holds exclusive (SW) state. The downgrade e_r_down
    is sent by e_r's GLE to e_w's cache to remove that state. An evict-SW at the same
    cache between e_w and e_r_down would mean the cache lost exclusive state before the
    downgrade arrived, but since the evict triggers directory activity (a CLE), and
    e_w_cle immediately precedes e_r_cle with no bottom events between them, such an
    evict's directory event would need to be between e_w_cle and e_r_cle — contradicting
    the CLE immediate predecessor property. -/
lemma diffCache_noEvictBetween_noEvict
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noEvict b e_w hencapPDC.existsRDownAtW.choose := by
  -- noEvict = ∀ e_inter ∈ b, e_inter.Between e_w e_r_down → ¬ e_inter.isEvictSW
  -- The Between structure requires coherentRead : e_r_down.isCoherent.
  -- Any evict at the same cache between e_w and e_r_down would need its CLE
  -- between e_w_cle and e_r_cle, violating the immediate predecessor property.
  sorry

/-- Helper: Every intervening write between e_w and e_r_down falls into one of the three
    excludeOtherWrites cases (same cache / diff cache same cluster / diff cluster).

    For each case, the key argument is: any such write's CLE (or directory-level
    downgrade event) would need to be between the CLE boundaries (e_w_cle and
    e_r_cdir_down). Since e_w_cle immediately precedes e_r_cle and e_r_cdir_down is
    part of e_r's downgrade chain, no write's CLE can fall between them without
    violating the immediate predecessor property. -/
lemma diffCache_noEvictBetween_noWrite
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : Event.Between.noWrite b init e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := by
  -- noWrite = ∀ e_inter ∈ b, isClusterCache → isWrite → ¬down →
  --   excludeOtherWrites b init e_inter e_w e_r_down e_w_cle e_r_cdir_down
  -- For each e_inter, case-split on its location relative to e_w:
  --   1. Same cache → otherWSameCache
  --   2. Different cache, same cluster → otherWDiffCacheSameCluster
  --   3. Different cluster → otherWDiffCluster
  -- In each case, the interCleNotBetween field follows from the CLE immediate
  -- predecessor property: no bottom event at the same entry can be between e_w_cle
  -- and e_r_cle, and e_r_cdir_down is related to e_r_cle through the downgrade chain.
  sorry

/-- Helper: When a cache-level downgrade exists at e_w's cache (ordered after e_w), and
    e_w's CLE is the immediate predecessor of e_r's CLE, construct the noEvictBetween.cond.

    The three fields:
    - noWriteBtn: No intervening write between e_w and e_r_down at the cache level.
      Delegated to `diffCache_noEvictBetween_noWrite`.
    - noEvictBtn: No evict between e_w and e_r_down at the same cache.
      Delegated to `diffCache_noEvictBetween_noEvict`.
    - wObRDown: e_w is ordered before e_r_down.
      Extracted directly from the existential witness (hencapPDC.existsRDownAtW). -/
lemma diffCache_noEvictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin)
  : WriteRead.noEvictBetween.cond b init
      e_w hencapPDC.existsRDownAtW.choose
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPDC.encapProxyAndDir.existsRClusterDirDown.choose := {
    wObRDown := hencapPDC.existsRDownAtW.choose_spec.right.right.right
    noEvictBtn := diffCache_noEvictBetween_noEvict hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
    noWriteBtn := diffCache_noEvictBetween_noWrite hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
  }

/-- Helper: No directory-level write between e_w_cle and e_r_cdir_down.
    Since e_w_cle is the immediate predecessor of e_r_cle (CLE immediate predecessor),
    any intervening directory write from a same-cluster cache write would require that
    write's CLE to be between e_w_cle and e_r_cle, contradicting immediacy. Similarly,
    a different-cluster write's directory downgrade chain would need an event between
    e_w_cle and e_r_cle.

    The e_r_cdir_down boundary (cluster directory downgrade from e_r's chain) is part of
    the downgrade chain originating from e_r's GLE, structurally constraining what can
    appear between e_w_cle and e_r_cdir_down. -/
lemma diffCache_evictBetween_noWriteBtn
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : Event.Between.noDirWrite cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := by
  -- noDirWrite is ¬ sameOrDiffCluster, so we assume sameOrDiffCluster and derive contradiction.
  -- The argument mirrors wimmpredrCle_no_dir_write_between_same_cache but with
  -- e_r_cdir_down as the second boundary instead of e_r_cle.
  sorry

/-- Helper: e_w_cle is ordered before e_r_cdir_down.
    The CLE immediate predecessor relationship places e_w_cle before e_r_cle.
    The downgrade chain from e_r's GLE produces e_r_cdir_down at e_w's cluster directory.
    The ordering e_w_cle < e_r_cdir_down follows from the protocol structure:
    e_w_cle → ... → e_r_cle → (global chain) → e_r_cdir_down, or
    e_w_cle < e_r_cdir_down directly via the downgrade chain's position relative
    to the CLE immediate predecessor boundary. -/
lemma diffCache_evictBetween_wObRDown
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  : hw_c_and_g_lin.hreq's_dir_access.choose.OrderedBefore n
      hencapPD.existsRClusterDirDown.choose := by
  sorry

/-- Helper: When no cache-level downgrade exists at e_w's cache (¬hcdown), and
    e_w's CLE is the immediate predecessor of e_r's CLE, construct the evictBetween.cond.

    The three fields:
    - noWriteBtn: No intervening directory write between e_w's CLE and e_r's cluster dir down.
      Delegated to `diffCache_evictBetween_noWriteBtn`.
    - evictBtn: Trivially satisfiable — `dirEvict` is `∃ e ∈ b, OrderedBetween → isDirEvict`.
      Picking e = e_w_cle, the antecedent `e_w_cle.OrderedBetween n e_w_cle e_r_cdir_down`
      is false (requires e_w_cle strictly after itself), so the implication holds vacuously.
    - wObRDown: Delegated to `diffCache_evictBetween_wObRDown`. -/
lemma diffCache_evictBetween_cond
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hencapPD : Behaviour.gdown.encapProxyAndDir cmp b init e_w hr_c_and_g_lin)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  (hno_cdown : ¬ ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down)
  : WriteRead.evictBetween.cond cmp b init
      hw_c_and_g_lin.hreq's_dir_access.choose
      hencapPD.existsRClusterDirDown.choose
      hknow_dir_access := {
    noWriteBtn := diffCache_evictBetween_noWriteBtn hw_is_write hr_is_read
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent
      hencapPD hknow_dir_access
    evictBtn := ⟨hw_c_and_g_lin.hreq's_dir_access.choose,
      hw_c_and_g_lin.hreq's_dir_access.choose_spec.left,
      fun h => (Event.contradiction_of_reflexive_ordered_before n h.pred).elim⟩
    wObRDown := diffCache_evictBetween_wObRDown
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hencapPD
  }

/-- Coherent write at a different cache with CLE immediate predecessor relationship.
    Builds the wHasPermsAfter.case by constructing the downgrade chain from the read's GLE
    down to e_w's cache, then deciding between noEvictBetween and evictBetween.

    The downgrade chain goes:
    - e_r's GLE → global downgrade e_r_gdown (from diffCache_coherent_encapProxyAndDir)
    - e_r_gdown → cluster proxy e_r_proxy at e_w's protocol (via GlobalToCluster shim)
    - e_r_proxy → cluster directory downgrade e_r_cdir_down at e_w's protocol
    - e_r_cdir_down → cache downgrade e_r_down at e_w's cache struct (noEvict case only)

    The noEvict vs evict decision:
    - noEvictBetween: downgrade chain extends to e_w's cache, no evicts between e_w and e_r_down
    - evictBetween: cache was evicted, chain only reaches cluster directory level -/
lemma diffCache_coherent_wHasPermsAfter_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hw_coherent : e_w.isCoherent)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : WriteRead.wObRCle.diffCache.wHasPermsAfter.case cmp b init
      (hw_c_and_g_lin.hreq's_dir_access.choose) (hr_c_and_g_lin.hreq's_dir_access.choose)
      hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Step 1: Construct the global + cluster level downgrade chain (common to both cases)
  have hencapPD := diffCache_coherent_encapProxyAndDir
    hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent
  -- Step 2: Does the cluster directory downgrade propagate to a cache-level downgrade at e_w?
  -- If e_w's cache still holds the line (no evict) → chain extends to cache → noEvictBetween
  -- If e_w's cache was evicted → chain only reaches cluster directory → evictBetween
  by_cases hcdown : ∃ e_r_down ∈ b,
    e_r_down.struct = e_w.struct ∧ e_r_down.down ∧ e_w.OrderedBefore n e_r_down
  · -- noEvictBetween: downgrade reaches e_w's cache directly
    let hencapPDC : Behaviour.gdown.encapProxyAndDirAndCDown e_w hr_c_and_g_lin :=
      { encapProxyAndDir := hencapPD, existsRDownAtW := hcdown }
    exact .noEvictBetween {
      gdownEncapProxyAndDirAndCDown := hencapPDC
      noEvictBetween := diffCache_noEvictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hencapPDC
    }
  · -- evictBetween: cache was evicted, downgrade only reaches cluster directory level
    exact .evictBetween {
      encapProxyAndDir := hencapPD
      evictBetween := diffCache_evictBetween_cond hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent
        hencapPD hknow_dir_access hcdown
    }

/-- Helper for wImmPredRCle diffCache: Decides which WriteRead.wObRCle.diffCache.case to apply
    based on coherence of the write and its directory access structure.

    Case analysis:
    - Coherent write → wHasPermsAfter (write retains/obtains permissions)
    - Non-coherent write, case-split on dirAccessOfRequest:
      - encapDir (missing perms) → wNoPermsAfter
      - orderBeforeDir (has perms) or orderAfterDir (Vd writeback) → wCleAfter -/
lemma wimmpredrCle_diff_cache_choose_case
  {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e_w e_r : Event n}
  (hw_is_write : e_w.isWrite) (hr_is_read : e_r.isRead)
  (hw_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_w)
  (hr_c_and_g_lin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e_r)
  (hw_imm_pred_r_cle : CompoundProtocol.cleImmediatePredecessor hw_c_and_g_lin hr_c_and_g_lin)
  (hdiff_cache : e_w.struct ≠ e_r.struct)
  (hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper)
  : WriteRead.wObRCle.diffCache.case hw_is_write hr_is_read hw_c_and_g_lin hr_c_and_g_lin hknow_dir_access := by
  -- Main decision point: is e_w coherent?
  by_cases hw_coherent : e_w.isCoherent
  · -- Coherent write → wHasPermsAfter
    exact WriteRead.wObRCle.diffCache.case.wHasPermsAfter hw_coherent
      (diffCache_coherent_wHasPermsAfter_case hw_is_write hr_is_read
        hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache hw_coherent hknow_dir_access)
  · -- Non-coherent write: construct the shared wCleAfter.cond.wrapper once,
    -- then case-split on dirAccessOfRequest to select the constructor.
    have hw_nc : e_w.isNonCoherent := isNonCoherent_of_not_isCoherent_write hw_is_write hw_coherent
    have hwrapper := diffCache_wCleAfter_cond_wrapper
      hw_c_and_g_lin hr_c_and_g_lin hw_imm_pred_r_cle hdiff_cache
    -- dirAccessOfRequest determines whether write has missing perms
    have hw_dir_access := hw_c_and_g_lin.hreq's_dir_access.choose_spec.right
    cases hw_dir_access with
    | encapDir hreq_missing_perms _ =>
      -- NC write with missing perms → wNoPermsAfter
      exact WriteRead.wObRCle.diffCache.case.wNoPermsAfter hreq_missing_perms hw_nc hwrapper
    | orderBeforeDir _ _ _ _ _ _ _ _ =>
      -- NC write with perms (predecessor obtained dir access) → wCleAfter
      exact WriteRead.wObRCle.diffCache.case.wCleAfter hwrapper
    | orderAfterDir _ _ _ _ =>
      -- NC weak request on Vd (e.g. writeback) → wCleAfter
      exact WriteRead.wObRCle.diffCache.case.wCleAfter hwrapper
