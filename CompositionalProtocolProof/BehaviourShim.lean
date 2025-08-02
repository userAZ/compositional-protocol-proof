import CompositionalProtocolProof.BehaviourRelationProofs
import CompositionalProtocolProof.Protocol

variable (n : Nat)

--------------- At Pg. 35 of Doc -------------------

def Event.reqAtGlobalCacheCid (e_greq : Event n) (globalCid : Fin 2) : Prop := match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => fin_2 = globalCid
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

def Event.reqAtCorrespondingGCacheOfCDir (e_dir e_greq : Event n) : Prop :=
  match e_dir with
  | .directoryEvent _ =>
    match e_dir.protocol with
    | .cluster1 => e_greq.reqAtGlobalCacheCid n 0
    | .cluster2 => e_greq.reqAtGlobalCacheCid n 1
    | .global => False
  | .cacheEvent _ => False

structure Event.isGlobalCache (e_greq : Event n) : Prop where
  reqAtCache : e_greq.isCacheEvent
  notAtGProxy : e_greq.reqAtGlobalCache
  reqGlobal : e_greq.protocol = .global

structure Event.isClusterDir (e_dir : Event n) : Prop where
  dirAtDir : e_dir.isDirectoryEvent
  dirCluster : e_dir.protocol = .cluster1 ∨ e_dir.protocol = .cluster2

/-- Def 2.43: Constraints of the Global Cache Event corresponding to a Cluster Directory Event. -/
structure Event.globalCacheEventOfClusterDir (e_greq e_dir : Event n) where
  reqGlobalCache : e_greq.isGlobalCache
  dirCluster : e_dir.isClusterDir
  sameAddr : e_dir.addr = e_greq.addr
  gReq : e_dir.reqAtCorrespondingGCacheOfCDir n e_greq -- Global Cache Request corresponds to e_dir's cluster
  matchingOp : e_greq.req = ⟨⟨e_dir.req.val.rw, true, .SC⟩, by simp[Request.IsValid']⟩
  notDowngrade : ¬ e_greq.down

structure Event.clusterDirEncapCorrespondingGlobalCache (b : Behaviour n) (e_dir e_greq : Event n) : Prop where
  encapGlobalCache : e_dir.Encapsulates n e_greq
  gReqOfCDir : e_greq.globalCacheEventOfClusterDir n e_dir
  onlyGlobalReq : ∀ e_gcache ∈ b, e_dir.reqAtCorrespondingGCacheOfCDir n e_gcache →
    e_gcache.isGlobalCache → e_dir.Encapsulates n e_gcache → e_gcache = e_greq

-- state the previous state of the corresponding global cache does not have sufficient state for a directory access.

/-- An Global Cache Event `e_gcache` corresponding to a Directory Event `e_cdir` ends before `e_cdir` in a Behaviour `b`. -/
structure Behaviour.globalCacheFinishesBeforeNotEncapClusterDirectory (b : Behaviour n) (e_gcache e_cdir : Event n) where
  finBefore : b.finishesBeforeNotEncap n e_gcache e_cdir
  gCacheOfCDir : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e_gcache

/-- There's an intermediate event `e_inter` that finishes before the successor `e_succ`, and
predecessor `e_pred` finishes before `e_inter`, where `e_pred` and `e_inter` are at the same Entry. -/
structure Event.intermediateFinishesBeforeNotEncapOfSameEntry (e_inter e_pred e_succ : Event n) : Prop where
  noInter : e_inter.intermediateFinishesBeforeOfSameEntry n e_pred e_succ
  noEncap : ¬ e_succ.Encapsulates n e_inter

/-- There is _no_ intermediate event `e_inter` that finishes before the successor `e_succ`, and
predecessor `e_pred` finishes before `e_inter` in the same entry. Note that `e_pred` is at a different `cid`
than `e_succ` in the same Protocol. -/
def Behaviour.noIntermediateFinishesBeforeNotEncapOfSameEntry (b : Behaviour n) (e_pred e_succ : Event n) : Prop :=
  ∀ e_inter ∈ b, ¬ e_inter.intermediateFinishesBeforeNotEncapOfSameEntry n e_pred e_succ

/-- There is no event `e_inter` that _immediately_ finishes before the successor `e_succ` -/
structure Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncap (b : Behaviour n) (e_pred e_succ : Event n) where
  finishBefore : Behaviour.globalCacheFinishesBeforeNotEncapClusterDirectory n b e_pred e_succ
  noIntermediate : b.noIntermediateFinishesBeforeNotEncapOfSameEntry n e_pred e_succ

/-- Latest (that isn't encapsulated by the Cluster Directory Event) Corresponding Global Cache Event of a Cluster Directory Event. -/
def Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncapEvents : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b | b.immediateFinishesBeforeAtGlobalCacheNotEncap n e_pred e_succ}

/- Prove if needed -/
lemma Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncapEvents_is_subsingleton (b : Behaviour n) (e_succ : Event n)
  : (b.immediateFinishesBeforeAtGlobalCacheNotEncapEvents n e_succ).Subsingleton := by
  sorry

def Event.globalCidCorrespondingToClusterDir (e_dir : Event n) : CacheId n :=
  match e_dir.protocol with
  | .cluster1 => CacheId.cache (ProtocolCacheInstance.globalP 0)
  | .cluster2 => CacheId.cache (ProtocolCacheInstance.globalP 1)
  | .global => panic! "Error: The Global Directory does not have a corresponding cache."

/-- Assumption: The set of events from projecting the events at `cid` is singleton. -/
noncomputable def Behaviour.stateOfSubsingletonEventSet
  (b : Behaviour n) (init : InitialSystemState n) (struct : Struct n) (s : Set (Event n)) : EntryState n :=
  b.eventToEntryState n init s.toOption struct

noncomputable def Behaviour.globalCacheStateOfDirectoryEvent (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : EntryState n :=
  let global_cache_cid := Struct.cache (e_dir.globalCidCorrespondingToClusterDir n)
  let global_event_imm_finish_before_dir := b.immediateFinishesBeforeAtGlobalCacheNotEncapEvents n e_dir
  b.stateOfSubsingletonEventSet n init global_cache_cid global_event_imm_finish_before_dir

def Behaviour.clusterDirNoPermsInGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop :=
  -- clusterDir : e_dir.isClusterDir
  ¬ e_dir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_dir).state

def Behaviour.clusterDirHasPermsInGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : Prop :=
  -- clusterDir : e_dir.isClusterDir
  e_dir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_dir).state

lemma Behaviour.immediateFinishesBeforeAtGlobalCacheNotEncapEvents_is_singleton (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n)
  -- [TODO] state that hinit_i : all initial states are in I.
  (hinit_i : sorry) (hcdir_has_perms : e_dir.req.MRS ≤ (b.globalCacheStateOfDirectoryEvent n init e_dir).state )
  : (b.immediateFinishesBeforeAtGlobalCacheNotEncapEvents n e_dir).Subsingleton := by
  sorry

def Behaviour.existsGlobalCacheAccessOfDirEvent (b : Behaviour n) (e_dir : Event n) : Prop :=
  ∃ e_greq ∈ b, Event.clusterDirEncapCorrespondingGlobalCache n b e_dir e_greq

def Event.clusterDirNotEncapCorrespondingGlobalCache (b : Behaviour n) (e_dir : Event n) : Prop :=
  ∀ e_gcache ∈ b, e_dir.reqAtCorrespondingGCacheOfCDir n e_gcache →
    e_gcache.isGlobalCache → ¬ e_dir.Encapsulates n e_gcache

/-- (Shim) Axiom 15: Cluster Directory Events are translated to Request Events at the corresponding Cache in the Global Protocol. -/
inductive Behaviour.Shim.ClusterToGlobal (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n)
| encapGlobalCache (no_global_cache_perms : b.clusterDirNoPermsInGlobalCache n init e_dir)
  (request_global_cache : b.existsGlobalCacheAccessOfDirEvent n e_dir)
  : Behaviour.Shim.ClusterToGlobal b init e_dir
| noGlobalCache (has_global_cache_perms : b.clusterDirHasPermsInGlobalCache n init e_dir)
  (no_global_cache_request : e_dir.clusterDirNotEncapCorrespondingGlobalCache n b)
  : Behaviour.Shim.ClusterToGlobal b init e_dir

/- For Stating the Global Cache State a Directory Event has corresponding permissions of. -/
structure Behaviour.globalCacheFinishesBeforeClusterDirectory (b : Behaviour n) (e_gcache e_cdir : Event n) where
  finBefore : b.finishesBefore n e_gcache e_cdir
  gCacheOfCDir : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e_gcache

/-- There is no event `e_inter` that _immediately_ finishes before the successor `e_succ` -/
structure Behaviour.immediateFinishesBeforeAtGlobalCache (b : Behaviour n) (e_pred e_succ : Event n) where
  finishBefore : Behaviour.globalCacheFinishesBeforeClusterDirectory n b e_pred e_succ
  noIntermediate : b.noIntermediateFinishesBeforeOfSameEntry n e_pred e_succ

/-- Latest Corresponding Global Cache Event of a Cluster Directory Event. -/
def Behaviour.immediateFinishesBeforeAtGlobalCacheEvents : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b | b.immediateFinishesBeforeAtGlobalCache n e_pred e_succ}

/- Prove if needed -/
lemma Behaviour.immediateFinishesBeforeAtGlobalCacheEvents_is_subsingleton (b : Behaviour n) (e_succ : Event n)
  : (b.immediateFinishesBeforeAtGlobalCacheEvents n e_succ).Subsingleton := by
  sorry

structure Behaviour.clusterDirectoryFinishesBeforeGlobalCache (b : Behaviour n) (e_cdir e_gcache : Event n) where
  finBefore : b.finishesBefore n e_cdir e_gcache
  gCacheOfCDir : Event.reqAtCorrespondingGCacheOfCDir n e_cdir e_gcache

/-- There is no event `e_inter` that _immediately_ finishes before the successor `e_succ` -/
structure Behaviour.immediateFinishesBeforeAtClusterDirectory (b : Behaviour n) (e_pred e_succ : Event n) where
  finishBefore : Behaviour.clusterDirectoryFinishesBeforeGlobalCache n b e_pred e_succ
  noIntermediate : b.noIntermediateFinishesBeforeOfSameEntry n e_pred e_succ

/-- The Latest Cluster Directory Event corresponding to a Global Cache Event -/
def Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b | b.immediateFinishesBeforeAtClusterDirectory n e_pred e_succ}

/- Prove if needed -/
lemma Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_subsingleton (b : Behaviour n) (e_succ : Event n)
  : (b.immediateFinishesBeforeAtClusterDirectoryEvents n e_succ).Subsingleton := by
  sorry

lemma Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_same_struct {b : Behaviour n} {e_cdir e e_succ : Event n}
  (hcdir : immediateFinishesBeforeAtClusterDirectory n b e_cdir e_succ)
  (he : immediateFinishesBeforeAtClusterDirectory n b e e_succ)
  : Event.struct n e = Event.struct n e_cdir := by
  have hcdir_at_corresponding_cdir := hcdir.finishBefore.gCacheOfCDir
  have he_at_corresponding_cdir := he.finishBefore.gCacheOfCDir
  simp[Event.reqAtCorrespondingGCacheOfCDir] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
  match e_cdir, e with
  | .directoryEvent de_cdir, .directoryEvent de_e =>
    simp[Event.protocol] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
    match hcdir_pi : de_cdir.pInst, he_pi : de_e.pInst with
    | .cluster1, .cluster1
    | .cluster2, .cluster2 =>
      simp[hcdir_pi, he_pi] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
      simp[Event.struct, hcdir_pi, he_pi]
    | .global, .global | .cluster1, .global | .cluster2, .global | .global, .cluster1 | .global, .cluster2
      => simp[hcdir_pi, he_pi] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
    | .cluster1, .cluster2 | .cluster2, .cluster1 =>
      simp[hcdir_pi, he_pi, Event.reqAtGlobalCacheCid] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
      -- Contradiction, `e_succ` can't be at Global Cache 0 and 1 at the same time.
      match e_succ with
      | .cacheEvent ce_succ =>
        simp[] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
        match hsucc_cid : ce_succ.cid with
        | .cache pci =>
          simp[hsucc_cid] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
          match hsucc_pci : pci with
          | .globalP fin2 =>
            simp[] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
            absurd hcdir_at_corresponding_cdir
            simp[he_at_corresponding_cdir]
          | .cluster1 _ | .cluster2 _ => simp[] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
        | .proxy _ => simp[hsucc_cid] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
      | .directoryEvent _ => simp[] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
  | .cacheEvent _, .cacheEvent _ | .directoryEvent _, .cacheEvent _ | .cacheEvent _, .directoryEvent _
    => simp at hcdir_at_corresponding_cdir he_at_corresponding_cdir

-- BEGIN: State before a global downgrade is translated satisfies Compound SWMR:

/-- There is no event `e_inter` that _immediately_ finishes before the successor `e_succ` -/
structure Behaviour.immediateFinishesBeforeAtClusterDirectoryNotEncap (b : Behaviour n) (e_pred e_succ : Event n) where
  finishBefore : Behaviour.clusterDirectoryFinishesBeforeGlobalCache n b e_pred e_succ
  notEncap : ¬ e_succ.Encapsulates n e_pred
  noIntermediate : b.noIntermediateFinishesBeforeOfSameEntryNotEncap n e_pred e_succ

/-- The Latest Cluster Directory Event corresponding to a Global Cache Event -/
def Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap : Behaviour n → Event n → Set (Event n)
| b, e_succ => {e_pred ∈ b | b.immediateFinishesBeforeAtClusterDirectoryNotEncap n e_pred e_succ}
-- [NOTE] prove the above is subsingleton?

lemma Behaviour.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap_is_subsingleton (b : Behaviour n) (e_succ : Event n)
  : (b.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n e_succ).Subsingleton := by
  sorry

-- END: State before a global downgrade is translated satisfies Compound SWMR:

lemma Behaviour.contradiction_of_two_directory_events_immediate_finishes_before_successor_event
  {b : Behaviour n} {de_cdir de : DirectoryEvent n} {e_succ : Event n}
  (hcdir_ob_de : DirectoryEvent.OrderedBefore n de_cdir de)
  (he_in_b :Event.directoryEvent de ∈ b)
  (hcdir : immediateFinishesBeforeAtClusterDirectory n b (Event.directoryEvent de_cdir) e_succ)
  (he :immediateFinishesBeforeAtClusterDirectory n b (Event.directoryEvent de) e_succ)
  : False := by
  have he_not_intermediate := hcdir.noIntermediate (Event.directoryEvent de) he_in_b
  apply he_not_intermediate
  constructor
  . case sameCidInterPred =>
    apply Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_same_struct
    . case hcdir => exact hcdir
    . case he => exact he
  . case sameAddr =>
    have hcdir_same_addr_succ := hcdir.finishBefore.finBefore.sameAddr
    have he_same_addr_succ := he.finishBefore.finBefore.sameAddr
    simp[Event.sameAddr] at hcdir_same_addr_succ he_same_addr_succ
    simp[hcdir_same_addr_succ, he_same_addr_succ]
  . case interPred =>
    simp[Event.finishesBefore, Event.oEnd,]
    calc de_cdir.oEnd < de.oStart := hcdir_ob_de
      _ < de.oEnd := de.oWellFormed
  . case interSucc => exact he.finishBefore.finBefore.endBefore

lemma Behaviour.contradiction_of_two_ordered_directory_events_immediate_finishes_before_successor_event
  {b : Behaviour n} {de_cdir de : DirectoryEvent n} {e_succ : Event n}
  (hordered : DirectoryEvent.OrderedBefore n de de_cdir ∨ DirectoryEvent.OrderedBefore n de_cdir de)
  (he_in_b :Event.directoryEvent de ∈ b)
  (hcdir : immediateFinishesBeforeAtClusterDirectory n b (Event.directoryEvent de_cdir) e_succ)
  (he :immediateFinishesBeforeAtClusterDirectory n b (Event.directoryEvent de) e_succ)
  : False := by
  cases hordered
  . case inl hde_ob_cdir =>
    apply Behaviour.contradiction_of_two_directory_events_immediate_finishes_before_successor_event
    . case hcdir_ob_de => exact hde_ob_cdir
    . case he_in_b => exact hcdir.finishBefore.finBefore.predInB
    . case hcdir => exact he
    . case he => exact hcdir
  . case inr hcdir_ob_de =>
    apply Behaviour.contradiction_of_two_directory_events_immediate_finishes_before_successor_event
    . case hcdir_ob_de => exact hcdir_ob_de
    . case he_in_b => exact he_in_b
    . case hcdir => exact hcdir
    . case he => exact he


/- Will need this lemma later.-/
lemma Behaviour.immediateFinishesBeforeAtClusterDirectoryEvents_is_cdir_singleton {e_cdir} (b : Behaviour n)
  (e_succ : Event n) (h : b.immediateFinishesBeforeAtClusterDirectory n e_cdir e_succ)
  : (b.immediateFinishesBeforeAtClusterDirectoryEvents n e_succ) = {e_cdir} := by
  simp[immediateFinishesBeforeAtClusterDirectoryEvents]
  apply Set.ext
  case h =>
  intro e
  apply Iff.intro
  . case mp =>
    intro he_in_finish_befores
    simp_all
    obtain ⟨he_in_b,he_imm_fin_before⟩ := he_in_finish_befores
    case intro =>
    by_contra he_ne_cdir
    -- Show for either case of `e.OrderedBefore e_cdir` or `e_cdir.OrderedBefore e`, there's a Contradiction:
    have hcdir_at_corresponding_cdir := h.finishBefore.gCacheOfCDir
    have he_at_corresponding_cdir := he_imm_fin_before.finishBefore.gCacheOfCDir
    simp[Event.reqAtCorrespondingGCacheOfCDir] at hcdir_at_corresponding_cdir he_at_corresponding_cdir
    match e, e_cdir with
    | .directoryEvent de, .directoryEvent de_cdir =>
      -- Contradiction; Both `e` and `e_cdir` can't both be immediate finish-before `e_succ` events.
      have hordered := b.orderedAtEntry.dir_ordered de de_cdir |>.ordered
      simp[DirectoryEvent.Ordered] at hordered
      apply Behaviour.contradiction_of_two_ordered_directory_events_immediate_finishes_before_successor_event
      . case hordered => exact hordered
      . case he_in_b => exact he_in_b
      . case hcdir => exact h
      . case he => exact he_imm_fin_before
    | .cacheEvent _, .cacheEvent _ | .directoryEvent _, .cacheEvent _ | .cacheEvent _, .directoryEvent _
      => simp at hcdir_at_corresponding_cdir he_at_corresponding_cdir
  . case mpr =>
    intro he_in_cdir
    simp[]
    apply And.intro
    . case left =>
      simp at he_in_cdir; rw[he_in_cdir]
      exact h.finishBefore.finBefore.predInB
    . case right =>
      simp at he_in_cdir; rw[he_in_cdir]
      exact h

def Event.clusterDirProtocolCorrespondingToGlobalCache (e_gcache : Event n) : ProtocolInstance :=
  match e_gcache with
  | .cacheEvent ce => match ce.cid with
    | .cache pci => match pci with
      | .globalP fin2 => match fin2 with
        | 0 => .cluster1
        | 1 => .cluster2
      | .cluster1 _
      | .cluster2 _ => panic! "Error: Expected `e_gcache` to be a Global _Cache_ Event, not a _Cluster_ Cache Event."
    | .proxy _ => panic! "Error: Expected `e_gcache` to be a Global _Cache_ Event, not a _Proxy_ Cache Event."
  | .directoryEvent _ => panic! "Error: Expected `e_gcache` to be a Global _Cache_ Event, not a Directory Event."

noncomputable def Behaviour.globalCacheStateOfDirEventState (b : Behaviour n) (init : InitialSystemState n) (e_dir : Event n) : EntryState n :=
  let global_cache_cid := Struct.cache (e_dir.globalCidCorrespondingToClusterDir n)
  let global_event_imm_finish_before_dir := (b.immediateFinishesBeforeAtGlobalCacheEvents n e_dir)
  b.stateOfSubsingletonEventSet n init global_cache_cid global_event_imm_finish_before_dir

noncomputable def Behaviour.latestDirectoryStateOfGlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : EntryState n :=
  let cluster_dir_struct := Struct.directory (e_gcache.clusterDirProtocolCorrespondingToGlobalCache n)
  let cluster_dir_imm_finish_before_global := b.immediateFinishesBeforeAtClusterDirectoryEvents n e_gcache
  b.stateOfSubsingletonEventSet n init cluster_dir_struct cluster_dir_imm_finish_before_global

/-- The state at the Cluster Directory before a corresopnding Global Cache Event `e_gcache`.-/
noncomputable def Behaviour.latestDirectoryState.Before.GlobalCache (b : Behaviour n) (init : InitialSystemState n) (e_gcache : Event n) : EntryState n :=
  let cluster_dir_struct := Struct.directory (e_gcache.clusterDirProtocolCorrespondingToGlobalCache n)
  let cluster_dir_imm_finish_before_global_not_encap := b.immediateFinishesBeforeAtClusterDirectoryEventsNotEncap n e_gcache
  b.stateOfSubsingletonEventSet n init cluster_dir_struct cluster_dir_imm_finish_before_global_not_encap

def Event.globalCacheCorrespondingCluster (e_greq e_cluster : Event n) : Prop := match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => match fin_2 with
        | 0 => e_cluster.protocol = .cluster1
        | 1 => e_cluster.protocol = .cluster2
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

/-- Def: State that an Event `e` is in the corresponding Cluster to a Global Cache Event `e_gReq` -/
def Event.correspondingClusterOfGlobalCache {α : Type} (e_greq : Event n) (e : α) (protocol : α → ProtocolInstance) : Prop :=
  match e_greq with
  | .cacheEvent ce => match ce.cid with
    | .cache p_cache_inst => match p_cache_inst with
      | .globalP fin_2 => match fin_2 with
        | 0 => protocol e = .cluster1
        | 1 => protocol e = .cluster2
      | .cluster1 _ => False
      | .cluster2 _ => False
    | .proxy _ => False
  | .directoryEvent _ => False

def Protocol.hasCoherentWrite (p : Protocol n) : Prop := ∃ req ∈ p.requests, req.isCoherentWrite
def Protocol.hasCoherentRead (p : Protocol n) : Prop := ∃ req ∈ p.requests, req.isCoherentRead

def Protocol.hasCoherentWriteAndRead (p : Protocol n) : Prop := p.hasCoherentWrite ∧ p.hasCoherentRead

def Protocol.noCoherentWrite (p : Protocol n) : Prop := ∀ req ∈ p.requests, ¬ req.isCoherentWrite
def Protocol.noCoherentRead (p : Protocol n) : Prop := ∀ req ∈ p.requests, ¬ req.isCoherentRead

def Protocol.noCoherentWriteOrRead (p : Protocol n) : Prop := p.noCoherentWrite ∧ p.noCoherentRead

structure Event.isGlobalDowngrade (e : Event n) : Prop where
  isGlobal : e.isGlobalCache
  isDown : e.down

structure Event.isSCWriteGlobalDowngrade (e : Event n) : Prop where
  isGlobalDown : e.isGlobalCache
  isSCWrite : e.isSCWrite

structure Event.isSCReadGlobalDowngrade (e : Event n) : Prop where
  isGlobalDown : e.isGlobalCache
  isSCRead : e.isSCRead

/-- A directory event `e` is made on state `s` -/
def Behaviour.dirEventMadeOn (b : Behaviour n) (init : InitialSystemState n) (e : Event n) (s : State) : Prop :=
  (b.directoryStateMadeOn n init e).toState = s

def Event.atProxy (e : Event n) : Prop := match e with
  | .cacheEvent ce => match ce.cid with
    | .proxy _ => True
    | .cache _ => False
  | .directoryEvent _ => False

structure Event.Shim.Global.ToCluster.matchingCluster (e_gdown e_shim_trans : Event n) : Prop where
  sameAddr : e_gdown.sameAddr n e_shim_trans
  atCorrCluster : e_gdown.correspondingClusterOfGlobalCache n e_shim_trans (Event.protocol n)

/-- A translated event from the shim `e_shim_trans` goes to the Proxy Cache, for the same address,
in the Cluster corresponding to requesting downgrade. -/
structure Event.Shim.Global.ToCluster.proxyCacheEvent (e_gdown e_shim_trans : Event n) : Prop where
  clusterMatch : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_shim_trans
  atProxy : e_shim_trans.atProxy n

/-- A translated Global Request that contains a Cluster Proxy Cache Event `e_shim` of request  -/
structure Event.Shim.Global.ToCluster.translateProxyEvent (e_gdown e_shim : Event n) (prop : ValidRequest → Prop) (isDown : Prop) : Prop where
  atCorrClusterProxy : Event.Shim.Global.ToCluster.proxyCacheEvent n e_gdown e_shim
  reqTranslation : prop e_shim.req
  downgrade : e_shim.down = isDown
  globalEncap : e_gdown.Encapsulates n e_shim

/-- A Global cache event encapsulates a cluster directory event at the corresponding cluster. -/
structure Event.Shim.Global.ToCluster.correspondingDirectoryEvent (e_gdown e_shim_trans : Event n) : Prop where
  clusterMatch : Event.Shim.Global.ToCluster.matchingCluster n e_gdown e_shim_trans
  atDir : e_shim_trans.isDirectoryEvent n
  globalEncap : e_gdown.Encapsulates n e_shim_trans

/-- Global Cache Downgrade Request, encapsulates a Cluster Directory event `e_cdir`.
`e_cdir` is of a specific Request stated by `prop`, and is a downgrade or request as per `isDown` -/
structure Event.Shim.Global.ToCluster.translateDirectoryEvent (e_gdown e_shim_trans : Event n) (prop : ValidRequest → Prop) (isDown : Prop) : Prop where
  dirCorrespondToGlobalCache : Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_shim_trans
  reqTranslation : prop e_shim_trans.req
  downgrade : e_shim_trans.down = isDown

/-- A global SC write downgrade encapsulates a Coherent Write `e_w` and Evict `e_v` (`e_w` orderedBefore `e_v`) in the corresponding Cluster's Proxy Cache. -/
structure Behaviour.encapCorrespondingGetSWAndEvict (b : Behaviour n) (init : InitialSystemState n)
  (e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict : Event n) : Prop where
  cohWriteDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_coh_write) true e_shim_coh_write e_dir_shim_coh_write
  cohWrite : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_write ValidRequest.isSCWrite False
  cohEvictDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_coh_evict) true e_shim_coh_evict e_dir_shim_coh_evict
  cohEvict : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_evict ValidRequest.isSCWrite True
  cohWriteImmBeforeEvict : b.ImmediateBottomPredecessor n e_dir_shim_coh_write e_dir_shim_coh_evict
  -- `e_gdown` only encapsulates these 2 cluster directory events at the corresponding cluster
  onlyWriteEvictDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_coh_write ∨ e_cdir = e_dir_shim_coh_evict

/-- Wrapper for the above. -/
def Behaviour.encapCorrespondingGetSWAndEvictWrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_coh_write ∈ b, ∃ e_dir_shim_coh_write, ∃ e_shim_coh_evict ∈ b, ∃ e_dir_shim_coh_evict ∈ b,
    b.encapCorrespondingGetSWAndEvict n init e_gdown e_shim_coh_write e_dir_shim_coh_write e_shim_coh_evict e_dir_shim_coh_evict

/-- Helper for (Shim) Axiom 16: State a Global Write Fwd Downgrade (for a Cluster with both Coherent Write and Read)
is translated to a Cluster (1) Proxy Cache SC Write, and (2) a Proxy Cache SC Write Evict. -/
structure Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop where
  -- clusterDir : Event.Shim.Global.ToCluster.directoryEventStateCheck n e_gdown
  -- gDownOnSWOrMR : b.dirEventMadeOn n init e_dir_check SW ∨ b.dirEventMadeOn n init MR -- consider using a weak downgrade
  scGDownTranslation : b.encapCorrespondingGetSWAndEvictWrapper n init e_gdown

/-- Wrapper for def above. -/
def Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop :=
  Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation n b init p e_gdown

structure Behaviour.encapCorrespondingGetMR (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown e_shim_coh_read e_dir_shim_coh_read : Event n) : Prop where
  cohRead : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_coh_read ValidRequest.isSCRead False
  cohReadDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_coh_read) true e_shim_coh_read e_dir_shim_coh_read
  onlyReadDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_coh_read

/-- Helper for (Shim) Axiom 16: State that a Global Read Fwd Downgrade (for a Cluster with both Coherent Write and Read)
is translated to a Cluster Proxy Cache SC Read. -/
def Behaviour.Shim.Global.bothWriteRead.SCReadDownTranslation (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_coh_read ∈ b, ∃ e_dir_shim_coh_read ∈ b, b.encapCorrespondingGetMR n init p e_gdown e_shim_coh_read e_dir_shim_coh_read

/-- Helper for (Shim) Axiom 16: translation from a Global SC Write Downgrade to the Cluster,
where the protocol has both a Coherent-Write and Coherent-Read.
Covers `bothCoherentWriteAndRead` case in `inductive Behaviour.Shim.GlobalToCluster` -/
inductive Behaviour.Shim.Global.bothWriteRead.Down (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| scWriteDown (hwrite_down : e_gdown.isSCWriteGlobalDowngrade)
  (translation : Behaviour.Shim.Global.bothCoherentWriteRead.SCWriteDownTranslation.wrapper n b init p e_gdown)
  : Behaviour.Shim.Global.bothWriteRead.Down b init p e_gdown
| scReadDown (hread_down : e_gdown.isSCReadGlobalDowngrade) (hmade_on_sw : b.cacheStateMadeOn n init e_gdown = SW) -- MR downgrades are sent to SW caches
  (translation : Behaviour.Shim.Global.bothWriteRead.SCReadDownTranslation n b init p e_gdown)
  : Behaviour.Shim.Global.bothWriteRead.Down b init p e_gdown

def Behaviour.Shim.Global.toCluster.clusterDirStateBefore (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) (s : State) : Prop :=
  (Behaviour.latestDirectoryState.Before.GlobalCache n b init e_gdown).state = s

/-- Helper for (Shim) Axiom 16: a Global `Write` Downgrade to a Cluster Protocol with no Coherent Read on Vd state
is translated to a Directory state check, directory downgrades from Vd to Vc, and Vc to I. -/
structure Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd (b : Behaviour n) (init : InitialSystemState n) (e_gdown e_dir_shim_vd_down e_dir_shim_vc_down : Event n) : Prop where
  gDownEncapVdWBDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vd_down ValidRequest.isNcWeakWrite True
  vdWBDirImmBeforeVcInvalDir : b.ImmediateBottomPredecessor n e_dir_shim_vd_down e_dir_shim_vc_down
  gDownEncapVcInvalDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vc_down ValidRequest.isNcWeakRead True
  -- `e_gdown` only encapsulates these 2 directory events at the corresponding cluster
  onlyVdVcDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_vd_down ∨ e_cdir = e_dir_shim_vc_down

def Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd.wrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_dir_shim_vd_down ∈ b, ∃ e_dir_shim_vc_down ∈ b,
    Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd n b init e_gdown e_dir_shim_vd_down e_dir_shim_vc_down

/-- Helper for (Shim) Axiom 16: a Global `Write` Downgrade to a Cluster Protocol with no Coherent Read on SW state
is translated to a Directory state check, then an Acquire, and directory downgrades from Vd to Vc, and Vc to I. -/
structure Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW (b : Behaviour n) (init : InitialSystemState n) (e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down : Event n) : Prop where
  acqDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_acq) true e_shim_acq e_dir_shim_acq
  acq : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_acq ValidRequest.isAcquire False
  acqDirImmBeforeVdWBDir : b.ImmediateBottomPredecessor n e_dir_shim_acq e_dir_shim_vd_down
  gDownEncapVdWBDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vd_down ValidRequest.isNcWeakWrite True
  vdWBDirImmBeforeVcInvalDir : b.ImmediateBottomPredecessor n e_dir_shim_vd_down e_dir_shim_vc_down
  gDownEncapVcInvalDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vc_down ValidRequest.isNcWeakRead True
  -- `e_gdown` only encapsulates these 3 directory events at the corresponding cluster
  onlyAcqVdVcDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_acq ∨ e_cdir = e_dir_shim_vd_down ∨ e_cdir = e_dir_shim_vc_down

def Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW.wrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_acq ∈ b, ∃ e_dir_shim_acq ∈ b, ∃ e_dir_shim_vd_down ∈ b, ∃ e_dir_shim_vc_down ∈ b,
    Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down e_dir_shim_vc_down

structure Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc (b : Behaviour n) (init : InitialSystemState n) (e_gdown e_dir_shim_vc_down : Event n) : Prop where
  gDownEncapVcInvalDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vc_down ValidRequest.isNcWeakRead True
  -- `e_gdown` only encapsulates this 1 directory event at the corresponding cluster
  onlyVcDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_vc_down

def Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc.wrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_dir_shim_vc_down ∈ b,
    Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc n b init e_gdown e_dir_shim_vc_down

/-- Helper for (Shim) Axiom 16: This inductive : Prop states the cases where a Global Fwded GetSW (GetM) is
translated to specified messages based on the state of the corresponding Cluster directory. -/
inductive Behaviour.Shim.Global.ToCluster.noCoherentRead.WriteDowngradeTranslation (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop
| onDirSW (dirSW : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown SW)
  (translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirSW.wrapper n b init e_gdown)
  : Behaviour.Shim.Global.ToCluster.noCoherentRead.WriteDowngradeTranslation b init e_gdown
| onDirVd (dirVd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVd.wrapper n b init e_gdown)
  : Behaviour.Shim.Global.ToCluster.noCoherentRead.WriteDowngradeTranslation b init e_gdown
| onDirVc (dirVc : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vc)
  (translation : Event.Shim.Global.ToCluster.noCoherentRead.globalWriteDownOnDirVc.wrapper n b init e_gdown)
  : Behaviour.Shim.Global.ToCluster.noCoherentRead.WriteDowngradeTranslation b init e_gdown

/-- Helper for (Shim) Axiom 16: a Global `Read` Downgrade to a Cluster Protocol with no Coherent Read on Vd state
is translated to a Directory state check, directory downgrades from Vd to Vc, and Vc to I. -/
structure Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd (b : Behaviour n) (init : InitialSystemState n) (e_gdown e_dir_shim_vd_down : Event n) : Prop where
  gDownEncapVdWBDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vd_down ValidRequest.isNcWeakWrite True
  onlyVdDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_vd_down

def Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd.wrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_acq ∈ b, ∃ e_dir_shim_acq ∈ b, ∃ e_dir_shim_vd_down ∈ b,
    Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd n b init e_gdown e_dir_shim_vd_down

/-- Helper for (Shim) Axiom 16: a Global `Read` Downgrade to a Cluster Protocol with no Coherent Read on SW state
is translated to a Directory state check, then an Acquire, and directory downgrades from Vd to Vc. -/
structure Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW (b : Behaviour n) (init : InitialSystemState n) (e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down : Event n) : Prop where
  acqDir : Behaviour.cacheEncapsulatesCorrespondingDirEvent n b (init.stateAt n e_shim_acq) true e_shim_acq e_dir_shim_acq
  acq : Event.Shim.Global.ToCluster.translateProxyEvent n e_gdown e_shim_acq ValidRequest.isAcquire False
  acqDirImmBeforeVdWBDir : b.ImmediateBottomPredecessor n e_dir_shim_acq e_dir_shim_vd_down
  gDownEncapVdWBDir : Event.Shim.Global.ToCluster.translateDirectoryEvent n e_gdown e_dir_shim_vd_down ValidRequest.isNcWeakWrite True
  onlyAcqVdDir : ∀ e_cdir ∈ b, Event.Shim.Global.ToCluster.correspondingDirectoryEvent n e_gdown e_cdir →
    e_cdir = e_dir_shim_acq ∨ e_cdir = e_dir_shim_vd_down

def Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW.wrapper (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop :=
  ∃ e_shim_acq ∈ b, ∃ e_dir_shim_acq ∈ b, ∃ e_dir_shim_vd_down ∈ b,
    Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW n b init e_gdown e_shim_acq e_dir_shim_acq e_dir_shim_vd_down

/-- Helper for (Shim) Axiom 16: This inductive : Prop states the cases where a Global Fwded GetMR (GetS) is
translated to specified messages based on the state of the corresponding Cluster directory. -/
inductive Behaviour.Shim.Global.ToCluster.noCoherentRead.ReadDowngradeTranslation (b : Behaviour n) (init : InitialSystemState n) (e_gdown : Event n) : Prop
| onDirSW (dirSW : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown SW)
  (translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirSW.wrapper n b init e_gdown)
  : Behaviour.Shim.Global.ToCluster.noCoherentRead.ReadDowngradeTranslation b init e_gdown
| onDirVd (dirVd : Behaviour.Shim.Global.toCluster.clusterDirStateBefore n b init e_gdown Vd)
  (translation : Event.Shim.Global.ToCluster.noCoherentRead.globalReadDownOnDirVd.wrapper n b init e_gdown)
  : Behaviour.Shim.Global.ToCluster.noCoherentRead.ReadDowngradeTranslation b init e_gdown

inductive Behaviour.Shim.Global.noCoherentRead.Down (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| scWriteDowngrade (hwrite_down : e_gdown.isSCWriteGlobalDowngrade)
  (translation : Behaviour.Shim.Global.ToCluster.noCoherentRead.WriteDowngradeTranslation n b init e_gdown)
  : Behaviour.Shim.Global.noCoherentRead.Down b init p e_gdown
| scReadDowngrade  (hread_down : e_gdown.isSCReadGlobalDowngrade) (hmade_on_sw : b.cacheStateMadeOn n init e_gdown = SW)
  (translation : Behaviour.Shim.Global.ToCluster.noCoherentRead.ReadDowngradeTranslation n b init e_gdown)
  : Behaviour.Shim.Global.noCoherentRead.Down b init p e_gdown

/-- (Shim) Axiom 16: Downgrade at a Global Cache is translated to a Cluster Directory access -/
inductive Behaviour.Shim.GlobalToCluster (b : Behaviour n) (init : InitialSystemState n) (p : Protocol n) (e_gdown : Event n) : Prop
| bothCoherentWriteAndRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hboth_coherent_wr : p.hasCoherentWriteAndRead n) (downTranslation : Behaviour.Shim.Global.bothWriteRead.Down n b init p e_gdown)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
| noCoherentRead (hcorrespond : e_gdown.correspondingClusterOfGlobalCache n p Protocol.pi)
  (hno_coherent_read : p.noCoherentRead n) (downTranslation : Behaviour.Shim.Global.noCoherentRead.Down n b init p e_gdown)
  : Behaviour.Shim.GlobalToCluster b init p e_gdown
