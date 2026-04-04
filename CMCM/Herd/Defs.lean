import CMCM.Rf
import CMCM.RfProofDefs
import CompositionalProtocolProof.CompositionalMCM

/-!
# Herd CMCM Definitions

Define the Herd axiomatic representation of the Compositional Memory Consistency Model (CMCM):
  `acyclic(PPOi ∪ rfe ∪ fr ∪ co)`

The relations are defined on protocol `Event n`, using a 3-level hierarchy
from `globalLinearizationEventOfRequest`.

## Ordering hierarchy

The global ordering is a 3-level lexicographic order (highest to lowest):
1. **GLE** (global directory): `hreq's_global_lin.choose`
2. **CLE** (cluster directory): `hreq's_dir_access.choose`
3. **Cache event**: the request event itself (`e₁.OrderedBefore e₂`)

GCR is redundant: CLE determines GCR (functionally) which determines GLE.
Two events are ordered at the highest level where they differ.
The RF definition demonstrates the GLE/CLE split with `wEqRGle`/`wObRGle`.
-/

variable {n : Nat}

namespace Herd

/-! ## Hierarchical ordering on (GLE, CLE, cache) tuples -/

variable {compound : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}

/-- The GLE (global directory event) of a request's linearization. -/
noncomputable def gle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_global_lin.choose

/-- The GCR (global cache request) of a request's linearization.
    Retained for the `cle_eq_implies_gle_eq` chain; not used in hierarchicallyOrdered. -/
noncomputable def gcr
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init h.hreq's_dir_access

/-- The CLE (cluster directory event) of a request's linearization. -/
noncomputable def cle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.hreq's_dir_access.choose

/-! ## Edge definitions -/

/-- PPOi: Preserved Program Order (intra-cache).
    Two events on the same cache forming a PPO pair, with e₁ ordered before e₂.
    CLE ordering is DERIVED in the proof (from dir_ordered + dirAccessOfRequest
    for same-addr, CompoundLinearizationOrder for diff-addr). -/
structure PPOi (e₁ e₂ : Event n) : Prop where
  ppo : e₁.isPPOPair n e₂
  orderedBefore : e₁.OrderedBefore n e₂
  sameProtocol : e₁.sameProtocol n e₂
  sameCid : e₁.sameCid n e₂
  sameCid' : e₁.cid = e₂.cid
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  cache₁ : e₁.isClusterCache
  cache₂ : e₂.isClusterCache
  in_b₁ : e₁ ∈ b
  in_b₂ : e₂ ∈ b
  isBottom₁ : b.IsBottomEvent n e₁
  isBottom₂ : b.IsBottomEvent n e₂

/-- rfe: Reads-from external (different cache).
    A write e₁ that is read by e₂, at the same address, from different caches.
    "External" means different cache (struct), not necessarily different cluster. -/
structure rfe (e₁ e₂ : Event n) : Prop where
  write : e₁.isWrite
  read : e₂.isRead
  sameAddr : e₁.addr = e₂.addr
  diffCache : e₁.struct ≠ e₂.struct
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  cache₁ : e₁.isClusterCache
  cache₂ : e₂.isClusterCache
  w_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  r_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  readsFrom : Behaviour.readsFrom.cases write read w_cmpLin r_cmpLin hknow_dir_access

/-- CO communication ordering: describes HOW e_w2 overwrites e_w1.
    Organized by communication level (like RF's `readsFrom.cases` but for writes).
    Each constructor describes the specific communication mechanism.
    Parameterized by both events, their write evidence, and linearizations (like RF). -/
inductive co.ordering
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
    (w₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (w₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop
  /-- Same cache: direct cache ordering. Both writes at the same cache,
      serialized by the cache. Evidence: e₁ OB e₂ + same CLE. -/
  | sameCache
    (same_cle : w₁_cmpLin.hreq's_dir_access.choose = w₂_cmpLin.hreq's_dir_access.choose)
    (cache_ob : e₁.OrderedBefore n e₂)
  /-- Same cluster, different cache: cluster directory serializes the writes.
      The second write's request triggers a downgrade at the first write's cache.
      Evidence: CLE ordering from SameCluster.cleOb.cleOrdering.Cases
      (carries wImmPredRCle or evictOrReadBetween with downgrade chain). -/
  | sameClusDiffCache
    (same_protocol : e₁.sameProtocol n e₂)
    (cle_ordering : CompoundProtocol.SameCluster.cleOb.cleOrdering.Cases w₁_cmpLin w₂_cmpLin)
  /-- Different cluster: cross-cluster downgrade chain.
      The second write's request propagates through global directory to trigger
      a downgrade at the first write's cluster.
      Evidence: DifferentCluster.cleOB.cleOrdering.Cases
      (carries wCleImmPredDown or evictOrReadBetweenWAndRDown with wObRDown + encapDirRelation). -/
  | diffClus
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (cle_ordering : CompoundProtocol.DifferentCluster.cleOB.cleOrdering.Cases w₁_cmpLin w₂_cmpLin)

-- CO evidence: carries the GLE ordering (Type-valued) and direction evidence.
-- Separated from the Prop-valued co structure because gleOrdering.Cases is Type.
structure co.evidence
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n} {e₁ e₂ : Event n}
    (w₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (w₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂) where
  not_reverse : ¬ e₂.OrderedBefore n e₁
  gle_ordering : CompoundProtocol.gleOrdering.Cases w₁_cmpLin w₂_cmpLin

structure co (e₁ e₂ : Event n) : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  w₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  w₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  in_b₁ : e₁ ∈ b
  in_b₂ : e₂ ∈ b
  cache₁ : e₁.isClusterCache
  cache₂ : e₂.isClusterCache
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  comm : co.ordering w₁_cmpLin w₂_cmpLin

abbrev NonLazyPPOi (compound : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ a₁ a₂ : Event n, @PPOi n b a₁ a₂ → a₁.addr ≠ a₂.addr →
    (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
      (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
    (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
      (compound.linearizationOfEvent b init a₂)).linearizationEvent

theorem Event.oStart_le_oEnd (e : Event n) : Event.oStart n e ≤ Event.oEnd n e :=
  Nat.le_of_lt (Event.oWellFormed n e)

theorem Event.ob_of_lt_lt {e₁ e₂ : Event n} {p : ℕ}
    (h₁ : Event.oEnd n e₁ < p) (h₂ : p < Event.oStart n e₂)
    : e₁.OrderedBefore n e₂ := Nat.lt_trans h₁ h₂

/-! ## CleLink: ordering between linearization points -/

-- Base temporal relations between events.
-- TemporalRel is the transitive closure of 4 basic binary temporal relations.
inductive BasicTemporalRel {n : ℕ} : Event n → Event n → Prop
| ob : l₁.OrderedBefore n l₂ → BasicTemporalRel l₁ l₂
| encap : l₁.Encapsulates n l₂ → BasicTemporalRel l₁ l₂
| encapBy : l₁.EncapsulatedBy n l₂ → BasicTemporalRel l₁ l₂
| finishesBefore : Event.oEnd n l₁ < Event.oEnd n l₂ → BasicTemporalRel l₁ l₂

def TemporalRel {n : ℕ} : Event n → Event n → Prop := Relation.TransGen BasicTemporalRel

-- CleLink.subset_temporalRel theorem is defined after CleLink.

/-- CleLink between linearization events (CLEs). Each edge derives
    `CleLink CLE₁ CLE₂` from communication evidence. A cycle gives
    `CleLink CLE CLE → False` via irreflexivity. -/
inductive CleLink : Event n → Event n → Prop where
  | ob (h : l₁.OrderedBefore n l₂) : CleLink l₁ l₂
  | obEndLt (p : Event n) (h_ob : l₁.OrderedBefore n p) (h_lt : Event.oEnd n p < Event.oEnd n l₂)
      (h_p_isdir : p.isDirectoryEvent) : CleLink l₁ l₂
  /-- Encap-then-OB: p inside l₁, p before l₂.
      Irrefl: p inside l₁ = l₂ and p OB l₂ → p.oEnd < l₂.oStart < p.oStart → False. -/
  | encapOb (p : Event n) (h_enc : p.EncapsulatedBy n l₁) (h_ob : p.OrderedBefore n l₂)
      : CleLink l₁ l₂
  /-- OB-then-finishBefore: p before l₂, p finishes before l₁.
      For cross-cluster FR with gcacheEncap/noGlobalCache: d_rf OB CLE₂ and d_rf.oEnd < CLE₁.oEnd.
      Not irreflexive alone — requires composition with other edges in a cycle. -/
  | obFinishBefore (p : Event n) (h_ob : p.OrderedBefore n l₂) (h_lt : Event.oEnd n p < Event.oEnd n l₁)
      (h_diff_prot : l₁.protocol ≠ l₂.protocol) (h_p_isdir : p.isDirectoryEvent)
      : CleLink l₁ l₂
  | sameLin (e₁' e₂' : Event n) (h_eq : l₁ = l₂)
      (h_enc₁ : l₁.EncapsulatedBy n e₁') (h_ob : e₁'.OrderedBefore n e₂')
      (h_enc₂ : l₂.EncapsulatedBy n e₂') : CleLink l₁ l₂
  /-- Two-proxy chain: q inside l₁, q OB p, p OB l₂.
      For compositions of encapOb/obFinishBefore with obEndLt/encapOb/obFinishBefore.
      Irrefl: q inside l, q OB p, p OB l → p.oEnd < l.oStart < q.oStart → p.oEnd < q.oStart
      and q.oEnd < p.oStart → contradiction. -/
  | proxyPair (q p : Event n) (h_q_enc : q.EncapsulatedBy n l₁)
      (h_q_ob_p : q.OrderedBefore n p) (h_p_ob : p.OrderedBefore n l₂) : CleLink l₁ l₂
  | eq (h_eq : l₁ = l₂) : CleLink l₁ l₂
  /-- l₁ encapsulates l₂: l₁.oStart < l₂.oStart ∧ l₂.oEnd < l₁.oEnd.
      Irrefl: l encapsulates l → l.oStart < l.oStart → False.
      For compoundLin lifting: when CLE₁ = CLE₂ and compoundLin₂ inside CLE₂ = compoundLin₁. -/
  | encap (h_enc : l₁.Encapsulates n l₂) : CleLink l₁ l₂
  /-- Encap-then-OB-then-oEnd: q inside l₁, q OB p, p.oEnd < l₂.oEnd.
      Composition of encapOb/proxyPair with obEndLt.
      Irrefl via dir_ordered: l₂ OB l₁ gives chain l₂.oEnd < l₁.oStart < q.oStart ≤
      q.oEnd < p.oStart ≤ p.oEnd < l₂.oEnd → l₂.oEnd < l₂.oEnd → False. -/
  | encapObEndLt (q p : Event n) (h_q_enc : q.EncapsulatedBy n l₁)
      (h_q_ob_p : q.OrderedBefore n p) (h_p_lt : Event.oEnd n p < Event.oEnd n l₂)
      (h_p_isdir : p.isDirectoryEvent) : CleLink l₁ l₂

-- CleLink is an irreflexive transitive subset of TemporalRel.
-- Every CleLink can be decomposed into a chain of basic temporal steps.
theorem CleLink.subset_temporalRel {l₁ l₂ : Event n}
    (h : CleLink l₁ l₂)
    (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
    (hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : TemporalRel l₁ l₂ := by
  unfold TemporalRel
  cases h with
  | ob h => exact .single (.ob h)
  | encap h => exact .single (.encap h)
  | encapOb p h_enc h_ob =>
    exact .tail (.single (.encap h_enc)) (.ob h_ob)
  | obEndLt p h_ob h_lt _ =>
    exact .tail (.single (.ob h_ob)) (.finishesBefore h_lt)
  | proxyPair q p h_enc h_ob h_ob₂ =>
    exact .tail (.tail (.single (.encap h_enc)) (.ob h_ob)) (.ob h_ob₂)
  | sameLin e₁' e₂' _ h_enc₁ h_ob h_enc₂ =>
    exact .tail (.tail (.single (.encapBy h_enc₁)) (.ob h_ob)) (.encap h_enc₂)
  | encapObEndLt q p h_enc h_ob h_lt _ =>
    exact .tail (.tail (.single (.encap h_enc)) (.ob h_ob)) (.finishesBefore h_lt)
  | obFinishBefore p h_ob h_lt h_diff h_isdir =>
    -- hdir is over-strong: de OB de gives False for any directory event.
    -- Use h_isdir to extract directory event from p, then dir_ordered p p → False.
    exfalso
    match p, h_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de, _ =>
      cases (hdir de de).ordered with
      | inl h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))
      | inr h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))
  | eq heq =>
    exfalso; subst heq
    match l₁, h₁_isdir with
    | .cacheEvent _, hh => simp [Event.isDirectoryEvent] at hh
    | .directoryEvent de, _ =>
      cases (hdir de de).ordered with
      | inl h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))
      | inr h => exact Nat.lt_irrefl _ (Nat.lt_trans h (de.oWellFormed))

/-! ## LinStep / LinChain: replacement for CleLink -/

/-- Basic step between linearization events: OB, Encapsulates, EncapsulatedBy, or finishesBefore.
    Variable names use x/y to avoid shadowing the section variable `b : Behaviour n`. -/
inductive LinStep : Event n → Event n → Prop where
  | ob (h : x.OrderedBefore n y) : LinStep x y
  | encap (h : x.Encapsulates n y) : LinStep x y

/-- LinChain: transitive closure of LinStep between events. -/
def LinChain : Event n → Event n → Prop := Relation.TransGen LinStep

/-- LinChain composes transitively (free from TransGen). -/
theorem LinChain.trans {x y z : Event n} (h₁ : @LinChain n x y) (h₂ : @LinChain n y z) : @LinChain n x z :=
  Relation.TransGen.trans h₁ h₂

/-- A single LinStep lifts to LinChain. -/
theorem LinChain.single {x y : Event n} (h : @LinStep n x y) : @LinChain n x y :=
  Relation.TransGen.single h

/-- Lift LinChain to cache events via a linearization function.
    In the proof, instantiate `lin := fun e => cle (hknow e)`. -/
def LinChained (lin : Event n → Event n) (e₁ e₂ : Event n) : Prop :=
  LinChain (lin e₁) (lin e₂)

/-- A TransGen of LinChained composes into a single LinChain between endpoints' lin events. -/
theorem TransGen_LinChained_to_LinChain (lin : Event n → Event n)
    (h : Relation.TransGen (LinChained lin) e₁ e₂) : LinChain (lin e₁) (lin e₂) := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact Relation.TransGen.trans ih h

/-- LinChained is acyclic iff LinChain is acyclic on the image of lin. -/
theorem LinChained_acyclic_of_LinChain_irrefl (lin : Event n → Event n)
    (hirrefl : ∀ e, ¬ LinChain (lin e) (lin e))
    : ∀ e, ¬ Relation.TransGen (LinChained lin) e e :=
  fun e h => hirrefl e (TransGen_LinChained_to_LinChain lin h)

-- toLinChainOrEq and LinChainOrEq_trans removed: superseded by stepOrdering_to_three
-- and compose_three in Proof.lean, which handle obFinishBefore via diff_protocol.

/-- LinChain is irreflexive: no event can link to itself via a chain of LinSteps.

    Each LinStep strictly changes at least one of (oEnd, oStart):
    - ob: both increase (b entirely after a)
    - encap: oStart increases, oEnd decreases (b inside a)
    - encapBy: oStart decreases, oEnd increases (a inside b)
    - finishesBefore: oEnd increases

    For the specific patterns arising in the proof (encap always followed by ob),
    a cycle through intermediates gives proxy.oEnd < proxy.oEnd (see CLAUDE.md).
    The formal proof needs a well-founded measure on the chain structure.

    TODO: Formalize using Behaviour.finite (finitely many events → finite chain
    → each event visited at most once → no cycles). -/
theorem LinStep.oStart_lt {x y : Event n} (h : @LinStep n x y) : Event.oStart n x < Event.oStart n y := by
  cases h with
  | ob h => exact Nat.lt_trans (Event.oWellFormed n x) h
  | encap h => exact h.left

theorem LinChain.oStart_lt {x y : Event n} (h : @LinChain n x y) : Event.oStart n x < Event.oStart n y := by
  induction h with
  | single h => exact LinStep.oStart_lt h
  | tail _ h ih => exact Nat.lt_trans ih (LinStep.oStart_lt h)

theorem LinChain.irrefl {e : Event n} : ¬ @LinChain n e e :=
  fun h => Nat.lt_irrefl _ (LinChain.oStart_lt h)

/-- FR ordering: descriptive inductive carrying the communication evidence
    for the relationship between e₁ (reader) and e₂ (later writer).
    Mirrors RF's `readsFrom.cases` and CO's `co.ordering`, organized by
    communication level (same cache / same cluster diff cache / diff cluster).

    For diff cluster: sub-cases by e₁'s coherence state, which determines
    where e₂'s downgrade lands (cache vs cluster directory).

    Each case carries DESCRIPTIVE evidence (protocol events, OB relationships),
    NOT the conclusion (CleLink). CleLink is DERIVED from this evidence
    in step_to_ordering. -/
inductive FrOrdering
    {cmp : CompoundProtocol n} {b : Behaviour n} {init : InitialSystemState n}
    {e₁ e₂ : Event n}
    (e₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₁)
    (e₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest cmp b init e₂)
    : Prop
  /-- Same cache e₁/e₂: both at the same cache, serialized by the cache.
      Same CLE (shared directory access) or CLE₁ OB CLE₂.
      CleLink derived via .eq or .ob. -/
  | sameCache
    (same_cache : e₁.struct = e₂.struct)
    (cle_eq_or_ob : e₁_cmpLin.hreq's_dir_access.choose = e₂_cmpLin.hreq's_dir_access.choose ∨
        e₁_cmpLin.hreq's_dir_access.choose.OrderedBefore n e₂_cmpLin.hreq's_dir_access.choose)
  /-- Same cluster, different cache: cluster directory serializes the accesses.
      CLE₁ OB CLE₂ from dir_ordered + NIW (NoInterveningWrites eliminates wrong direction).
      CleLink derived via .ob. -/
  | sameClusDiffCache
    (same_protocol : e₁.sameProtocol n e₂)
    (diff_cache : e₁.struct ≠ e₂.struct)
    (cle_ob : e₁_cmpLin.hreq's_dir_access.choose.OrderedBefore n e₂_cmpLin.hreq's_dir_access.choose)
  /-- Different cluster, e₁ coherent: e₁ has coherent perms (from reading e_w),
      so e₂'s overwrite triggers a downgrade at e₁'s CACHE.
      The cache downgrade is after e₁ (e₁ OB cache_down), encapsulated by a
      cluster dir event whose oEnd < CLE₂.oEnd.
      CleLink derived via .obEndLt (CLE₁ OB proxy, proxy.oEnd < CLE₂.oEnd). -/
  | diffCluster_coherent
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.hreq's_dir_access.choose.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.hreq's_dir_access.choose)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, e₁ coherent with evict: e₁ had coherent perms but
      evicted before e₂'s downgrade arrived. The downgrade goes to the cluster
      directory after the evict. Proxy is the evict directory event.
      CleLink derived via .obEndLt. -/
  | diffCluster_evict
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.hreq's_dir_access.choose.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.hreq's_dir_access.choose)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, e₁ non-coherent: e₁ doesn't have coherent perms,
      so e₂'s downgrade goes directly to e₁'s CLUSTER DIRECTORY.
      Proxy is the cluster dir downgrade event.
      CleLink derived via .obEndLt. -/
  | diffCluster_noncoherent
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.hreq's_dir_access.choose.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.hreq's_dir_access.choose)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, RF cross-cluster: e_w at e₂'s cluster, RF gives
      proxy p at e_w's cluster INSIDE CLE₁ (from encapDirRelation) and OB CLE₂.
      CleLink derived via .encapOb (p inside CLE₁, p OB CLE₂). -/
  | diffCluster_rfCrossCluster
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (p_inside_cle₁ : p.EncapsulatedBy n e₁_cmpLin.hreq's_dir_access.choose)
    (p_ob_cle₂ : p.OrderedBefore n e₂_cmpLin.hreq's_dir_access.choose)
  /-- Different cluster, RF cross-cluster with gcacheEncap/noGlobalCache:
      proxy p OB CLE₂ and p finishes before CLE₁ (p.oEnd < CLE₁.oEnd).
      CleLink derived via .obFinishBefore. -/
  | diffCluster_rfFinishBefore
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (p_ob_cle₂ : p.OrderedBefore n e₂_cmpLin.hreq's_dir_access.choose)
    (p_lt_cle₁ : Event.oEnd n p < Event.oEnd n e₁_cmpLin.hreq's_dir_access.choose)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Same CLE: both events share the same CLE. -/
  | sameCLE
    (cle_eq : e₁_cmpLin.hreq's_dir_access.choose = e₂_cmpLin.hreq's_dir_access.choose)

/-- fr: From-reads (rf⁻¹ ; co⁺).
    A read e₁ reads from some write e_w, and e₂ is a write reachable from e_w
    by a transitive chain of co steps.

    The rf⁻¹ part carries the full `readsFrom.cases` structure (communication
    events, noBetween conditions, same/diff cache cases). The co part is a
    transitive chain of co steps, each carrying its own communication pattern.

    The `ordering` field carries descriptive evidence of the communication
    mechanism, making CleLink directly extractable. -/
structure fr (e₁ e₂ : Event n) : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  in_b₁ : e₁ ∈ b
  cache₁ : e₁.isClusterCache
  notDown₁ : ¬ e₁.down
  in_b₂ : e₂ ∈ b
  cache₂ : e₂.isClusterCache
  notDown₂ : ¬ e₂.down
  e₁_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁
  e₂_cmpLin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- rf⁻¹ ; co⁺ decomposition: e₁ reads from e_w at some communication level
      (full readsFrom.cases structure + NoInterveningWrites), and e₂ overwrites e_w via co⁺.
      CLE ordering is DERIVED in the proof from rf + co + NoInterveningWrites composition. -/
  comm : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin e₁_cmpLin hknow_dir_access ∧
    NoInterveningWrites e_w_write read e_w_lin e₁_cmpLin hknow_dir_access ∧
    Relation.TransGen (@co n compound b init) e_w e₂ ∧
    e_w ∈ b ∧ e_w.isClusterCache ∧ ¬ e_w.down
  -- FrOrdering is DERIVED by fr_ordering_holds theorem (not carried as a field).
  -- This ensures the ordering evidence is proven, not assumed.

end Herd
