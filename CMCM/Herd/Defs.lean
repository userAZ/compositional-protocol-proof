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
  h.gle

/-- The GCR (global cache request) of a request's linearization.
    Retained for the `cle_eq_implies_gle_eq` chain; not used in hierarchicallyOrdered. -/
noncomputable def gcr
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  Behaviour.Shim.ClusterToGlobal.cDir'sGReq.wrapper compound b init h.hreq's_dir_access

/-- The CLE (cluster directory event) of a request's linearization. -/
noncomputable def cle
    (h : CompoundProtocol.globalLinearizationEventOfRequest compound b init e) : Event n :=
  h.cle

/-! ## CleLink: ordering between linearization points -/

-- Base temporal relations between events.
-- TemporalRel is the transitive closure of 4 basic binary temporal relations.
inductive BasicTemporalRel {n : ℕ} : Event n → Event n → Prop
| ob : l₁.OrderedBefore n l₂ → BasicTemporalRel l₁ l₂
| encap : l₁.Encapsulates n l₂ → BasicTemporalRel l₁ l₂
| encapBy : l₁.EncapsulatedBy n l₂ → BasicTemporalRel l₁ l₂
| finishesBefore : Event.oEnd n l₁ < Event.oEnd n l₂ → BasicTemporalRel l₁ l₂
/-- Proxy: p OB l₂ and p.oEnd < l₁.oEnd. Used for obFinishBefore (cross-cluster)
    and cle_ob_compoundLin (compoundLin after CLE, need chain to CLE₂). -/
| finishesAfterProxy (p : Event n) : p.OrderedBefore n l₂ → Event.oEnd n p < Event.oEnd n l₁ → BasicTemporalRel l₁ l₂

def TemporalRel {n : ℕ} : Event n → Event n → Prop := Relation.TransGen BasicTemporalRel

-- CleLink.subset_temporalRel theorem is defined after CleLink.

-- OB between events implies they're distinct.
theorem Event.ne_of_ob {e₁ e₂ : Event n} (h : e₁.OrderedBefore n e₂) : e₁ ≠ e₂ :=
  fun heq => by subst heq; exact Nat.lt_irrefl _ (Nat.lt_trans h (Event.oWellFormed n e₁))

-- Encapsulation implies distinct events.
theorem Event.ne_of_encap {e₁ e₂ : Event n} (h : e₁.Encapsulates n e₂) : e₁ ≠ e₂ :=
  fun heq => by subst heq; exact Nat.lt_irrefl _ h.left

-- EncapsulatedBy implies distinct events.
theorem Event.ne_of_encapBy {e₁ e₂ : Event n} (h : e₁.EncapsulatedBy n e₂) : e₁ ≠ e₂ :=
  fun heq => by subst heq; exact Nat.lt_irrefl _ h.left

-- Different protocol implies distinct events.
theorem Event.ne_of_diff_prot {e₁ e₂ : Event n} (h : e₁.protocol ≠ e₂.protocol) : e₁ ≠ e₂ :=
  fun heq => by subst heq; exact absurd rfl h

-- EncapOb (p inside l₁, p OB l₂) at self → False.
theorem Event.ne_of_encapOb {l₁ l₂ : Event n} {p : Event n}
    (h_enc : p.EncapsulatedBy n l₁) (h_ob : p.OrderedBefore n l₂) : l₁ ≠ l₂ :=
  fun heq => Nat.lt_irrefl _ (heq ▸ Nat.lt_trans h_enc.left
    (Nat.lt_of_le_of_lt (Nat.le_of_lt p.oWellFormed) h_ob))

-- ProxyPair (q inside l₁, q OB p, p OB l₂) at self → False.
theorem Event.ne_of_proxyPair {l₁ l₂ : Event n} {q p : Event n}
    (h_enc : q.EncapsulatedBy n l₁) (h_qob : q.OrderedBefore n p) (h_pob : p.OrderedBefore n l₂) : l₁ ≠ l₂ :=
  fun heq => Nat.lt_irrefl _ (heq ▸ Nat.lt_trans h_enc.left (Nat.lt_trans
    (Nat.lt_of_le_of_lt (Nat.le_of_lt q.oWellFormed) h_qob)
    (Nat.lt_of_le_of_lt (Nat.le_of_lt p.oWellFormed) h_pob)))

-- ObEndLt (l₁ OB p, p.oEnd < l₂.oEnd) at self → False.
theorem Event.ne_of_obEndLt {l₁ l₂ : Event n} {p : Event n}
    (h_ob : l₁.OrderedBefore n p) (h_lt : Event.oEnd n p < Event.oEnd n l₂) : l₁ ≠ l₂ :=
  fun heq => Nat.lt_irrefl _ (heq ▸ Nat.lt_trans h_ob
    (Nat.lt_of_lt_of_le p.oWellFormed (Nat.le_of_lt h_lt)))

-- EncapObEndLt (q inside l₁, q OB p, p.oEnd < l₂.oEnd) at self → False.
-- Uses dir_ordered on l₁ and p (DISTINCT events, legitimate).
-- Actually: just chain temporals.
-- ne_of_encapObEndLt: removed. encapObEndLt doesn't carry h_ne.
-- At cycle closure, handled by dir_ordered on DISTINCT events l and p.

/-- CleLink between linearization events (CLEs). Each edge derives
    `CleLink CLE₁ CLE₂` from communication evidence. A cycle gives
    `CleLink CLE CLE → False` via irreflexivity.
    Non-eq constructors carry h_ne : l₁ ≠ l₂ (from temporal/protocol evidence).
    At cycle closure (l₁ = l₂): non-eq cases give absurd rfl h_ne → False. -/

inductive CleLink : Event n → Event n → Prop where
  | ob (h : l₁.OrderedBefore n l₂) (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | obEndLt (p : Event n) (h_ob : l₁.OrderedBefore n p) (h_lt : Event.oEnd n p < Event.oEnd n l₂)
      (h_p_isdir : p.isDirectoryEvent) (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | encapOb (p : Event n) (h_enc : p.EncapsulatedBy n l₁) (h_ob : p.OrderedBefore n l₂)
      (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | obFinishBefore (p : Event n) (h_ob : p.OrderedBefore n l₂) (h_lt : Event.oEnd n p < Event.oEnd n l₁)
      (h_diff_prot : l₁.protocol ≠ l₂.protocol) (h_p_isdir : p.isDirectoryEvent)
      (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | sameLin (e₁' e₂' : Event n) (h_eq : l₁ = l₂)
      (h_enc₁ : l₁.EncapsulatedBy n e₁') (h_ob : e₁'.OrderedBefore n e₂')
      (h_enc₂ : l₂.EncapsulatedBy n e₂') : CleLink l₁ l₂
  | proxyPair (q p : Event n) (h_q_enc : q.EncapsulatedBy n l₁)
      (h_q_ob_p : q.OrderedBefore n p) (h_p_ob : p.OrderedBefore n l₂)
      (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | eq (h_eq : l₁ = l₂) : CleLink l₁ l₂
  | encap (h_enc : l₁.Encapsulates n l₂) (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂
  | encapObEndLt (q p : Event n) (h_q_enc : q.EncapsulatedBy n l₁)
      (h_q_ob_p : q.OrderedBefore n p) (h_p_lt : Event.oEnd n p < Event.oEnd n l₂)
      (h_p_isdir : p.isDirectoryEvent) (h_ne : l₁ ≠ l₂) : CleLink l₁ l₂

-- CleLink decomposes into equality or a transitive chain of basic temporal steps.
-- The eq constructor maps to l₁ = l₂ (not TemporalRel, which requires strict progress).
-- All other constructors map to TemporalRel chains.
theorem CleLink.subset_temporalRel {l₁ l₂ : Event n}
    (h : CleLink l₁ l₂)
    (_h₁_isdir : l₁.isDirectoryEvent) (_h₂_isdir : l₂.isDirectoryEvent)
    (_hdir : ∀ (de₁ de₂ : DirectoryEvent n), DirectoryEvent.AreOrdered n de₁ de₂)
    : l₁ = l₂ ∨ TemporalRel l₁ l₂ := by
  cases h with
  | ob h => exact Or.inr (.single (.ob h))
  | encap h => exact Or.inr (.single (.encap h))
  | encapOb p h_enc h_ob =>
    exact Or.inr (.tail (.single (.encap h_enc)) (.ob h_ob))
  | obEndLt p h_ob h_lt _ =>
    exact Or.inr (.tail (.single (.ob h_ob)) (.finishesBefore h_lt))
  | proxyPair q p h_enc h_ob h_ob₂ =>
    exact Or.inr (.tail (.tail (.single (.encap h_enc)) (.ob h_ob)) (.ob h_ob₂))
  | sameLin e₁' e₂' _ h_enc₁ h_ob h_enc₂ =>
    exact Or.inr (.tail (.tail (.single (.encapBy h_enc₁)) (.ob h_ob)) (.encap h_enc₂))
  | encapObEndLt q p h_enc h_ob h_lt _ =>
    exact Or.inr (.tail (.tail (.single (.encap h_enc)) (.ob h_ob)) (.finishesBefore h_lt))
  | obFinishBefore p h_ob h_lt _ _ =>
    exact Or.inr (.single (.finishesAfterProxy p h_ob h_lt))
  | eq heq => exact Or.inl heq

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

/-- How a compoundLin event connects to its CLE through dirAccessOfRequest.
    Each case names the proxy relationship explicitly:
    - `eq`: cmpLin = CLE (dirLin case — the event linearizes at the directory)
    - `cle_ob`: CLE OB cmpLin (orderBeforeDir — a predecessor got perms through a dir
      access, and cmpLin = e itself. The predecessor encaps the CLE.)
    - `inside`: cmpLin inside CLE (encapDir — CLE encapsulates cmpLin. The CLE
      is the dir event that directly processes the request.)
    orderAfterDir is vacuous (compoundLin_not_ob_cle). -/
inductive CmpLinCleRel {n : ℕ} (cmpLin cle : Event n) : Prop
  | eq (h : cmpLin = cle)
  | cle_ob (h : cle.OrderedBefore n cmpLin)
  | inside (h : cle.Encapsulates n cmpLin)

/-- LinLink: ordering between compoundLin events, bridged through proxy CLEs.
    `step`: both compoundLin events ARE directory events (dirLin case).
    `proxy`: compoundLin events connected through CLE proxies with EXPLICIT
    proxy chain via CmpLinCleRel (showing how each cmpLin relates to its CLE
    through dirAccessOfRequest: encapDir, orderBeforeDir, or eq). -/
inductive LinLink {n : ℕ} (l₁ l₂ : Event n) : Prop
  /-- Both cmpLin events are CLEs themselves (dirLin). -/
  | step (h : @CleLink n l₁ l₂) (h₁_isdir : l₁.isDirectoryEvent) (h₂_isdir : l₂.isDirectoryEvent)
  /-- cmpLin events connected through CLE proxies.
      cle₁/cle₂ are the proxy dir events from dirAccessOfRequest.
      h_prefix: how cmpLin₁ connects to cle₁ (eq/cle_ob/inside from dirAccessOfRequest).
      h_suffix: how cmpLin₂ connects to cle₂.
      h_so: CleLink between the proxy CLEs (from step_to_ordering). -/
  | proxy (cle₁ cle₂ : Event n)
      (h_so : @CleLink n cle₁ cle₂)
      (h₁_isdir : cle₁.isDirectoryEvent) (h₂_isdir : cle₂.isDirectoryEvent)
      (h_prefix : CmpLinCleRel l₁ cle₁)
      (h_suffix : CmpLinCleRel l₂ cle₂)

/-- The 3-way compoundLin ordering for an edge: forward LinLink, equality, or reverse LinLink. -/
abbrev CmpLinOrdering {n : ℕ} (cmpLin₁ cmpLin₂ : Event n) : Prop :=
  LinLink cmpLin₁ cmpLin₂ ∨ cmpLin₁ = cmpLin₂ ∨ LinLink cmpLin₂ cmpLin₁
/-! ## Edge definitions

All edge definitions are parameterized by linearization evidence `lin₁ lin₂`
(of type `globalLinearizationEventOfRequest`). This makes compoundLin the
PRIMARY concept: `lin.compoundLin` is the linearization point, `lin.cle` is
the CLE, `lin.gle` is the GLE. The underlying cache events `e₁ e₂` are
implicit (inferred from the lin types). -/

/-- PPOi: Preserved Program Order (intra-cache).
    Two events on the same cache forming a PPO pair, with e₁ ordered before e₂.
    Parameterized by linearization evidence (provides compoundLin/CLE/GLE). -/
structure PPOi {e₁ e₂ : Event n}
    (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : Prop where
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
  /-- CompoundLin events are ordered through CLE bridge. -/
  cmpLin_ordered : CmpLinOrdering lin₁.compoundLin lin₂.compoundLin

/-- rfe: Reads-from external (different cache).
    A write e₁ that is read by e₂, at the same address, from different caches.
    Parameterized by linearization evidence (provides compoundLin/CLE/GLE).
    "External" means different cache (struct), not necessarily different cluster. -/
structure rfe {e₁ e₂ : Event n}
    (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : Prop where
  write : e₁.isWrite
  read : e₂.isRead
  sameAddr : e₁.addr = e₂.addr
  diffCache : e₁.struct ≠ e₂.struct
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  cache₁ : e₁.isClusterCache
  cache₂ : e₂.isClusterCache
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  readsFrom : Behaviour.readsFrom.cases write read lin₁ lin₂ hknow_dir_access
  /-- Protocol causal ordering: the reader finishes strictly after the writer.
      Validated by Murphi model checking. -/
  event_oEnd_lt : Event.oEnd n e₁ < Event.oEnd n e₂
  /-- CompoundLin events are ordered (forward, equal, or reverse) through CLE bridge. -/
  cmpLin_ordered : CmpLinOrdering lin₁.compoundLin lin₂.compoundLin

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
    (same_cle : w₁_cmpLin.cle = w₂_cmpLin.cle)
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

/-- CO: Coherence ordering between two writes.
    Parameterized by linearization evidence (provides compoundLin/CLE/GLE). -/
structure co {e₁ e₂ : Event n}
    (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : Prop where
  write₁ : e₁.isWrite
  write₂ : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  in_b₁ : e₁ ∈ b
  in_b₂ : e₂ ∈ b
  cache₁ : e₁.isClusterCache
  cache₂ : e₂.isClusterCache
  notDown₁ : ¬ e₁.down
  notDown₂ : ¬ e₂.down
  comm : co.ordering lin₁ lin₂
  /-- Protocol causal ordering: the overwriter finishes strictly after the overwritee.
      Validated by Murphi model checking. -/
  event_oEnd_lt : Event.oEnd n e₁ < Event.oEnd n e₂
  /-- CompoundLin events are ordered through CLE bridge. -/
  cmpLin_ordered : CmpLinOrdering lin₁.compoundLin lin₂.compoundLin

abbrev NonLazyPPOi (compound : CompoundProtocol n) (b : Behaviour n) (init : InitialSystemState n) : Prop :=
  ∀ (a₁ a₂ : Event n) (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init a₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init a₂),
    @PPOi n compound b init a₁ a₂ lin₁ lin₂ → a₁.addr ≠ a₂.addr →
    (compound.compoundLinearizationEvent compound.shimAxioms b init a₁
      (compound.linearizationOfEvent b init a₁)).linearizationEvent.OrderedBefore n
    (compound.compoundLinearizationEvent compound.shimAxioms b init a₂
      (compound.linearizationOfEvent b init a₂)).linearizationEvent

theorem Event.oStart_le_oEnd (e : Event n) : Event.oStart n e ≤ Event.oEnd n e :=
  Nat.le_of_lt (Event.oWellFormed n e)

theorem Event.ob_of_lt_lt {e₁ e₂ : Event n} {p : ℕ}
    (h₁ : Event.oEnd n e₁ < p) (h₂ : p < Event.oStart n e₂)
    : e₁.OrderedBefore n e₂ := Nat.lt_trans h₁ h₂


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
    (cle_eq_or_ob : e₁_cmpLin.cle = e₂_cmpLin.cle ∨
        e₁_cmpLin.cle.OrderedBefore n e₂_cmpLin.cle)
  /-- Same cluster, different cache: cluster directory serializes the accesses.
      CLE₁ OB CLE₂ from dir_ordered + NIW (NoInterveningWrites eliminates wrong direction).
      CleLink derived via .ob. -/
  | sameClusDiffCache
    (same_protocol : e₁.sameProtocol n e₂)
    (diff_cache : e₁.struct ≠ e₂.struct)
    (cle_ob : e₁_cmpLin.cle.OrderedBefore n e₂_cmpLin.cle)
  /-- Different cluster, e₁ coherent: e₁ has coherent perms (from reading e_w),
      so e₂'s overwrite triggers a downgrade at e₁'s CACHE.
      The cache downgrade is after e₁ (e₁ OB cache_down), encapsulated by a
      cluster dir event whose oEnd < CLE₂.oEnd.
      CleLink derived via .obEndLt (CLE₁ OB proxy, proxy.oEnd < CLE₂.oEnd). -/
  | diffCluster_coherent
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.cle.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.cle)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, e₁ coherent with evict: e₁ had coherent perms but
      evicted before e₂'s downgrade arrived. The downgrade goes to the cluster
      directory after the evict. Proxy is the evict directory event.
      CleLink derived via .obEndLt. -/
  | diffCluster_evict
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.cle.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.cle)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, e₁ non-coherent: e₁ doesn't have coherent perms,
      so e₂'s downgrade goes directly to e₁'s CLUSTER DIRECTORY.
      Proxy is the cluster dir downgrade event.
      CleLink derived via .obEndLt. -/
  | diffCluster_noncoherent
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (cle₁_ob_p : e₁_cmpLin.cle.OrderedBefore n p)
    (p_lt_cle₂ : Event.oEnd n p < Event.oEnd n e₂_cmpLin.cle)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Different cluster, RF cross-cluster: e_w at e₂'s cluster, RF gives
      proxy p at e_w's cluster INSIDE CLE₁ (from encapDirRelation) and OB CLE₂.
      CleLink derived via .encapOb (p inside CLE₁, p OB CLE₂). -/
  | diffCluster_rfCrossCluster
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (p_inside_cle₁ : p.EncapsulatedBy n e₁_cmpLin.cle)
    (p_ob_cle₂ : p.OrderedBefore n e₂_cmpLin.cle)
  /-- Different cluster, RF cross-cluster with gcacheEncap/noGlobalCache:
      proxy p OB CLE₂ and p finishes before CLE₁ (p.oEnd < CLE₁.oEnd).
      CleLink derived via .obFinishBefore. -/
  | diffCluster_rfFinishBefore
    (diff_protocol : ¬ e₁.sameProtocol n e₂)
    (p : Event n)
    (p_ob_cle₂ : p.OrderedBefore n e₂_cmpLin.cle)
    (p_lt_cle₁ : Event.oEnd n p < Event.oEnd n e₁_cmpLin.cle)
    (h_p_isdir : p.isDirectoryEvent)
  /-- Same CLE: both events share the same CLE. -/
  | sameCLE
    (cle_eq : e₁_cmpLin.cle = e₂_cmpLin.cle)

/-- fr: From-reads (rf⁻¹ ; co⁺).
    Parameterized by linearization evidence (provides compoundLin/CLE/GLE). -/
structure fr {e₁ e₂ : Event n}
    (lin₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₁)
    (lin₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init e₂)
    : Prop where
  read : e₁.isRead
  write : e₂.isWrite
  sameAddr : e₁.addr = e₂.addr
  in_b₁ : e₁ ∈ b
  cache₁ : e₁.isClusterCache
  notDown₁ : ¬ e₁.down
  in_b₂ : e₂ ∈ b
  cache₂ : e₂.isClusterCache
  notDown₂ : ¬ e₂.down
  hknow_dir_access : CompoundProtocol.globalLinearizationEventOfRequest.wrapper (n := n)
  /-- rf⁻¹ ; co⁺ decomposition: e₁ reads from e_w at some communication level.
      The co chain uses existential lin for intermediate writes (internal to FR). -/
  comm : ∃ (e_w : Event n) (e_w_write : e_w.isWrite)
    (e_w_lin : CompoundProtocol.globalLinearizationEventOfRequest compound b init e_w),
    e_w.addr = e₁.addr ∧
    Behaviour.readsFrom.cases e_w_write read e_w_lin lin₁ hknow_dir_access ∧
    NoInterveningWrites e_w_write read e_w_lin lin₁ hknow_dir_access ∧
    Relation.TransGen (fun ew₁ ew₂ => ∃ (l₁ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₁)
      (l₂ : CompoundProtocol.globalLinearizationEventOfRequest compound b init ew₂), co l₁ l₂) e_w e₂ ∧
    e_w ∈ b ∧ e_w.isClusterCache ∧ ¬ e_w.down
  /-- Protocol causal ordering: the later writer finishes strictly after the reader.
      Validated by Murphi model checking. -/
  event_oEnd_lt : Event.oEnd n e₁ < Event.oEnd n e₂
  /-- CompoundLin events are ordered through CLE bridge. -/
  cmpLin_ordered : CmpLinOrdering lin₁.compoundLin lin₂.compoundLin
  -- FrOrdering is DERIVED by fr_ordering_holds theorem (not carried as a field).
  -- This ensures the ordering evidence is proven, not assumed.

end Herd
