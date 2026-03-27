# Dead Ends — Approaches That Failed and Why

## Adding proxy protocol/isDir to obFinishBefore constructor
**What**: Add `h_p_isdir : p.isDirectoryEvent` and `h_p_prot : p.protocol = l₂.protocol` to obFinishBefore.
**Why it fails**: Composed obFinishBefore(l₁, l₃) has proxy at l₂'s protocol, but constructor needs `p.protocol = l₃.protocol` (the NEW l₂). Since l₂.protocol ≠ l₃.protocol for cross-cluster edges, the field doesn't propagate.

## Adding obFinishBeforeEndLt constructor
**What**: `obFinishBeforeEndLt p₁ p₂ (p₁ OB p₂) (p₁.oEnd < l₁.oEnd) (p₂.oEnd < l₂.oEnd) (diff_prot)`.
**Why it fails**: INCREASES sorry count. Every `cases h₂` and `cases hso₁` needs the new constructor. The diff-protocol direction composes, but same-protocol l₃ OB l₁ doesn't — same blocker as obFinishBefore.

## Per-edge temporal measures for acyclicity
- `e₁.oEnd < e₂.oEnd` (finishesBefore): FAILS for orderAfterDir (CLE past target).
- `e₁ OB e₂` (OrderedBefore on cache events): FAILS for cross-cluster COM.
- `CLE₁ OB CLE₂`: FAILS for same-CLE PPOi (CLE₁ = CLE₂).
- Lex pair (CLE.oEnd, e.oEnd): FAILS for orderAfterDir.
- oEnd-based arguments: FAILS — no contradiction from oEnd alone for orderAfterDir cycles.

## LinLink with EncapBy
**What**: Add EncapBy to LinStep for a richer LinLink.
**Why it fails**: EncapBy DECREASES oStart (going from inner to outer event). No single monotone measure for OB + Encap + EncapBy. All 2-cycles of these DO contradict (via oStart/oEnd chains), but proving general TransGen irreflexivity needs a lex pair or case analysis that I couldn't find.

## Expanding wildcard sorry's without closure plan
**What**: Replace `| _ => sorry` with explicit cases for obEndLt/obFinishBefore/encapObEndLt.
**Why it fails**: Creates MORE sorry's (one per explicit case) without closing any. Only expand when you have a concrete plan to close each expanded case.

## Adding protocol to .ob constructor
**What**: Add `h_same_prot : l₁.protocol = l₂.protocol` to StepOrdering.ob.
**Why it fails**: 42+ `.ob` constructions need updating. Many are in compose_three where the protocol might not be same-cluster (for cross-cluster OB from dir_ordered model over-strength). Big refactor for marginal benefit.

## Composing abstract StepOrderings without edge data
**What**: compose_three takes only StepOrdering h₁ × StepOrdering h₂.
**Why it fails**: StepOrdering loses protocol info from edges. Cross-cluster proxies have unknown temporal ordering. Every hard sorry traces back to this information loss. Fix: keep original edge data (hedge, h_prefix_edge) alongside.
