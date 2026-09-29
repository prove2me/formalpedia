-- Prove2me | Definitions.Def_Applications_ChainedLabelWidth
-- name    : Applications_ChainedLabelWidth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:23.240171+00:00
-- url     : https://prove2.me/theorems/0427062a-e3b3-4d39-8d9d-d86c793e9027
-- title:
--   Aether Catalog definitions — Applications_ChainedLabelWidth
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ChainedLabelWidth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ChainedLabelWidth.lean by skeleton subtraction
import Mathlib
/-
# Chained integer label encodings: the width criterion

## Context (FACT round-29 #2, "THE-ORIGINAL-STANDS")

Experimental pipelines routinely build a *joint label* for a pair of discrete
codes `(a, b)` by chaining them into a single integer

  `pj = a * M + b`

for some fixed decimal *frame* `M` (in the programme: `M = 10000`, `M = 100`,
`M = 10`).  This is a bijection onto its image **iff the frame is at least as
wide as the alphabet of the inner code**.  When the frame is too narrow the
encoding silently *merges* distinct pairs, and every downstream statistic
(label count, label entropy, mutual information) is computed on a coarsening of
the intended population rather than on the population itself.

This file is the arithmetic half of the reconciliation.  It proves:

* `chain_inj_of_lt` / `chainPair_injective` — width-valid chaining is injective;
* `chain_collision_of_frame_lt` — a *narrow* frame always produces an explicit
  collision, so the failure is structural, not data-dependent;
* `card_chain_image_of_width` — a wide frame realises the full `A * B` labels;
* `card_chain_image_of_narrow` — the **exact** label count `M * (A - 1) + B`
  for a narrow frame `M ≤ B`; the image is a full interval;
* `collapse_36_to_18` — the audited instance: `4 × 9 = 36` genuine pairs are
  reported as `18` labels under a `·3` frame (the shape of the retracted
  rebuild reading), while a width-valid frame keeps all `36`.

Nothing here is `decide`-only: the counting theorems are proved for all
`A, B, M` by an explicit interval identification, and the numeric instances are
corollaries of them.
-/

namespace ChainedLabelWidth

open Finset

/-- Chained integer label: outer code `a`, inner code `b`, decimal frame `M`. -/
def chain (M a b : ℕ) : ℕ := a * M + b


/-! ## Width criterion: injectivity -/




/-! ## Exact label counts -/





/-! ## The audited instance: `36` genuine pairs, `18` reported labels -/




/-- A width-check predicate an audit can actually run: the frame must dominate
the inner alphabet. -/
def WidthOK (B M : ℕ) : Prop := B ≤ M


end ChainedLabelWidth


