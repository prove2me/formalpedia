-- Prove2me | Theorems.Thm_ChainedLabelWidth_chain_image_eq_range
-- name    : ChainedLabelWidth.chain_image_eq_range
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:55.480888+00:00
-- url     : https://prove2.me/theorems/b4186726-5c1f-43cb-97ae-39ea0715110c
-- title:
--   Under a narrow frame `M ≤ B` the image is exactly the interval
-- statement:
--   Under a **narrow** frame `M ≤ B` the image is exactly the interval
--   `[0, M * (A - 1) + B)`.
--
--   ```lean
--   theorem ChainedLabelWidth.chain_image_eq_range{A B M : ℕ} (hMB : M ≤ B) (hA : 1 ≤ A) :
--       (range A ×ˢ range B).image (fun p => chain M p.1 p.2)
--         = range (M * (A - 1) + B) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ChainedLabelWidth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ChainedLabelWidth.lean#L92

-- Thm stub generated from Applications/ChainedLabelWidth.lean
import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
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

open ChainedLabelWidth

open Finset



/-! ## Width criterion: injectivity -/




/-! ## Exact label counts -/

theorem ChainedLabelWidth.chain_image_eq_range{A B M : ℕ} (hMB : M ≤ B) (hA : 1 ≤ A) :
    (range A ×ˢ range B).image (fun p => chain M p.1 p.2)
      = range (M * (A - 1) + B) := by sorry
