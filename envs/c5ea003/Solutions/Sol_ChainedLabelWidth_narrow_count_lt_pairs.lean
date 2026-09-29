-- Prove2me | solution 1 for ChainedLabelWidth.narrow_count_lt_pairs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:10:22.536046+00:00
-- url     : https://prove2.me/submissions/1e0707cd-597c-4c0c-8bb4-3c40647863a8

-- Sol generated from Applications/ChainedLabelWidth.lean
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





/-! ## The audited instance: `36` genuine pairs, `18` reported labels -/







open ChainedLabelWidth in
theorem solution{A B M : ℕ} (hMB : M < B) (hA : 2 ≤ A) :
    M * (A - 1) + B < A * B := by
  have h1 : M * (A - 1) + 1 * (A-1) ≤ (B-1) * (A - 1) + 1 * (A-1) := by
    have : M * (A-1) ≤ (B-1) * (A-1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : (B - 1) * (A - 1) + 1 * (A - 1) = B * (A - 1) := by
    have : 0 < B := by omega
    cases B with
    | zero => omega
    | succ b => simp; ring
  have h3 : B * (A - 1) + B = A * B := by
    cases A with
    | zero => omega
    | succ a => simp; ring
  omega
