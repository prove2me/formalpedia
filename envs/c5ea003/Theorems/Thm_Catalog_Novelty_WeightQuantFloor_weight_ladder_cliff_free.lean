-- Prove2me | Theorems.Thm_Catalog_Novelty_WeightQuantFloor_weight_ladder_cliff_free
-- name    : Catalog.Novelty.WeightQuantFloor.weight_ladder_cliff_free
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:17:36.851894+00:00
-- url     : https://prove2.me/theorems/7a316201-1197-4c47-8be5-61cb7cf277fa
-- title:
--   No cliff, anywhere.
-- statement:
--   **No cliff, anywhere.**  A "cliff" on this axis would be a per-bit
--   degradation factor of `4` or worse (the quadratic-curvature ceiling; see
--   `Novelty.QuantCurvatureNoFloor`).  No pair of rungs of the weight ladder reaches
--   it — in sharp contrast with the cache-key axis, where the degradation factor
--   between 8-bit and 5-bit keys is unbounded (see
--   `Novelty.SelectionContentPrecision`).
--
--   ```lean
--   theorem Catalog.Novelty.WeightQuantFloor.weight_ladder_cliff_free{r s : Rung} (hr : r ∈ ladder) (hs : s ∈ ladder)
--       (h : s.tenthBits < r.tenthBits) :
--       excess s ^ 10 < 4 ^ (r.tenthBits - s.tenthBits) * excess r ^ 10 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightQuantFloorLadder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightQuantFloorLadder.lean#L114

-- Thm stub generated from Novelty/WeightQuantFloorLadder.lean
import Mathlib
import Definitions.Def_Novelty_WeightQuantFloorLadder

/-!
# The weight-quantisation ladder: a geometric law with no bit-width floor (NET-95)

This file formalises the *quantitative* content of the NET-95 measurement
**THE-WEIGHT-FLOOR-COLLAPSED**.  A 7B model was evaluated with `llama-perplexity`
(ctx = 2048, 8 threads, a 250 KB held-out wikitext slice) at seven weight
precisions:

| rung   | bpw  | PPL    |
|--------|------|--------|
| fp16   | 16   | 6.9825 |
| q8_0   | 8.5  | 6.9781 |
| q6_k   | 6.6  | 7.0006 |
| q5_k_m | 5.5  | 7.0427 |
| q4_k_m | 4.8  | 7.1093 |
| q3_k_m | 3.9  | 7.2758 |
| q2_k   | 2.6  | 8.1105 |

The narrative claim attached to this table is that the "sub-6-bit floor" reported
for a toy round-to-nearest quantiser (NET-52) is *not* a law about bit widths:
at scale, with calibration-aware k-quants, the excess perplexity
`E(b) = PPL(b) - PPL(fp16)` is a smooth, convex, purely geometric function of the
bit width, with **no cliff anywhere** between 6.6 and 2.6 bpw.

Everything below is proved from the measured numbers as exact rationals.

## Main results

* `weight_ladder_geometric_band` — the *one-parameter law*.  For **every** pair of
  rungs of the k-quant ladder (not merely adjacent ones), the excess perplexity
  ratio per bit removed lies in the band `[5/2, 3]`:
  `(5/2)^k · E(r)^10 ≤ E(s)^10 ≤ 3^k · E(r)^10`, where `k` is the bit-width gap in
  tenths of a bit.  Ten inequalities, all tight enough that neither endpoint of
  the band can be moved much (the extreme observed per-bit rates are `2.539` and
  `2.982`).
* `weight_ladder_cliff_free` — no pair of rungs exhibits a per-bit degradation
  factor of `4` or more: the ladder is cliff-free in the strong, all-pairs sense.
* `weight_ladder_convex` — `E` is a strictly convex function of the bit width on
  the measured points (all ten triples of secant slopes are increasing), and
  `weight_ladder_strictAnti` — `E` is strictly decreasing in bit width.
* `scorecard_P1`, `scorecard_P2_refuted`, `scorecard_P3_refuted`,
  `q8_0_within_noise` — the pre-registered predictions, adjudicated.
* `geometric_closure` / `excess_le_of_bits_below` — the abstract reason a
  geometric band forbids a floor: a per-bit multiplicative bound propagates to a
  bound `m ^ k` after `k` further bits are removed, so degradation can never blow
  up at a finite bit width.
* `one_bit_below_q2k_stays_under_fifty_percent` — the conditional extrapolation:
  if the fitted upper rate `m = 3` persists below 2.6 bpw, then even at 1.6 bpw
  the relative excess is still under the `+50%` "undeployable" threshold.
-/

open Catalog.Novelty.WeightQuantFloor

/-! ## 1. The measured ladder -/








/-! ## 2. The one-parameter geometric law -/

theorem Catalog.Novelty.WeightQuantFloor.weight_ladder_cliff_free{r s : Rung} (hr : r ∈ ladder) (hs : s ∈ ladder)
    (h : s.tenthBits < r.tenthBits) :
    excess s ^ 10 < 4 ^ (r.tenthBits - s.tenthBits) * excess r ^ 10 := by sorry
