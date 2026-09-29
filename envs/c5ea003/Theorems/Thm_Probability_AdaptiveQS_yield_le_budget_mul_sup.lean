-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_yield_le_budget_mul_sup
-- name    : Probability.AdaptiveQS.yield_le_budget_mul_sup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:55:34.726007+00:00
-- url     : https://prove2.me/theorems/ba05fa4e-0488-4793-9e67-b48513e9fc37
-- title:
--   The realised oracle bound.
-- statement:
--   **The realised oracle bound.**  Every allocation of a budget `B` over nonnegative
--   sieve lengths yields at most `B ·` (largest rate).  The measured `+74.8%` headroom is
--   therefore capped by the rate spread and by nothing else — no adaptive rule can exceed it.
--
--   ```lean
--   theorem Probability.AdaptiveQS.yield_le_budget_mul_sup{s : Finset ι} {r ℓ : ι → ℝ} {i₀ : ι}
--       (hmax : ∀ i ∈ s, r i ≤ r i₀) (hℓ : ∀ i ∈ s, 0 ≤ ℓ i) {B : ℝ} (hB : ∑ i ∈ s, ℓ i = B) :
--       yieldOf s r ℓ ≤ r i₀ * B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSAllocation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSAllocation.lean#L295

-- Thm stub generated from Probability/AdaptiveQSAllocation.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Why inverse-rate reallocation must lose, and why the floor clip is load-bearing

Experiment 559 (round-73 #2, `ADAPT-NULL-EQUALIZER / SKIP-FLIP-WINS`) measured an
adaptive quadratic sieve in which a cheap quadratic-residue dial predicts the
per-target relation *rate* well (Spearman `0.739`, oracle dial `0.778`,
`FB100 = 0.835`), and then reallocated sieve length in inverse proportion to the
predicted rate.  The reallocation **lost**: `-17.6%` total yield with a floor clip
in place, and a catastrophic `-146.7%` with the clip removed, while a
*concentrator* that pushes budget towards the high-rate targets gained `+8.6%`
and the realised oracle bound sat `+74.8%` above the baseline.

This file explains all four numbers as one exact theorem, at the level of the
allocation model itself: **no calibration error is involved, the sign of the
inverse-rate policy is forced.**

The model.  A budget `B` of sieve length is split over targets `i ∈ s` with
positive relation rates `r i` (relations per unit of sieve length); an allocation
`ℓ` yields `yieldOf s r ℓ = ∑ i ∈ s, r i * ℓ i`.

Main results.

* `card_sq_le_sum_mul_sum_inv`, `card_sq_lt_sum_mul_sum_inv` — the AM–HM core,
  with the strict form: `n² ≤ (∑ r)(∑ r⁻¹)`, strictly as soon as two rates differ.
  Proved by pairwise symmetrisation over `s ×ˢ s`, not quoted.
* `invRate_yield_le_uniform_yield` / `invRate_yield_lt_uniform_yield` — **the
  inverse-rate policy loses, always.**  Its yield is `B ·` harmonic mean of the
  rates, the uniform baseline is `B ·` arithmetic mean, and the loss is strict
  whenever the dial has anything to say (two rates differ).  So a dial with
  *perfect* calibration would still lose under this policy: the `-17.6%` is a
  property of the reallocation rule, not of the predictor.
* `clipYield_eq`, `clipYield_mono`, `clipYield_strictMono` — **the floor clip is
  load-bearing and monotonically so.**  Interpolating the clipped policy
  `ℓ i = f + (B - n f) (r i)⁻¹ / ∑ r⁻¹` in the floor `f`, the yield is affine and
  *strictly increasing* in `f`; `f = 0` is the unclipped policy and `f = B / n`
  is the uniform baseline.  Removing the clip is exactly moving down this line,
  which is why unclipped is worse than clipped and clipped is worse than uniform.
* `concentrator_yield_ge_uniform_yield` — pushing the whole budget onto a
  maximal-rate target beats uniform: the correct sign is the opposite one.
* `yield_le_budget_mul_sup` — the realised oracle bound: *every* admissible
  allocation is capped by `B ·` (max rate), so the measured `+74.8%` headroom is
  bounded by the rate spread and by nothing else.
* `oracle_gap_eq_budget_mul_sup_sub_mean` — the headroom of the uniform baseline
  is exactly `B (max r - mean r)`.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*}

/-! ## The allocation model -/





/-! ## The AM–HM core, proved by pairwise symmetrisation -/








/-! ## The yields of the two policies -/






/-! ## The floor clip is load-bearing -/






/-! ## The concentrator and the oracle bound -/

theorem Probability.AdaptiveQS.yield_le_budget_mul_sup{s : Finset ι} {r ℓ : ι → ℝ} {i₀ : ι}
    (hmax : ∀ i ∈ s, r i ≤ r i₀) (hℓ : ∀ i ∈ s, 0 ≤ ℓ i) {B : ℝ} (hB : ∑ i ∈ s, ℓ i = B) :
    yieldOf s r ℓ ≤ r i₀ * B := by sorry
