-- Prove2me | Definitions.Def_Probability_AdaptiveQSAllocation
-- name    : Probability_AdaptiveQSAllocation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:59.579734+00:00
-- url     : https://prove2.me/theorems/bf49883b-b72e-47d8-b52d-f49aa2e98e37
-- title:
--   Aether Catalog definitions — Probability_AdaptiveQSAllocation
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AdaptiveQSAllocation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AdaptiveQSAllocation.lean by skeleton subtraction
import Mathlib
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

namespace Probability.AdaptiveQS

open Finset

variable {ι : Type*}

/-! ## The allocation model -/

/-- Total yield of a sieve-length allocation `ℓ` against per-target relation rates `r`. -/
def yieldOf (s : Finset ι) (r ℓ : ι → ℝ) : ℝ := ∑ i ∈ s, r i * ℓ i

/-- The uniform baseline: every target gets `B / |s|` of the budget. -/
noncomputable def uniformAlloc (s : Finset ι) (B : ℝ) : ι → ℝ := fun _ => B / s.card

/-- The measured adaptive policy: sieve length in inverse proportion to the predicted
rate, renormalised to the budget `B`. -/
noncomputable def invRateAlloc (s : Finset ι) (r : ι → ℝ) (B : ℝ) : ι → ℝ :=
  fun i => B * (r i)⁻¹ / ∑ j ∈ s, (r j)⁻¹

/-- The clipped inverse-rate policy with floor `f`: every target is guaranteed `f`
units of sieve length, and the remaining budget is split in inverse proportion to
the rate.  `f = 0` is the unclipped policy, `f = B / |s|` is the uniform baseline. -/
noncomputable def clipInvAlloc (s : Finset ι) (r : ι → ℝ) (B f : ℝ) : ι → ℝ :=
  fun i => f + (B - s.card * f) * (r i)⁻¹ / ∑ j ∈ s, (r j)⁻¹

/-! ## The AM–HM core, proved by pairwise symmetrisation -/








/-! ## The yields of the two policies -/






/-! ## The floor clip is load-bearing -/






/-! ## The concentrator and the oracle bound -/

/-- The rate-concentrator: the whole budget on a single (maximal-rate) target. -/
noncomputable def concAlloc [DecidableEq ι] (i₀ : ι) (B : ℝ) : ι → ℝ :=
  fun i => if i = i₀ then B else 0





end Probability.AdaptiveQS


