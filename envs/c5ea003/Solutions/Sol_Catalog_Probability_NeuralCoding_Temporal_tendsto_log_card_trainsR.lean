-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.tendsto_log_card_trainsR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:40:48.000004+00:00
-- url     : https://prove2.me/submissions/b9f4e9f6-1cf8-4248-8081-0368dcebab7e

-- Sol generated from Probability/RefractoryGrowthRate.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Definitions.Def_Probability_RefractoryGrowthRate
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_log_card_trainsR_bounds
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The exact growth rate of refractory temporal codes

`RefractoryGeneralized.lean` proved the combinatorial half of the refractory
capacity problem: the number `c_r(n) = (trainsR r n).card` of admissible spike
trains in a window of `n` bins, for a neuron with an `r`-bin refractory period,
satisfies

`c_r(n) = n + 1` for `n ≤ r`,   `c_r(n + r + 1) = c_r(n + r) + c_r(n)`,

whose characteristic equation is `x ^ (r + 1) = x ^ r + 1`.  Only crude rate
bounds (`c_r((r+1)m) ≤ (2^r + 1)^m`) were available there.

This file settles the *analytic* half: the exponential growth rate of `c_r` is
exactly the root of the characteristic equation.

## Main definitions

* `lamR r` : the unique real `x ≥ 1` with `x ^ r * (x - 1) = 1`, equivalently
  `x ^ (r + 1) = x ^ r + 1`.  It lies in `(1, 2]`.

## Main results

* `lamR_unique` : uniqueness of the root, and `lamR_one_eq_goldenRatio`,
  `lamR_zero` : `λ_0 = 2`, `λ_1 = φ`.
* `card_trainsR_le_lamR`, `lamR_le_card_trainsR` : the two-sided bound
  `λ_r ^ n ≤ λ_r ^ r * c_r(n)` and `c_r(n) ≤ (r + 1) * λ_r ^ n`.
* `tendsto_log_card_trainsR` : `log c_r(n) / n → log λ_r`;
  `tendsto_card_trainsR_rpow` : `c_r(n) ^ (1/n) → λ_r`;
  `tendsto_temporal_rate` : the bit rate `log₂ c_r(n) / n → log₂ λ_r`.
* `lamR_strictAnti` : `λ_{r+1} < λ_r` — a longer refractory period strictly
  lowers the rate — and `tendsto_lamR_one` : `λ_r → 1`, so the rate tends to `0`.
* `lamR_two_bounds` : `1.46 < λ_2 < 1.47`, hence a rate of about `0.55` bits per
  bin, well below the `2/3` upper bound proved earlier.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Filter Topology

/-! ## 1.  The characteristic root -/
















/-! ## 2.  Two-sided bounds on the capacity -/



/-! ## 3.  The growth rate -/






/-! ## 4.  Monotonicity in the refractory period -/




/-! ## 5.  Numerics for the two-bin refractory period -/




open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(r : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((trainsR r n).card) / n) atTop
      (𝓝 (Real.log (lamR r))) := by
  set L := Real.log (lamR r) with hL
  have hlow : Tendsto (fun n : ℕ => L - ((r : ℝ) * L) / (n : ℝ)) atTop (𝓝 L) := by
    have h0 : Tendsto (fun n : ℕ => ((r : ℝ) * L) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using tendsto_const_nhds.sub h0
  have hhigh : Tendsto (fun n : ℕ => L + Real.log ((r : ℝ) + 1) / (n : ℝ)) atTop (𝓝 L) := by
    have h0 : Tendsto (fun n : ℕ => Real.log ((r : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using tendsto_const_nhds.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (log_card_trainsR_bounds r n).1
    have hEq : L - ((r : ℝ) * L) / (n : ℝ) = ((n : ℝ) * L - (r : ℝ) * L) / n := by
      field_simp
    rw [hEq]
    gcongr
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (log_card_trainsR_bounds r n).2
    have hEq : L + Real.log ((r : ℝ) + 1) / (n : ℝ)
        = (Real.log ((r : ℝ) + 1) + (n : ℝ) * L) / n := by
      field_simp; ring
    rw [hEq]
    gcongr
