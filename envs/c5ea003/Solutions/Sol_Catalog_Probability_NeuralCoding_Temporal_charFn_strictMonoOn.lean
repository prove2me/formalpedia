-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.charFn_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:27:21.128788+00:00
-- url     : https://prove2.me/submissions/f51b94d7-e81a-43b7-b07d-4ccf78a913af

-- Sol generated from Probability/RefractoryGrowthRate.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Definitions.Def_Probability_RefractoryGrowthRate
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
theorem solution(r : ℕ) : StrictMonoOn (charFn r) (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have h1 : x ^ r ≤ y ^ r := pow_le_pow_left₀ hx0 hxy.le r
  have hyr : (0 : ℝ) < y ^ r := pow_pos hy0 r
  have h2 : x - 1 < y - 1 := by linarith
  calc charFn r x = x ^ r * (x - 1) := rfl
    _ ≤ y ^ r * (x - 1) := by
        exact mul_le_mul_of_nonneg_right h1 (by linarith)
    _ < y ^ r * (y - 1) := by exact mul_lt_mul_of_pos_left h2 hyr
    _ = charFn r y := rfl
