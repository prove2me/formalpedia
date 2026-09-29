-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.tendsto_lamR_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:35:04.508761+00:00
-- url     : https://prove2.me/submissions/b66ed9fa-d881-4e2c-84e0-262419729f3f

-- Sol generated from Probability/RefractoryGrowthRate.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Definitions.Def_Probability_RefractoryGrowthRate
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_charFn_strictMonoOn
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






theorem lamR_mem_Icc (r : ℕ) : lamR r ∈ Set.Icc (1 : ℝ) 2 :=
  (exists_charFn_eq_one r).choose_spec.1

theorem charFn_lamR (r : ℕ) : charFn r (lamR r) = 1 :=
  (exists_charFn_eq_one r).choose_spec.2









/-! ## 2.  Two-sided bounds on the capacity -/



/-! ## 3.  The growth rate -/






/-! ## 4.  Monotonicity in the refractory period -/




/-! ## 5.  Numerics for the two-bin refractory period -/




open Catalog.Probability.NeuralCoding.Temporal in
theorem solution: Tendsto (fun r : ℕ => lamR r) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have hele : e ≤ ε := min_le_left _ _
  -- for `r` large, `(1 + e)^r * e > 1`, so `λ_r < 1 + e`
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / e ^ 2)
  refine ⟨R + 1, fun r hr => ?_⟩
  have hrpos : (1 : ℝ) / e ^ 2 < r := by
    have : (R : ℝ) ≤ r := by exact_mod_cast (by omega : R ≤ r)
    linarith
  have hbig : (1 : ℝ) < charFn r (1 + e) := by
    have hpow : (1 : ℝ) + r * e ≤ (1 + e) ^ r := by
      have := one_add_mul_le_pow (a := e) (by linarith) r
      linarith
    have hkey : 1 < (1 + (r : ℝ) * e) * e := by
      have hr2 : 1 / e ^ 2 < (r : ℝ) := hrpos
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < e ^ 2)] at hr2
      nlinarith [he0]
    have hcf : charFn r (1 + e) = (1 + e) ^ r * e := by simp [charFn]
    rw [hcf]
    have : (1 + (r : ℝ) * e) * e ≤ (1 + e) ^ r * e := by
      exact mul_le_mul_of_nonneg_right hpow he0.le
    linarith
  have hlt : lamR r < 1 + e := by
    have hmono := charFn_strictMonoOn r
    have h1 : (1 : ℝ) ≤ lamR r := (lamR_mem_Icc r).1
    have h2 : (1 : ℝ) ≤ 1 + e := by linarith
    have : charFn r (lamR r) < charFn r (1 + e) := by rw [charFn_lamR r]; exact hbig
    exact (hmono.lt_iff_lt h1 h2).mp this
  have hge1 : (1 : ℝ) ≤ lamR r := (lamR_mem_Icc r).1
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith
