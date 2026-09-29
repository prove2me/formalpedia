-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.logb_lamR_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:34:59.481668+00:00
-- url     : https://prove2.me/submissions/370de743-6c13-4107-9749-baff375df24a

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

theorem lamR_spec (r : ℕ) : (lamR r) ^ r * (lamR r - 1) = 1 := charFn_lamR r

theorem one_lt_lamR (r : ℕ) : 1 < lamR r := by
  rcases lt_or_eq_of_le (lamR_mem_Icc r).1 with h | h
  · exact h
  · exfalso
    have := lamR_spec r
    rw [← h] at this
    norm_num at this


theorem lamR_pos (r : ℕ) : 0 < lamR r := lt_trans one_pos (one_lt_lamR r)





/-! ## 2.  Two-sided bounds on the capacity -/



/-! ## 3.  The growth rate -/






/-! ## 4.  Monotonicity in the refractory period -/




/-! ## 5.  Numerics for the two-bin refractory period -/

/-- `1.46 < λ_2 < 1.47`: a two-bin refractory period allows about `0.5515` bits per
bin, strictly below the `2/3` bound of `temporal_rate_two_le`. -/
theorem lamR_two_bounds : 1.46 < lamR 2 ∧ lamR 2 < 1.47 := by
  have hmono := charFn_strictMonoOn 2
  have hlam : (1 : ℝ) ≤ lamR 2 := (lamR_mem_Icc 2).1
  constructor
  · have hlow : charFn 2 1.46 < charFn 2 (lamR 2) := by
      rw [charFn_lamR 2]; norm_num [charFn]
    exact (hmono.lt_iff_lt (by norm_num) hlam).mp hlow
  · have hhigh : charFn 2 (lamR 2) < charFn 2 1.47 := by
      rw [charFn_lamR 2]; norm_num [charFn]
    exact (hmono.lt_iff_lt hlam (by norm_num)).mp hhigh



open Catalog.Probability.NeuralCoding.Temporal in
theorem solution: Real.logb 2 (lamR 2) < 2 / 3 := by
  have h : lamR 2 < 1.47 := lamR_two_bounds.2
  have hpos : (0 : ℝ) < lamR 2 := lamR_pos 2
  have h1 : Real.logb 2 (lamR 2) < Real.logb 2 1.47 :=
    Real.logb_lt_logb (by norm_num) hpos h
  have h2 : Real.logb 2 1.47 < 2 / 3 := by
    have hcube : Real.log ((1.47 : ℝ) ^ (3 : ℕ)) < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hcube
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb, div_lt_iff₀ hl2]
    push_cast at hcube
    linarith
  linarith
