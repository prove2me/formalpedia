-- Prove2me | solution 1 for GeneratorTilt.integral_zOfRatio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T11:17:25.413552+00:00
-- url     : https://prove2.me/submissions/5ce1e447-e8f0-4da2-aac5-7aed886d0d80

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
open GeneratorTilt in
theorem solution : (∫ r in (1:ℝ)..2, zOfRatio r) = Real.sqrt 2 - 1 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hden : (1 : ℝ) - 1 / Real.sqrt 2 ≠ 0 := by
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one (by linarith)]
      exact h2
    intro hc
    linarith
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- `∫₁² r^{-1/2} = 2√2 - 2`
  have hbase : (∫ r in (1:ℝ)..2, 1 / Real.sqrt r) = 2 * Real.sqrt 2 - 2 := by
    have hderiv : ∀ r ∈ Set.uIcc (1:ℝ) 2,
        HasDerivAt (fun x : ℝ => 2 * Real.sqrt x) (1 / Real.sqrt r) r := by
      intro r hr
      rw [Set.uIcc_of_le (by norm_num)] at hr
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
      have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrpos)
      have h := (Real.hasDerivAt_sqrt (ne_of_gt hrpos)).const_mul (2:ℝ)
      convert h using 1
      field_simp
    have hcont : IntervalIntegrable (fun r : ℝ => 1 / Real.sqrt r) MeasureTheory.volume 1 2 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      refine ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn ?_
      intro r hr
      exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hr.1))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    simp
  -- `zOfRatio` is affine in `r ↦ 1/√r`
  have hform : ∀ r : ℝ, zOfRatio r
      = (1 / Real.sqrt r) * (1 / (1 - 1 / Real.sqrt 2))
        - (1 / Real.sqrt 2) * (1 / (1 - 1 / Real.sqrt 2)) := by
    intro r
    rw [zOfRatio]
    field_simp
  have hint1 : IntervalIntegrable (fun r : ℝ => 1 / Real.sqrt r) MeasureTheory.volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    refine ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn ?_
    intro r hr
    exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hr.1))
  rw [intervalIntegral.integral_congr (g := fun r => (1 / Real.sqrt r) * (1 / (1 - 1 / Real.sqrt 2))
      - (1 / Real.sqrt 2) * (1 / (1 - 1 / Real.sqrt 2))) (fun r _ => hform r)]
  rw [intervalIntegral.integral_sub ((hint1.mul_const _)) (intervalIntegrable_const),
    intervalIntegral.integral_mul_const, hbase, intervalIntegral.integral_const]
  -- the remaining identity is `(2√2 - 2 - 1/√2)/(1 - 1/√2) = √2 - 1`
  rw [smul_eq_mul]
  have hne1 : Real.sqrt 2 - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h2)
  field_simp
  linear_combination hsq
