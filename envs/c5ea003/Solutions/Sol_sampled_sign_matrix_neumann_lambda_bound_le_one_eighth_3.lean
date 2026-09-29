-- Prove2me | solution 3 for sampled_sign_matrix_neumann_lambda_bound_le_one_eighth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:25.099349+00:00
-- url     : https://prove2.me/submissions/626ab1b6-5465-4fa5-85e3-f026f68230ee

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution (C₀ : ℝ) :
    C₀ * Real.rpow (max 1 ((8 * C₀) ^ 2)) (-((1 : ℝ) / 2)) ≤
      (1 : ℝ) / 8 := by
  by_cases hC₀ : C₀ ≤ 0
  · have hbase_pos : 0 < max 1 ((8 * C₀) ^ 2) :=
      lt_of_lt_of_le zero_lt_one (le_max_left 1 ((8 * C₀) ^ 2))
    have hrpow_nonneg :
        0 ≤ Real.rpow (max 1 ((8 * C₀) ^ 2)) (-((1 : ℝ) / 2)) := by
      rw [Real.rpow_eq_pow]
      exact Real.rpow_nonneg hbase_pos.le _
    have hprod_nonpos :
        C₀ * Real.rpow (max 1 ((8 * C₀) ^ 2)) (-((1 : ℝ) / 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC₀ hrpow_nonneg
    linarith
  · have hC₀_pos : 0 < C₀ := lt_of_not_ge hC₀
    by_cases hsmall : 8 * C₀ ≤ 1
    · have hsquare_le : (8 * C₀) ^ 2 ≤ (1 : ℝ) := by nlinarith
      rw [max_eq_left hsquare_le]
      have hC₀_le : C₀ ≤ (1 : ℝ) / 8 := by linarith
      simpa [Real.rpow_eq_pow] using hC₀_le
    · have hlarge : 1 ≤ 8 * C₀ := le_of_not_ge hsmall
      have hsquare_ge : (1 : ℝ) ≤ (8 * C₀) ^ 2 := by nlinarith
      rw [max_eq_right hsquare_ge, Real.rpow_eq_pow]
      rw [Real.rpow_neg (sq_nonneg (8 * C₀)) ((1 : ℝ) / 2)]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by linarith : 0 ≤ 8 * C₀)]
      field_simp [hC₀_pos.ne']
      norm_num
