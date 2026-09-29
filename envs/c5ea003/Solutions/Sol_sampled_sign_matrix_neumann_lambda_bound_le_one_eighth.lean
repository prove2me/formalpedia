-- Prove2me | solution 1 for sampled_sign_matrix_neumann_lambda_bound_le_one_eighth
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:37:45.737321+00:00
-- url     : https://prove2.me/submissions/7e8776bd-f611-4aaa-ab09-e87f71eff225

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution (C₀ : ℝ) :
    C₀ * Real.rpow (max 1 ((8 * C₀) ^ 2)) (-((1 : ℝ) / 2)) ≤
      (1 : ℝ) / 8 := by
  set B := max (1:ℝ) ((8 * C₀)^2) with hB
  have hB1 : (1:ℝ) ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hrpow : Real.rpow B (-((1:ℝ)/2)) = (Real.sqrt B)⁻¹ := by
    rw [show Real.rpow B (-((1:ℝ)/2)) = B ^ (-((1:ℝ)/2)) from rfl,
        Real.rpow_neg (le_of_lt hBpos), ← Real.sqrt_eq_rpow]
  rw [hrpow]
  by_cases hC0 : 0 < C₀
  · have hsqrtB : 8 * C₀ ≤ Real.sqrt B := by
      have h8 : (8 * C₀)^2 ≤ B := le_max_right _ _
      have hh := Real.sqrt_le_sqrt h8
      rwa [Real.sqrt_sq (by positivity)] at hh
    have hinv : (Real.sqrt B)⁻¹ ≤ (8 * C₀)⁻¹ := by
      gcongr
    calc C₀ * (Real.sqrt B)⁻¹
        ≤ C₀ * (8 * C₀)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hinv (le_of_lt hC0)
      _ = 1/8 := by field_simp
  · rw [not_lt] at hC0
    have hnn : 0 ≤ (Real.sqrt B)⁻¹ := by positivity
    nlinarith [hnn, hC0]
