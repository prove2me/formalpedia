-- Prove2me | solution 2 for linear_neumann_correction_lambda_bound_le_one_eighth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:31.24324+00:00
-- url     : https://prove2.me/submissions/a1727c94-93be-4c84-887b-9748425f50f3

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    (C₁ : ℝ) (hC₁ : 0 < C₁) :
    C₁ * Real.rpow (max 1 (8 * C₁)) (-1) ≤ (1 : ℝ) / 8 := by
  rw [Real.rpow_eq_pow, Real.rpow_neg_one]
  have hmax_pos : 0 < max 1 (8 * C₁) :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (8 * C₁))
  have hscale_pos : 0 < 8 * C₁ := by positivity
  have hscale_le : 8 * C₁ ≤ max 1 (8 * C₁) := le_max_right 1 (8 * C₁)
  have hinv_le : (max 1 (8 * C₁))⁻¹ ≤ (8 * C₁)⁻¹ :=
    (inv_le_inv₀ hmax_pos hscale_pos).mpr hscale_le
  calc
    C₁ * (max 1 (8 * C₁))⁻¹ ≤ C₁ * (8 * C₁)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv_le hC₁.le
    _ = (1 : ℝ) / 8 := by
      field_simp [hC₁.ne']
