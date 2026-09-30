-- Prove2me | solution 1 for lean_workbook_plus_38692
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:20.500572+00:00
-- url     : https://prove2.me/submissions/38ab3722-5844-4497-bd1f-c48169667594

import Mathlib.Analysis.Complex.Basic

theorem solution (x₁ x₂ : ℝ) :
  Real.sqrt (x₁^2 + (1 - x₂)^2) ≥ (Real.sqrt 2 / 2) * (x₁ + 1 - x₂) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  rw [mul_pow, div_pow, h2]
  nlinarith [sq_nonneg (x₁ - (1 - x₂))]
