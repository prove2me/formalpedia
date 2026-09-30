-- Prove2me | solution 1 for lean_workbook_plus_34121
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:41:08.141061+00:00
-- url     : https://prove2.me/submissions/3d8c6f16-7c0d-4774-a98e-9a348519a529

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h₁ : x^3 + y^2 - 2 = 0) (h₂ : x^2 + y^2 + x*y - y = 0) : x = 1 ∧ y = 1 := by
  exfalso
  have hy : y * (x - 1) = x ^ 3 - x ^ 2 - 2 := by linear_combination h₂ - h₁
  have hy2 : y ^ 2 = 2 - x ^ 3 := by linarith
  have hsq : (x ^ 3 - x ^ 2 - 2) ^ 2 = (2 - x ^ 3) * (x - 1) ^ 2 := by
    calc (x ^ 3 - x ^ 2 - 2) ^ 2 = (y * (x - 1)) ^ 2 := by rw [hy]
      _ = y ^ 2 * (x - 1) ^ 2 := by ring
      _ = (2 - x ^ 3) * (x - 1) ^ 2 := by rw [hy2]
  -- q(x) = x^6 - x^5 - x^4 - 3x^3 + 2x^2 + 4x + 2 > 0
  nlinarith [sq_nonneg (x^3 - x^2/2 - x), sq_nonneg (x^2 - x), sq_nonneg (x + 1), sq_nonneg (x^3), sq_nonneg (x^2 + x), sq_nonneg (x^3 - x^2/2 - 3*x/4 - 1)]
