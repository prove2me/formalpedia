-- Prove2me | solution 1 for lean_workbook_plus_65524
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:13:22.524578+00:00
-- url     : https://prove2.me/submissions/a27b183a-9502-4210-8e6b-57716227c020

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h₁ : x ^ 2 / 2 ≤ y) (h₂ : y ≤ -2 * x ^ 2 + 3 * x) : x ^ 2 + y ^ 2 ≤ 2 := by
  have hy0 : 0 ≤ y := by nlinarith [sq_nonneg x]
  have hx0 : 0 ≤ x := by nlinarith [sq_nonneg x]
  have hx1 : x ≤ 6 / 5 := by nlinarith [sq_nonneg x]
  have hy2 : y ^ 2 ≤ (-2 * x ^ 2 + 3 * x) ^ 2 := by
    have := mul_le_mul h₂ h₂ hy0 (by linarith)
    nlinarith
  have hq : 0 ≤ 1 + 2 * x - 2 * x ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg (x - 1)) hq]
