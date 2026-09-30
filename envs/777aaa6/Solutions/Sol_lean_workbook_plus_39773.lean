-- Prove2me | solution 1 for lean_workbook_plus_39773
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:41.058793+00:00
-- url     : https://prove2.me/submissions/6be64919-091c-4820-a749-74c00cea8d13

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (hx: x >= 0 ∧ y >= 0) (h : x + y^2 >= x^2 + y^3): 3 * x^2 + 2 * y^3 <= 5 := by
  obtain ⟨hx0, hy0⟩ := hx
  nlinarith [h, sq_nonneg (x - 1), mul_nonneg (sq_nonneg (y - 1)) (by linarith : (0:ℝ) ≤ 2 * y + 1)]
