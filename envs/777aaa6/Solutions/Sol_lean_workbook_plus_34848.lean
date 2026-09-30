-- Prove2me | solution 1 for lean_workbook_plus_34848
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:56.343272+00:00
-- url     : https://prove2.me/submissions/0a81a8ba-e1d6-40b0-bfe9-31e93ee18067

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / 2) * y ^ 6 + (1 / 2) * x ^ 4 * y ^ 4 ≥ x ^ 2 * y ^ 5 := by
  have h4 : 0 ≤ y ^ 4 := by positivity
  have := mul_nonneg h4 (sq_nonneg (y - x ^ 2))
  nlinarith [this]
