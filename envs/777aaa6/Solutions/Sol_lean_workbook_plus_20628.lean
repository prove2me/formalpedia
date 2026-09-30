-- Prove2me | solution 1 for lean_workbook_plus_20628
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:28:34.197023+00:00
-- url     : https://prove2.me/submissions/7a8df80c-cf6d-469d-b7eb-9a9ba608b128

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : Real.sqrt (36 * x ^ 4 - 40 * x ^ 2 + 4) = 2 * Real.sqrt ((1 - x) * (1 + x) * (1 - 3 * x) * (1 + 3 * x)) := by
  have h : 36 * x ^ 4 - 40 * x ^ 2 + 4 = (2 : ℝ) ^ 2 * ((1 - x) * (1 + x) * (1 - 3 * x) * (1 + 3 * x)) := by ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
