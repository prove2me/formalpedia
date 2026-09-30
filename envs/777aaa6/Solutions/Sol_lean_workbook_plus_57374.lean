-- Prove2me | solution 1 for lean_workbook_plus_57374
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:56.709469+00:00
-- url     : https://prove2.me/submissions/4ae8affb-0e7e-4724-ba89-1587c03771a1

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : (x = 1 ∨ x = -5 → 2*x^3 + 9*x^2 - 6*x - 5 = 0) := by
  rintro (rfl | rfl) <;> norm_num
