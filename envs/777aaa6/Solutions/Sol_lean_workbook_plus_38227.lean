-- Prove2me | solution 1 for lean_workbook_plus_38227
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:14.392126+00:00
-- url     : https://prove2.me/submissions/3f7f0452-9113-4c8e-8994-c8783eba16fc

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) : a^4 + b^4 ≥ 2 * a^2 * b^2 := by
  nlinarith [sq_nonneg (a^2 - b^2)]
