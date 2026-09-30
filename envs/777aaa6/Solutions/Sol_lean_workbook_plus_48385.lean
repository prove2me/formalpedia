-- Prove2me | solution 1 for lean_workbook_plus_48385
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:59.172336+00:00
-- url     : https://prove2.me/submissions/aed3b4c9-83ca-456a-8d43-ab5d8392e056

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (hab : a + b > 0) : a ^ 2 + b + 1 / (a + b) ≥ 7 / 4 := by
  have h1 : 1 / (a + b) ≥ 2 - (a + b) := by
    rw [ge_iff_le, le_div_iff₀ hab]
    nlinarith [sq_nonneg (a + b - 1)]
  nlinarith [sq_nonneg (a - 1 / 2)]
