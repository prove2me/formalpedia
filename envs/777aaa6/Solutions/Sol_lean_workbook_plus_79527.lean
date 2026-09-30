-- Prove2me | solution 1 for lean_workbook_plus_79527
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:09.470936+00:00
-- url     : https://prove2.me/submissions/2995bc74-261c-4304-93ac-05e0ada39d42

import Mathlib

theorem solution (x : ℝ) (hx : x > 0) :
    2 + x + x^3 ≥ 8 * x^3 / (x^4 + 1) := by
  have hden : 0 < x^4 + 1 := by positivity
  apply (div_le_iff₀ hden).2
  have hrem : 0 ≤ (x - 1)^2 *
      (x^5 + 2*x^4 + 4*x^3 + 8*x^2 + 5*x + 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith only [hrem]
