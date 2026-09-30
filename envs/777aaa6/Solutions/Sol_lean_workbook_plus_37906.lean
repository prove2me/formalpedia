-- Prove2me | solution 1 for lean_workbook_plus_37906
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:02.532945+00:00
-- url     : https://prove2.me/submissions/aa8769ea-4529-4bd4-b17a-316b904eeb44

import Mathlib
set_option autoImplicit false

theorem solution (u v : ℝ) : 4 * u ^ 2 * (27 * u ^ 4 - 42 * u ^ 2 * v ^ 2 + 27 * v ^ 4) * (u ^ 2 - v ^ 2) ^ 2 ≥ 0   := by
  have hq : 0 ≤ 27 * u ^ 4 - 42 * u ^ 2 * v ^ 2 + 27 * v ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2 - v ^ 2), mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg u)) hq)
    (sq_nonneg (u ^ 2 - v ^ 2))

#print axioms solution
