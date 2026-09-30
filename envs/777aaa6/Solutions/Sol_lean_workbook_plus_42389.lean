-- Prove2me | solution 1 for lean_workbook_plus_42389
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:48.048227+00:00
-- url     : https://prove2.me/submissions/acd96faa-98fa-49b4-9db3-432d93c40954

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) : (a - 1) * (3 * a - 7) ≥ 4 * |a - 5 / 3| - 8 / 3   := by
  by_cases h : 0 ≤ a - 5 / 3
  · rw [abs_of_nonneg h]
    nlinarith only [sq_nonneg (a - 7 / 3)]
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith only [sq_nonneg (a - 1)]

#print axioms solution
