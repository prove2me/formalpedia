-- Prove2me | solution 1 for lean_workbook_plus_7118
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:25.513854+00:00
-- url     : https://prove2.me/submissions/22f2152f-10e4-41c4-b51d-fe496cee71d5

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : 2 * x * Real.sqrt x - 3 * x + 1 ≥ 0   := by
  have hs : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have ht : 0 ≤ 2 * Real.sqrt x + 1 := by positivity
  have hp := mul_nonneg (sq_nonneg (Real.sqrt x - 1)) ht
  have hm := congrArg (fun y : ℝ => y * Real.sqrt x) hs
  nlinarith only [hs, hp, hm]

#print axioms solution
