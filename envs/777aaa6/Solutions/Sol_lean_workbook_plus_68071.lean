-- Prove2me | solution 1 for lean_workbook_plus_68071
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:21.823759+00:00
-- url     : https://prove2.me/submissions/d6accd75-897f-4ef5-93bf-ba47dbda62a7

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 + 3 ≥ 2 * (a + b + c)   := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

#print axioms solution
